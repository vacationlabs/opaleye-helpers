{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings  #-}

module Opaleye.TH (
      makeOpaleyeModels
    , makeOpaleyeTables
    , makeAdaptorAndInstances
    , Options(..)
    , TableOptions(..)
    )
where 

import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.FromField
import Language.Haskell.TH
import Language.Haskell.TH.Syntax hiding (lift)
import Control.Monad.IO.Class
import Control.Monad
import Data.Char
import Data.Maybe
import Data.List
import Data.Profunctor.Product.TH (makeAdaptorAndInstance)
import Data.Profunctor.Product.Default
import Opaleye
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Typeable
import Data.Aeson

import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader

data Options = Options { tableOptions :: [(String, TableOptions)] }

data TableOptions = TableOptions { modelName :: String, overrideDefaultTypes :: [(String, String)], skipInstancesFor :: [String] }

type ColumnType = String

data ColumnInfo = ColumnInfo { columnTableName :: String, columnName ::String, columnType :: ColumnType, columnDefault :: Bool, columnNullable :: Bool} deriving (Show)

testFunc2 :: ReaderT () Q (Maybe Name)
testFunc2 = lift $ lookupTypeName "wewq" 

type Env = (ConnectInfo, Options)
type EnvM a = ReaderT Env Q a

getColumns :: Connection -> String -> IO [ColumnInfo]
getColumns conn tname = do
  field_rows <- query conn
    "select column_name, udt_name, column_default, is_nullable from information_schema.columns where table_name = ?" 
    (Only tname) :: IO [(String, String, Maybe String, String)]
  return $ makeColumnInfo <$> field_rows
  where
    makeColumnInfo :: (String, String, Maybe String, String) -> ColumnInfo
    makeColumnInfo (name, ctype, hasDefault, isNullable) = ColumnInfo tname name ctype (isJust hasDefault) (isNullable == "YES")

lookupNewtypeForField :: ColumnInfo -> EnvM (Maybe Name)
lookupNewtypeForField ci = do
  (_, options) <- ask
  return $ mkName <$> lookup (columnName ci) (overrideDefaultTypes $ getTableOptions (columnTableName ci) options)

makePgType :: ColumnInfo -> EnvM Type
makePgType ci@(ColumnInfo  _ dbColumnName ct hasDefault isNullable) = do
  c <- lift $ lookupTypeName "Column"
  case c of
    Nothing -> error "Couldn't find opaleye's 'Column' type in scope. Have you imported Opaleye module?"
    Just columnName -> do
      Just n <- lift $ lookupTypeName "Nullable"
      x <- lookupNewtypeForField ci
      case x of
        Just pgType -> do
          return $ makeFinalType columnName n (ConT pgType)
        Nothing -> do
          pgType <- getPGColumnType ct
          return $ makeFinalType columnName n pgType
  where
    makeFinalType :: Name -> Name -> Type -> Type
    makeFinalType columnName nullableName pgType = let 
                       nn = AppT (ConT columnName) pgType
                       in if isNullable then (AppT (ConT columnName) (AppT (ConT nullableName) pgType))  else nn 

getPGColumnType :: ColumnType -> EnvM Type
getPGColumnType ct = lift $ (getType ct) 
  where
    getType :: ColumnType -> Q Type
    getType ct = do
      pg_array <- ConT <$> fromJust <$> lookupTypeName "PGArray"
      case ct of 
        "bool"        -> ConT <$> fromJust <$> lookupTypeName "PGBool"
        "int2"        -> ConT <$> fromJust <$> lookupTypeName "PGInt2"
        "int4"        -> ConT <$> fromJust <$> lookupTypeName "PGInt4"
        "int8"        -> ConT <$> fromJust <$> lookupTypeName "PGInt8"
        "float4"      -> ConT <$> fromJust <$> lookupTypeName "PGFloat4"
        "float8"      -> ConT <$> fromJust <$> lookupTypeName "PGFloat8"
        "numeric"     -> ConT <$> fromJust <$> lookupTypeName "PGNumeric"
        "char"        -> ConT <$> fromJust <$> lookupTypeName "PGText"
        "text"        -> ConT <$> fromJust <$> lookupTypeName "PGText"
        "bytea"       -> ConT <$> fromJust <$> lookupTypeName "PGBytea"
        "date"        -> ConT <$> fromJust <$> lookupTypeName "PGDate"
        "timestamp"   -> ConT <$> fromJust <$> lookupTypeName "PGTimestamp"
        "timestamptz" -> ConT <$> fromJust <$> lookupTypeName "PGTimestamptz"
        "time"        -> ConT <$> fromJust <$> lookupTypeName "PGTime"
        "timetz"      -> ConT <$> fromJust <$> lookupTypeName "PGTime"
        "interval"    -> ConT <$> fromJust <$> lookupTypeName "PGInt8"
        "uuid"        -> ConT <$> fromJust <$> lookupTypeName "PGUuid"
        "json"        -> ConT <$> fromJust <$> lookupTypeName "PGJson"
        "jsonb"       -> ConT <$> fromJust <$> lookupTypeName "PGJsonb"
        "varchar"     -> ConT <$> fromJust <$> lookupTypeName "PGText"
        "oid"         -> ConT <$> fromJust <$> lookupTypeName "PGInt8"
        "inet"        -> ConT <$> fromJust <$> lookupTypeName "PGText"
        "_varchar"    -> (AppT pg_array) <$> getType "text"
        "_text"       -> (AppT pg_array) <$> getType "text"
        "_int4"       -> (AppT pg_array) <$> getType "int4"
        "_int8"       -> (AppT pg_array) <$> getType "int8"
        other         -> error $ "Unimplemented PostgresQL type conversion for " ++ show other

getPGConFuncExp :: Type -> EnvM Exp
getPGConFuncExp (ConT name) = do
  let tname = case (nameBase name) of 
        "PGText" -> "pgStrictText"
        "PGInt4" -> "pgInt4"
        "PGInt8" -> "pgInt8"
        "PGBool" -> "pgBool"
        "PGTimestamp" -> "pgLocalTime"
        "PGTimestampz" -> "pgUTCTime"
        "pGTime" -> "pgTimeOfDay"
        "PGJson" -> "pgValueJSON"
        "PGJsonb" -> "pgValueJSONB"
  g <- lift $ lookupValueName tname
  case g of
    Just a -> return $ VarE a
    Nothing -> error $ "Cannot find " ++ tname
getPGConFuncExp (AppT pga pgt) = do
  g <- lift $ lookupValueName "pgArray"
  let pga_func = case g of
        Just a -> VarE a
        Nothing -> error $ "Cannot find pgArray"
  func1 <- getPGConFuncExp pgt
  return $ AppE pga_func func1

makeReadTypes :: [ColumnInfo] -> EnvM [Type]
makeReadTypes fieldInfos = mapM makePgType fieldInfos

makeHaskellTypes :: [ColumnInfo] -> EnvM [Type]
makeHaskellTypes fieldInfos = mapM makeHaskellType fieldInfos

getHaskellTypeFor :: ColumnType -> EnvM Type
getHaskellTypeFor ct = case ct of
  "bool"        -> lift $ (ConT).fromJust <$> lookupTypeName "Bool"
  "int2"        -> lift $ (ConT).fromJust <$> lookupTypeName "Int16"
  "int4"        -> lift $ (ConT).fromJust <$> lookupTypeName "Int"
  "int8"        -> lift $ (ConT).fromJust <$> lookupTypeName "Int64"
  "float4"      -> lift $ (ConT).fromJust <$> lookupTypeName "Float"
  "float8"      -> lift $ (ConT).fromJust <$> lookupTypeName "Double"
  "numeric"     -> lift $ (ConT).fromJust <$> lookupTypeName "Scientific"
  "char"        -> lift $ (ConT).fromJust <$> lookupTypeName "Char"
  "text"        -> lift $ (ConT).fromJust <$> lookupTypeName "Text"
  "bytea"       -> lift $ (ConT).fromJust <$> lookupTypeName "ByteString"
  "date"        -> lift $ (ConT).fromJust <$> lookupTypeName "Day"
  "timestamp"   -> lift $ (ConT).fromJust <$> lookupTypeName "LocalTime"
  "timestamptz" -> lift $ (ConT).fromJust <$> lookupTypeName "UTCTime"
  "time"        -> lift $ (ConT).fromJust <$> lookupTypeName "TimeOfDay"
  "timetz"      -> lift $ (ConT).fromJust <$> lookupTypeName "TimeOfDay"
  "interval"    -> lift $ (ConT).fromJust <$> lookupTypeName "DiffTime"
  "uuid"        -> lift $ (ConT).fromJust <$> lookupTypeName "UUID"
  "json"        -> lift $ (ConT).fromJust <$> lookupTypeName "Value"
  "jsonb"       -> lift $ (ConT).fromJust <$> lookupTypeName "Value"
  "varchar"     -> lift $ (ConT).fromJust <$> lookupTypeName "Text"
  "_varchar"    -> (AppT array) <$> getHaskellTypeFor "varchar"
  "_text"       -> (AppT array) <$> getHaskellTypeFor "varchar"
  "_int4"       -> (AppT array) <$> getHaskellTypeFor "int4"
  other         -> error $ "Unimplemented PostgresQL type conversion for " ++ show other
  where
    array :: Type
    array = ConT (''Vector)

makeRawHaskellType :: ColumnInfo -> EnvM Type
makeRawHaskellType ci = do
    makeNullable <$> getHaskellTypeFor (columnType ci)
  where
    makeNullable :: Type -> Type
    makeNullable typ = typ

makeHaskellType :: ColumnInfo -> EnvM Type
makeHaskellType ci = do
  nt <- lookupNewtypeForField ci
  case nt of
    Nothing -> makeRawHaskellType ci
    Just t -> return $ ConT t

makeWriteTypes :: [ColumnInfo] -> EnvM [Type]
makeWriteTypes fieldInfos = do
  Just maybeName <- lift $ lookupTypeName "Maybe"
  mapM (makePgType' maybeName) fieldInfos
  where
    makePgType' :: Name -> ColumnInfo -> EnvM Type
    makePgType' maybeName ci = do
      defaultType <- makePgType ci
      return $ if (columnDefault ci)
          then (AppT (ConT maybeName) defaultType)
          else defaultType

makeOpaleyeTables :: Env -> Q [Dec]
makeOpaleyeTables env = runReaderT (do
  (_, options) <- ask
  let names = fst <$> tableOptions options
  let models = (modelName.snd) <$> tableOptions options
  concat <$> zipWithM makeOpaleyeTable names models) env

makeOpaleyeTable :: String -> String -> EnvM [Dec]
makeOpaleyeTable t r = do
  (connectInfo, _) <- ask
  lift $ do
    fieldInfos <- runIO $ do
      conn <- connect connectInfo
      getColumns conn t
    Just adapterFunc <- lookupValueName $ makeAdapterName r
    Just constructor <- lookupValueName r
    Just tableTypeName <- lookupTypeName "Table"
    Just tableFunctionName <- lookupValueName "Table"
    Just pgWriteTypeName <- lookupTypeName $ makePGWriteTypeName r
    Just pgReadTypeName <- lookupTypeName $ makePGReadTypeName r
    let funcName = mkName $ t ++ "Table"
    let funcType = AppT (AppT (ConT tableTypeName) (ConT pgWriteTypeName)) (ConT pgReadTypeName)
    let signature = SigD funcName funcType
    fieldExps <- (getTableTypes fieldInfos)
    let
      funcExp = AppE (AppE (ConE tableFunctionName) (LitE $ StringL t)) funcExp2
      funcExp2 = AppE (VarE adapterFunc) funcExp3
      funcExp3 = foldl AppE (ConE constructor) fieldExps
      in return [signature, FunD funcName [Clause [] (NormalB funcExp) []]]
  where
    getTableTypes :: [ColumnInfo] -> Q [Exp]
    getTableTypes fieldInfos = do
      Just requiredName <- lookupValueName "required"
      Just optionalName <- lookupValueName "optional"
      return $ (mkExp requiredName optionalName) <$> fieldInfos
      where
        mkExp :: Name -> Name -> ColumnInfo -> Exp
        mkExp rq op ci = let 
                           ty = if (columnDefault ci) then op else rq 
                         in AppE (VarE ty) (LitE $ StringL $ columnName ci)

makePGReadTypeName :: String -> String
makePGReadTypeName tn = tn ++ "PGRead"

makePGWriteTypeName :: String -> String
makePGWriteTypeName tn = tn ++ "PGWrite"

makeAdapterName :: String -> String
makeAdapterName tn = 'p':tn

makeOpaleyeModels :: Env -> Q [Dec]
makeOpaleyeModels env = runReaderT (do
  newTypeDecs <- makeNewTypes
  (_, options) <- ask
  let names = fst <$> tableOptions options
  let models = (modelName.snd) <$> tableOptions options
  instances <- makeNewtypeInstances
  decs <- concat <$> zipWithM makeOpaleyeModel names models
  return $ newTypeDecs ++ decs ++ instances) env

collectNewTypes :: EnvM [(ColumnInfo, String)]
collectNewTypes = do
  (connInfo, options) <- ask
  concat <$> mapM getNewTypes (tableOptions options)
  where
    getNewTypes :: (String, TableOptions) -> EnvM [(ColumnInfo, String)]
    getNewTypes (tbName, tbOptions) = do
      (connectInfo, _) <- ask
      fieldInfos <- (lift.runIO) $ do
        conn <- connect connectInfo
        getColumns conn tbName
      return $ fromJust <$> (filter isJust $ (tryNewType tbOptions) <$> fieldInfos)
    tryNewType :: TableOptions -> ColumnInfo -> Maybe (ColumnInfo, String)
    tryNewType to ci = (\n -> (ci, n)) <$> lookup (columnName ci) (overrideDefaultTypes to)

makeNewTypes :: EnvM [Dec]
makeNewTypes = do
  nts <- collectNewTypes
  (a, b) <- foldM makeNewType ([], []) nts
  return b
  where
  makeNewType :: ([String], [Dec]) -> (ColumnInfo, String) -> EnvM ([String], [Dec])
  makeNewType (added, decs) (ci, nt_name) = do
    if nt_name `elem` added then (return (added, decs)) else do
      dec <- makeNewType' nt_name
      return (nt_name:added, dec:decs)
    where
      makeNewType' :: String -> EnvM Dec
      makeNewType' name = do
        let bang = Bang NoSourceUnpackedness NoSourceStrictness
        haskellType <- makeRawHaskellType ci
        return $ NewtypeD [] (mkName name) [] Nothing (NormalC (mkName name) [(bang, haskellType)]) [ConT ''Show]
    
makeOpaleyeModel :: String -> String -> EnvM [Dec]
makeOpaleyeModel t r = do
  (connectInfo, _) <- ask
  let recordName = mkName r
  let recordPolyName = mkName $ r ++ "Poly"
  fieldInfos <- (lift.runIO) $ do
    conn <- connect connectInfo
    getColumns conn t
  deriveShow <- lift $ [t| Show |]
  fields <- mapM (lift.newName.columnName) fieldInfos
  let rec = DataD [] recordPolyName (tVarBindings fields) Nothing [RecC recordName $ getConstructorArgs $ zip (mkName.(addPrefix r).columnName <$> fieldInfos) fields] [deriveShow]
  haskell <- makeHaskellAlias (mkName r) recordPolyName fieldInfos
  pgRead <- makePgReadAlias (mkName $ makePGReadTypeName r) recordPolyName fieldInfos
  pgWrite <- makePgWriteAlias (mkName $ makePGWriteTypeName r) recordPolyName fieldInfos
  return $ [rec, haskell, pgRead, pgWrite]
  where
    addPrefix :: String -> String -> String
    addPrefix pre (s:ss) = "_" ++ (toLower <$> pre) ++ (toUpper s:ss)
    makeHaskellAlias :: Name -> Name -> [ColumnInfo] -> EnvM Dec
    makeHaskellAlias hname poly_name fieldInfos = do
      types <- makeHaskellTypes fieldInfos
      return $ TySynD hname [] (full_type types)
      where
        full_type :: [Type] -> Type
        full_type typs = foldl AppT (ConT poly_name) typs
    makePgReadAlias :: Name -> Name -> [ColumnInfo] -> EnvM Dec
    makePgReadAlias name modelType fieldInfos = do
      readType <- makePgReadType modelType fieldInfos
      return $ TySynD name [] readType
    makePgReadType :: Name -> [ColumnInfo] -> EnvM Type
    makePgReadType modelType fieldInfos = do
      readTypes <- makeReadTypes fieldInfos
      return $ foldl AppT (ConT modelType) readTypes
    makePgWriteType :: Name -> [ColumnInfo] -> EnvM Type
    makePgWriteType modelType fieldInfos = do
      readTypes <- makeWriteTypes fieldInfos
      return $ foldl AppT (ConT modelType) readTypes
    makePgWriteAlias :: Name -> Name ->[ColumnInfo] -> EnvM Dec
    makePgWriteAlias name modelType fieldInfos = do
      writeType <- makePgWriteType modelType fieldInfos
      return $ TySynD name [] writeType
    tVarBindings :: [Name] -> [TyVarBndr]
    tVarBindings fields = PlainTV <$> fields
    getConstructorArgs :: [(Name, Name)] -> [VarBangType]
    getConstructorArgs fields = makeBangType <$> fields
      where
        makeBangType :: (Name, Name) -> VarBangType
        makeBangType (fieldName, name) = let bang = Bang NoSourceUnpackedness NoSourceStrictness in (fieldName, bang, VarT name)

makeNewtypeInstances :: EnvM [Dec]
makeNewtypeInstances = do
  newTypes <- groupDups <$> collectNewTypes
  concat  <$> (mapM makeInstancesForNewtypeColumn newTypes)
  where
    groupDups :: [(ColumnInfo, String)] -> [(ColumnInfo, Name)]
    groupDups pairs = fmap collect $ nub $ fmap snd pairs
      where
        collect :: String -> (ColumnInfo, Name)
        collect tn = (fromJust $ lookup tn $ swapped, mkName tn)
        swapped :: [(String, ColumnInfo)]
        swapped = fmap swap pairs
        swap :: (a, b) -> (b, a)
        swap (x, y) = (y, x)
    makeInstancesForNewtypeColumn :: (ColumnInfo, Name) -> EnvM [Dec]
    makeInstancesForNewtypeColumn (ci, ntName) = do
        fromFieldInstance <- makeFromFieldInstance ci ntName
        queryRunnerInstance <- makeQueryRunnerInstance ci ntName
        defaultInstance <- makeDefaultInstance ci ntName
        return $ fromFieldInstance ++ queryRunnerInstance ++ defaultInstance
      where
        makeFromFieldInstance :: ColumnInfo -> Name -> EnvM [Dec]
        makeFromFieldInstance ci ntName = do
          let ntNameQ = return $ ConT ntName
          let ntNameExpQ = return $ ConE ntName
          lift $ [d|
            instance FromField $(ntNameQ) where
              fromField field bs = fmap $(ntNameExpQ) (fromField field bs)
            |]
        makeQueryRunnerInstance :: ColumnInfo -> Name -> EnvM [Dec]
        makeQueryRunnerInstance ci ntName = do
          pgDefColType <- getPGColumnType (columnType ci)
          let ntNameQ = return $ ConT ntName
          lift $ [d|
            instance QueryRunnerColumnDefault $(return pgDefColType) $(ntNameQ) where
              queryRunnerColumnDefault = fieldQueryRunnerColumn
            instance QueryRunnerColumnDefault $(return $ ConT ntName) $(ntNameQ) where
              queryRunnerColumnDefault = fieldQueryRunnerColumn
            instance QueryRunnerColumnDefault (Nullable $(return $ ConT ntName)) $(ntNameQ) where
              queryRunnerColumnDefault = fieldQueryRunnerColumn
            |]
        makeDefaultInstance :: ColumnInfo -> Name -> EnvM [Dec]
        makeDefaultInstance ci ntName = do
          pgDefColType <- getPGColumnType(columnType ci)
          pgConFuncExp <- getPGConFuncExp pgDefColType
          let ntNameQ = return $ ConT ntName
          if (columnNullable ci)
            then
              (makeDefaultInstanceForNullable ci ntName)
            else 
              if (columnDefault ci) 
                then
                  lift [d|
                    instance Default Constant $(ntNameQ) (Column $(return pgDefColType)) where
                      def = Constant f
                        where
                        f ($(return $ ConP ntName $ [VarP $ mkName "x"])) = $(return pgConFuncExp) x
                    instance Default Constant $(ntNameQ) (Column $(ntNameQ)) where
                      def = f <$> def
                        where
                        f :: Column $(return pgDefColType) -> Column $(ntNameQ)
                        f  = unsafeCoerceColumn
                    |] 
                else
                  lift [d|
                    instance Default Constant $(ntNameQ) (Column $(return pgDefColType)) where
                      def = Constant f
                        where
                        f ($(return $ ConP ntName $ [VarP $ mkName "x"])) = $(return pgConFuncExp) x
                    instance Default Constant (Maybe $(ntNameQ)) (Column $(return pgDefColType)) where
                      def = Constant f
                        where
                        f (Just ($(return $ ConP ntName $ [VarP $ mkName "x"]))) = $(return pgConFuncExp) x
                    instance Default Constant $(ntNameQ) (Column $(ntNameQ)) where
                      def = f <$> def
                        where
                        f :: Column $(return pgDefColType) -> Column $(ntNameQ)
                        f  = unsafeCoerceColumn
                    |] 
        makeDefaultInstanceForNullable :: ColumnInfo -> Name -> EnvM [Dec]
        makeDefaultInstanceForNullable ci ntName = do
          argname <- lift $ newName "x"
          pgDefColType <- getPGColumnType(columnType ci)
          pgConFuncExp <- getPGConFuncExp pgDefColType
          let ntNameQ = return $ ConT ntName
          lift $ [d|
            instance Default Constant $(ntNameQ) (Column $(return pgDefColType)) where
              def = Constant f
                where
                f ($(return $ ConP ntName $ [VarP $ mkName "x"])) = $(return pgConFuncExp) x
            instance Default Constant $(ntNameQ) (Column $(ntNameQ)) where
              def = f <$> def
                where
                f :: Column $(return pgDefColType) -> Column $(ntNameQ)
                f  = unsafeCoerceColumn
            |]

getTableOptions :: String -> Options -> TableOptions
getTableOptions tname options = fromJust $ lookup tname (tableOptions options)

makeAdaptorAndInstances :: Env -> Q [Dec]
makeAdaptorAndInstances env = runReaderT (do
  (_, options) <- ask
  let models = (modelName.snd) <$> tableOptions options
  let an = makeAdapterName <$> models
  pn <- lift $ mapM (\x -> fromJust <$> lookupTypeName (x ++ "Poly")) models
  lift $ concat <$> zipWithM makeAdaptorAndInstance an pn) env
