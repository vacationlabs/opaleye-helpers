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
import GHC.Int

import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Monad.State.Lazy

import Control.Lens

data Options = Options { tableOptions :: [(String, TableOptions)] }

data TableOptions = TableOptions { modelName :: String, overrideDefaultTypes :: [(String, String)], protectedFields :: [String] }

type ColumnType = String

data ColumnInfo = ColumnInfo { columnTableName :: String, columnName ::String, columnType :: ColumnType, columnDefault :: Bool, columnNullable :: Bool, columnPrimary :: Bool} deriving (Show)

type LensClassGenerated = [String]
type Env = (ConnectInfo, Options, LensClassGenerated)
type EnvM a = StateT Env Q a

getColumns :: Connection -> String -> IO [ColumnInfo]
getColumns conn tname = do
  field_rows <- query conn "SELECT \
      \ c.column_name, c.udt_name, c.column_default, c.is_nullable, (array_agg(tc.constraint_type::text) @> ARRAY ['PRIMARY KEY']) as is_primary\
      \ FROM\
      \ information_schema.columns AS c \
      \ left join\
      \   information_schema.constraint_column_usage as ccu on\
      \     c.table_catalog = ccu.table_catalog and\
      \     c.table_schema = ccu.table_schema and\
      \     c.table_name  = ccu.table_name and\
      \     c.column_name = ccu.column_name\
      \ left join information_schema.table_constraints tc on\
      \   c.table_schema = tc. constraint_schema and\
      \   tc.table_name = c.table_name and\
      \   tc.constraint_name = ccu.constraint_name\
      \ where c.table_name = ? group by c.column_name,c.udt_name, c.column_default, c.is_nullable" (Only tname) :: IO [(String, String, Maybe String, String, Bool)]
  return $ makeColumnInfo <$> field_rows
  where
    makeColumnInfo :: (String, String, Maybe String, String, Bool) -> ColumnInfo
    makeColumnInfo (name, ctype, hasDefault, isNullable, isPrimary) = ColumnInfo tname name ctype (isJust hasDefault) (isNullable == "YES") isPrimary

lookupNewtypeForField :: ColumnInfo -> EnvM (Maybe Name)
lookupNewtypeForField ci = do
  (_, options, _) <- get
  return $ mkName <$> lookup (columnName ci) (overrideDefaultTypes $ getTableOptions (columnTableName ci) options)

makePgType :: ColumnInfo -> EnvM Type
makePgType ci@(ColumnInfo  _ dbColumnName ct hasDefault isNullable isPrimary) = do
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
        "hstore"      -> ConT <$> fromJust <$> lookupTypeName "PGJsonb"
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

fromJust' :: Maybe a -> a
fromJust' Nothing = error $ ""
fromJust' (Just a) = a

safeLookupTypeName :: String -> Q Name
safeLookupTypeName name = do
  n <- lookupTypeName name
  case n of
    Nothing -> error $ "Cannot find name '" ++ name ++ "'"
    Just x -> return x

getHaskellTypeFor :: ColumnType -> EnvM Type
getHaskellTypeFor ct = case ct of
  "bool"        -> lift $ (ConT) <$> safeLookupTypeName "Bool"
  "int2"        -> lift $ (ConT) <$> safeLookupTypeName "Int16"
  "int4"        -> lift $ (ConT) <$> safeLookupTypeName "Int"
  "int8"        -> lift $ (ConT) <$> safeLookupTypeName "Int64"
  "float4"      -> lift $ (ConT) <$> safeLookupTypeName "Float"
  "float8"      -> lift $ (ConT) <$> safeLookupTypeName "Double"
  "numeric"     -> lift $ (ConT) <$> safeLookupTypeName "Scientific"
  "char"        -> lift $ (ConT) <$> safeLookupTypeName "Char"
  "text"        -> lift $ (ConT) <$> safeLookupTypeName "Text"
  "bytea"       -> lift $ (ConT) <$> safeLookupTypeName "ByteString"
  "date"        -> lift $ (ConT) <$> safeLookupTypeName "Day"
  "timestamp"   -> lift $ (ConT) <$> safeLookupTypeName "LocalTime"
  "timestamptz" -> lift $ (ConT) <$> safeLookupTypeName "UTCTime"
  "time"        -> lift $ (ConT) <$> safeLookupTypeName "TimeOfDay"
  "timetz"      -> lift $ (ConT) <$> safeLookupTypeName "TimeOfDay"
  "interval"    -> lift $ (ConT) <$> safeLookupTypeName "DiffTime"
  "uuid"        -> lift $ (ConT) <$> safeLookupTypeName "UUID"
  "json"        -> lift $ (ConT) <$> safeLookupTypeName "Value"
  "jsonb"       -> lift $ (ConT) <$> safeLookupTypeName "Value"
  "hstore"      -> lift $ (ConT) <$> safeLookupTypeName "Value"
  "varchar"     -> lift $ (ConT) <$> safeLookupTypeName "Text"
  "_varchar"    -> (AppT array) <$> getHaskellTypeFor "varchar"
  "_text"       -> (AppT array) <$> getHaskellTypeFor "varchar"
  "_int4"       -> (AppT array) <$> getHaskellTypeFor "int4"
  other         -> error $ "Unimplemented PostgresQL type conversion for " ++ show other
  where
    array :: Type
    array = ConT (''Vector)

makeRawHaskellType :: ColumnInfo -> EnvM Type
makeRawHaskellType ci = do
    getHaskellTypeFor (columnType ci)

makeHaskellType :: ColumnInfo -> EnvM Type
makeHaskellType ci = do
  nt <- lookupNewtypeForField ci
  typ <- case nt of
    Nothing -> makeRawHaskellType ci
    Just t -> return $ ConT t
  return $ if (columnNullable ci) then (AppT (ConT ''Maybe) typ) else typ

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
makeOpaleyeTables env = do
  (decs, (_, _, clg)) <- runStateT (do
    (_, options, _) <- get
    let names = fst <$> tableOptions options
    let models = (modelName.snd) <$> tableOptions options
    typeClassDecs <- makeModelTypeClass
    tables <- concat <$> zipWithM makeOpaleyeTable names models
    lenses <- concat <$> zipWithM makeLensesForTable names models
    return $ typeClassDecs ++ tables ++ lenses) env
  return decs
  where
    makeModelTypeClass :: EnvM [Dec]
    makeModelTypeClass = lift $ do
      Just monadIO <- lookupTypeName "MonadIO"
      let modelTVar = VarT $ mkName "model"
      let mTVar = VarT $ mkName "m"
      insertType <- [t| (MonadIO $(return mTVar)) => Connection -> $(return modelTVar) -> $(return mTVar) $(return modelTVar) |]
      updateType <- [t| (MonadIO $(return mTVar)) => Connection -> $(return modelTVar) -> $(return mTVar) $(return modelTVar) |]
      deleteType <- [t| (MonadIO $(return mTVar)) => Connection -> $(return modelTVar) -> $(return mTVar) Int64 |]
      let
        insertSig = SigD (mkName "insertModel") insertType
        updateSig = SigD (mkName "updateModel") updateType
        deleteSig = SigD (mkName "deleteModel") deleteType
      return $ [ClassD [] (mkName "DbModel") [PlainTV $ mkName "model"] [] [insertSig, updateSig, deleteSig]]

makeLensesForTable :: String -> String -> EnvM [Dec]
makeLensesForTable t r = do
  (connectInfo, options, clg) <- get
  case lookup t (tableOptions options) of
    Just tOptions -> do
      let
        xs = protectedFields tOptions
        pFieldNames = (makeFieldName r) <$> xs 
      d1 <- makeLenses' r pFieldNames True
      d2 <- makeLenses' r pFieldNames False
      let decs = d1 ++ d2
      updateState decs
      return $ decs
    Nothing -> return []
  where
    -- Store the type class definitions contained
    -- in a list of declarations, in the state
    updateState :: [Dec] -> EnvM ()
    updateState decs = do
      (a, b, clg) <- get
      put (a, b, clg ++ (extractDecClasses decs))
      where
      extractDecClasses :: [Dec] -> [String]
      extractDecClasses decs = fromJust <$> filter isJust (extractClassName <$> decs)
        where
        extractClassName :: Dec -> Maybe String
        extractClassName (ClassD _ name _ _ _) = Just $ nameBase name
        extractClassName _ = Nothing
    makeLenses' :: String -> [String] -> Bool -> EnvM [Dec]
    makeLenses' modelname protected makeProtected = do
      (_, _, clg) <- get
      decs <- lift $ do 
        let modelTypeName = mkName $ modelname ++ "Poly"
        case makeProtected of
          True -> makeProtectedLenses modelTypeName clg 
          False -> makeNormalLenses modelTypeName clg
      return decs
      where
        makeProtectedLenses :: Name -> LensClassGenerated -> Q [Dec]
        makeProtectedLenses modelTypeName clg = do
          let
            -- The following code extracts list of generated
            -- classes from the state and only generate classes
            -- if they are not on that list.
            lr0 = abbreviatedFields & generateUpdateableOptics .~ False
            lr1 = lr0 & lensField .~ (protectedFieldNamer clg True)
            lr2 = lr0 & lensField .~ (protectedFieldNamer clg False)
            lr3 = (lr2 & createClass .~ False )
            in do
              decs1 <- makeLensesWith lr1 modelTypeName
              decs2 <- makeLensesWith lr3 modelTypeName
              return $ decs1 ++ decs2
        makeNormalLenses :: Name -> LensClassGenerated -> Q [Dec]
        makeNormalLenses modelTypeName clg = do
          runIO $ putStrLn $ show clg
          let
            lr1 = abbreviatedFields & lensField .~ (normalFieldNamer clg True)
            lr2 = abbreviatedFields & lensField .~ (normalFieldNamer clg False)
            lr3 = (lr2 & createClass .~ False )
            in do
              decs1 <- makeLensesWith lr1 modelTypeName
              decs2 <- makeLensesWith lr3 modelTypeName
              return $ decs1 ++ decs2
        protectedFieldNamer :: [String] -> Bool -> Name -> [Name] -> Name -> [DefName]
        protectedFieldNamer clgn eec x y fname = let
          sFname = "Has" ++ (ucFirst $ drop ((length r) + 1) $ nameBase fname)
          prted = elem sFname protected
          in if eec
             then (if (prted && (Prelude.not $ elem sFname clgn)) then (abbreviatedNamer x y fname) else [])
             else (if (prted && (elem sFname clgn)) then (abbreviatedNamer x y fname) else [])
        normalFieldNamer :: [String] -> Bool -> Name -> [Name] -> Name -> [DefName]
        normalFieldNamer clgn eec x y fname = let
          sFname = "Has" ++ (ucFirst $ drop ((length r) + 1) $ nameBase fname)
          prted = (Prelude.not $ elem (nameBase fname) protected)
          in if eec
             then (if (prted && (Prelude.not $ elem sFname clgn)) then (abbreviatedNamer x y fname) else [])
             else (if (prted && (elem sFname clgn)) then (abbreviatedNamer x y fname) else [])
        makeLenseName :: String -> String
        makeLenseName (x:xs) = lcFirst $ drop (length r) xs
        lcFirst :: String -> String
        lcFirst (x:xs) = (toLower x):xs
        ucFirst :: String -> String
        ucFirst (x:xs) = (toUpper x):xs

makeOpaleyeTable :: String -> String -> EnvM [Dec]
makeOpaleyeTable t r = do
  (connectInfo, _, _) <- get
  fieldInfos <- lift $ runIO $ do
    conn <- connect connectInfo
    getColumns conn t
  functions <- makeModelInstance fieldInfos
  lift $ do
    Just adapterFunc <- lookupValueName $ makeAdapterName r
    Just constructor <- lookupValueName r
    Just tableTypeName <- lookupTypeName "Table"
    Just tableFunctionName <- lookupValueName "Table"
    Just pgWriteTypeName <- lookupTypeName $ makePGWriteTypeName r
    Just pgReadTypeName <- lookupTypeName $ makePGReadTypeName r
    let funcName = mkName $ makeTablename t 
    let funcType = AppT (AppT (ConT tableTypeName) (ConT pgWriteTypeName)) (ConT pgReadTypeName)
    let signature = SigD funcName funcType
    fieldExps <- (getTableTypes fieldInfos)
    let
      funcExp = AppE (AppE (ConE tableFunctionName) (LitE $ StringL t)) funcExp2
      funcExp2 = AppE (VarE adapterFunc) funcExp3
      funcExp3 = foldl AppE (ConE constructor) fieldExps
      in return $ [signature, FunD funcName [Clause [] (NormalB funcExp) []]] ++ functions
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
    makeModelInstance :: [ColumnInfo] -> EnvM [Dec]
    makeModelInstance fieldInfos = do
      let (Just pField) = getPrimaryKeyField t r
      convertToPgWrite <- lift $ makeConversionFunction
      lift $ do 
        insertExp <- [e|liftIO $ Prelude.head <$> runInsertManyReturning conn $(return $ VarE $ mkName $ makeTablename t) [(toWrite $ constant model)] id |]
        updateExp <- [e|liftIO $ Prelude.head <$> runUpdateReturning conn $(return $ VarE $ mkName $ makeTablename t) (\_ -> toWrite $ constant model) (\r -> ($(return $ VarE $ mkName pField) r) .== (constant $  $(return $ VarE $ mkName pField) model)) id |]
        deleteExp <- [e|liftIO $ runDelete conn $(return $ VarE $ mkName $ makeTablename t) (\r -> ($(return $ VarE $ mkName pField) r) .== (constant $  $(return $ VarE $ mkName pField) model)) |]
        let pat = [VarP $ mkName "conn", VarP $ mkName "model"]
        let insertFunc = FunD (mkName "insertModel") [Clause pat (NormalB insertExp) convertToPgWrite]
        let updateFunc = FunD (mkName "updateModel") [Clause pat (NormalB updateExp) convertToPgWrite]
        let deleteFunc = FunD (mkName "deleteModel") [Clause pat (NormalB deleteExp) []]
        return [InstanceD Nothing [] (AppT (ConT $ mkName "DbModel") (ConT $ mkName r)) [insertFunc, updateFunc, deleteFunc]]
      where
        makeConversionFunction :: Q [Dec]
        makeConversionFunction = do
          let
            pgReadType = ConT $ (mkName $ makePGReadTypeName r)
            pgWriteType = ConT $ (mkName $ makePGWriteTypeName r)
            conversionFunctionSig = SigD (mkName "toWrite") $ AppT (AppT ArrowT pgReadType) pgWriteType
            conversionFunction = FunD (mkName "toWrite") [Clause [makePattern] (NormalB conExp) []]
          return $ [conversionFunctionSig, conversionFunction]
          where
            conExp :: Exp
            conExp = foldl AppE (ConE $ mkName $ r) $ getFieldExps
            getFieldExps :: [Exp]
            getFieldExps = zipWith getFieldExp fieldInfos [1..]
              where
              getFieldExp :: ColumnInfo -> Int -> Exp
              getFieldExp ci ix = if (columnDefault ci) then (AppE (ConE $ mkName "Just") mkVarExp) else mkVarExp
                where
                  mkVarExp :: Exp
                  mkVarExp = VarE $ mkName $ "a" ++ (show ix)
            makePattern :: Pat
            makePattern = ConP (mkName $ r) $ VarP <$> (mkName.(\x -> ('a':x)).show) <$>  take (Prelude.length fieldInfos) [1..]
        getPrimaryKeyField :: String -> String -> (Maybe String)
        getPrimaryKeyField tname modelName = case (filter (\ci -> columnPrimary ci)) fieldInfos of
            [primaryField] -> Just $ makeFieldName modelName (columnName primaryField)
            _ -> Nothing
  
makeTablename :: String -> String
makeTablename t = t ++ "Table"

makePGReadTypeName :: String -> String
makePGReadTypeName tn = tn ++ "PGRead"

makePGWriteTypeName :: String -> String
makePGWriteTypeName tn = tn ++ "PGWrite"

makeAdapterName :: String -> String
makeAdapterName tn = 'p':tn

makeOpaleyeModels :: Env -> Q [Dec]
makeOpaleyeModels env = fst <$> runStateT (do
  newTypeDecs <- makeNewTypes
  (_, options, _) <- get
  let names = fst <$> tableOptions options
  let models = (modelName.snd) <$> tableOptions options
  instances <- makeNewtypeInstances
  decs <- concat <$> zipWithM makeOpaleyeModel names models
  return $ newTypeDecs ++ decs ++ instances) env

collectNewTypes :: EnvM [(ColumnInfo, String)]
collectNewTypes = do
  (connInfo, options, _) <- get
  concat <$> mapM getNewTypes (tableOptions options)
  where
    getNewTypes :: (String, TableOptions) -> EnvM [(ColumnInfo, String)]
    getNewTypes (tbName, tbOptions) = do
      (connectInfo, _, _) <- get
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

makeFieldName :: String -> String -> String
makeFieldName modelName (s:ss) = "_" ++ (toLower <$> modelName) ++ (toUpper s:replaceUnderscore ss)

replaceUnderscore ('_':x:xs) = (toUpper x):(replaceUnderscore xs)
replaceUnderscore ('_':xs) = (replaceUnderscore xs)
replaceUnderscore (x:xs) = x:(replaceUnderscore xs)
replaceUnderscore [] = ""

ucFirst :: String -> String
ucFirst (s:ss) = (toUpper s):ss
    
makeOpaleyeModel :: String -> String -> EnvM [Dec]
makeOpaleyeModel t r = do
  (connectInfo, _, _) <- get
  let recordName = mkName r
  let recordPolyName = mkName $ r ++ "Poly"
  fieldInfos <- (lift.runIO) $ do
    conn <- connect connectInfo
    getColumns conn t
  deriveShow <- lift $ [t| Show |]
  fields <- mapM (lift.newName.columnName) fieldInfos
  let rec = DataD [] recordPolyName (tVarBindings fields) Nothing [RecC recordName $ getConstructorArgs $ zip (mkName.(makeFieldName r).columnName <$> fieldInfos) fields] [deriveShow]
  haskell <- makeHaskellAlias (mkName r) recordPolyName fieldInfos
  pgRead <- makePgReadAlias (mkName $ makePGReadTypeName r) recordPolyName fieldInfos
  pgWrite <- makePgWriteAlias (mkName $ makePGWriteTypeName r) recordPolyName fieldInfos
  return $ [rec, haskell, pgRead, pgWrite]
  where
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
          lift $ do
            common <- [d|
              instance QueryRunnerColumnDefault $(return pgDefColType) $(ntNameQ) where
                queryRunnerColumnDefault = fieldQueryRunnerColumn
              instance QueryRunnerColumnDefault $(return $ ConT ntName) $(ntNameQ) where
                queryRunnerColumnDefault = fieldQueryRunnerColumn
              |]
            return $ common
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
                then lift $ do
                  ins <- [d|
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
                  return $ ins
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
          if (columnDefault ci) 
            then
              lift $ [d|
                instance Default Constant $(ntNameQ) (Column (Nullable $(ntNameQ))) where
                  def = Constant f
                    where
                    f :: $(ntNameQ) -> Column (Nullable $(ntNameQ))
                    f $(return $ ConP ntName $ [VarP $ mkName "x"]) = toNullable $ unsafeCoerceColumn $ $(return pgConFuncExp) x
                |]
            else
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
makeAdaptorAndInstances env = fst <$> runStateT (do
  (_, options, _) <- get
  let models = (modelName.snd) <$> tableOptions options
  let an = makeAdapterName <$> models
  pn <- lift $ mapM (\x -> fromJust <$> lookupTypeName (x ++ "Poly")) models
  lift $ concat <$> zipWithM makeAdaptorAndInstance an pn) env

