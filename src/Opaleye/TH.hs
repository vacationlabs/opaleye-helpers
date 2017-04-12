{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings  #-}

module Opaleye.TH (
      makeOpaleyeModels
    , makeOpaleyeTables
    , makeAdaptorAndInstances
    , makeSecondaryModel
    , TableName(..)
    , ColumnName(..)
    , TypeName(..)
    , Options(..)
    , TableOptions(..)
    , module Opaleye.TH.Data
    )
where 

import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.FromField hiding (name)
import Database.PostgreSQL.Simple.HStore
import Database.PostgreSQL.Simple.ToField
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
import Opaleye.Internal.PGTypes
import qualified Opaleye.Internal.HaskellDB.Sql.Default as HDBD
import qualified Data.ByteString.Char8 as BS
import Data.Decimal
import GHC.Int
import GHC.Generics (Generic)

import Control.Monad.Trans.Class
import Control.Monad.State.Lazy

import Control.Lens hiding (swapped)

import Opaleye.TH.Data
import qualified Opaleye.TH.Transformations as TR

makePolyName :: TypeName -> TypeName
makePolyName (TypeName modelName) = TypeName $ modelName ++ "Poly"

makeTablename :: TableName -> String
makeTablename (TableName t) = t ++ "Table"

makePGReadTypeName :: TypeName -> TypeName
makePGReadTypeName (TypeName tn) = TypeName $ tn ++ "PGRead"

makePGReadAllNullableTypeName :: TypeName -> TypeName
makePGReadAllNullableTypeName tn = let (TypeName t1) = makePGReadTypeName tn in TypeName (t1 ++ "NullableWrapped")

makeToAllNullFuncName :: TypeName -> String
makeToAllNullFuncName tn = lcFirst $ (show $ makePGReadTypeName tn) ++ "Null"

makeToAllNullableFuncName :: TypeName -> String
makeToAllNullableFuncName tn = lcFirst $ (show $ makePGReadTypeName tn) ++ "ToNullableWrapped" 

makePGWriteTypeName :: TypeName -> TypeName
makePGWriteTypeName (TypeName tn) = TypeName $ tn ++ "PGWrite"

makeHaskellNameWithMaybes :: TypeName -> TypeName
makeHaskellNameWithMaybes (TypeName tn) = TypeName $ tn ++ "MaybeWrapped"

getFieldInfosForTable :: DbInfo -> TableName -> [ColumnInfo]
getFieldInfosForTable dbInfo tname = fromJust $ lookup tname dbInfo

getDbinfo :: IO Connection -> Options -> Q DbInfo
getDbinfo getConnection options = runIO $ do
  conn <- getConnection
  Prelude.mapM (fmap overrideNullables . getColumns conn options) (fst <$> tableOptions options)
  where
  overrideNullables :: TableInfo -> TableInfo
  overrideNullables (tn, cis) = case nullIgnored of
    Just ni -> if (and $ isPresent <$> ni) then (tn, fixNullable ni <$> cis) else error "Column for nullable override not found"
    Nothing -> (tn, cis)
    where
      isPresent :: ColumnName -> Bool
      isPresent cn = if cn `elem` availableColumns then True else error $ "Column for nullable override " ++ (show cn) ++ " not found in table " ++ (show tn) ++ ". Available columns are, " ++ (show availableColumns)
      availableColumns :: [ColumnName]
      availableColumns = columnName <$> cis
      fixNullable :: [ColumnName] -> ColumnInfo -> ColumnInfo
      fixNullable ni ci = if (columnName ci) `elem` ni then ci { columnNullable = False } else ci
      nullIgnored :: Maybe [ColumnName]
      nullIgnored = ignoreNullables <$> lookup tn (tableOptions options)

getColumns :: Connection -> Options -> TableName -> IO TableInfo
getColumns conn options tn@(TableName tname) = do
  let tOptions = fromJust $ lookup tn $ tableOptions options
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
  return $ (TableName tname, filterColumns tOptions $ makeColumnInfo <$> field_rows)
  where
    filterColumns :: TableOptions -> [ColumnInfo] -> [ColumnInfo]
    filterColumns to' cis = case (includeColumns to') of
      Nothing -> cis
      Just xs -> if validate xs then filter (\ci -> (columnName ci) `elem` xs) cis else error $ "Couldnot validate include column list"
      where
        tcns :: [ColumnName]
        tcns = columnName <$> cis
        validate :: [ColumnName] -> Bool
        validate cns = and $ isPresent <$> cns
          where
            isPresent :: ColumnName -> Bool
            isPresent cn = cn `elem` tcns
    makeColumnInfo :: (String, String, Maybe String, String, Bool) -> ColumnInfo
    makeColumnInfo (name, ctype, hasDefault, isNullable, isPrimary) = ColumnInfo (TableName tname) (ColumnName name) ctype (isJust hasDefault) (isNullable == "YES") isPrimary

lookupNewtypeForField :: ColumnInfo -> EnvM (Maybe Name)
lookupNewtypeForField ci = do
  (_, options, _) <- get
  return $ (mkName.show) <$> lookup (columnName ci) (overrideDefaultTypes $ getTableOptions (columnTableName ci) options)

makePgTypeWithNull :: ColumnInfo -> EnvM Type
makePgTypeWithNull ci = do
  t <- makePgType ci
  return $ case t of
    AppT (ConT _) a -> if (hasNullable a) then t else (addNullable t)
    _ -> error "Does not know how to make a nullable type"
  where
    addNullable :: Type -> Type
    addNullable (AppT a b) = let nullable = ConT (mkName "Nullable") in (AppT a (AppT nullable b))
    addNullable _ = error "Unexpected pattern while trying to wrap Nullable"
    hasNullable :: Type -> Bool
    hasNullable (AppT (ConT a) _) = nameBase a == "Nullable" 
    hasNullable _ = False

makePgType :: ColumnInfo -> EnvM Type
makePgType ci@(ColumnInfo  {..}) = do
  c <- lift $ lookupTypeName "Column"
  case c of
    Nothing -> error "Couldn't find opaleye's 'Column' type in scope. Have you imported Opaleye module?"
    Just opColumn -> do
      Just n <- lift $ lookupTypeName "Nullable"
      x <- lookupNewtypeForField ci
      case x of
        Just pgType -> do
          return $ makeFinalType opColumn n (ConT pgType)
        Nothing -> do
          pgType <- getPGColumnType columnType
          return $ makeFinalType opColumn n pgType
  where
    makeFinalType :: Name -> Name -> Type -> Type
    makeFinalType typeName nullableName pgType = let 
      nn = AppT (ConT typeName) pgType
      in if columnNullable then (AppT (ConT typeName) (AppT (ConT nullableName) pgType))  else nn 

getPGColumnType :: ColumnType -> EnvM Type
getPGColumnType ct = lift $ (getType ct) 
  where
    getType :: ColumnType -> Q Type
    getType ct' = do
      pg_array <- ConT <$> fromJust <$> lookupTypeName "PGArray"
      case ct' of 
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
        "hstore"      -> ConT <$> fromJust <$> lookupTypeName "PGJson"
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
        n -> error "Unknown pgType name " ++ (show n)
  g <- lift $ lookupValueName tname
  case g of
    Just a -> return $ VarE a
    Nothing -> error $ "Cannot find " ++ tname
getPGConFuncExp (AppT _ pgt) = do
  g <- lift $ lookupValueName "pgArray"
  let pga_func = case g of
        Just a -> VarE a
        Nothing -> error $ "Cannot find pgArray"
  func1 <- getPGConFuncExp pgt
  return $ AppE pga_func func1
getPGConFuncExp _ = error "Unexpected pattern while trying to make conversion function to pgType"

makeReadTypes :: [ColumnInfo] -> EnvM [Type]
makeReadTypes fieldInfos = mapM makePgType fieldInfos

makeReadTypesWithNulls :: [ColumnInfo] -> EnvM [Type]
makeReadTypesWithNulls fieldInfos = mapM makePgTypeWithNull fieldInfos

makeHaskellTypes :: [ColumnInfo] -> EnvM [Type]
makeHaskellTypes fieldInfos = mapM makeHaskellType fieldInfos

makeHaskellTypesWithMaybes :: [ColumnInfo] -> EnvM [Type]
makeHaskellTypesWithMaybes fieldInfos = mapM makeHaskellTypeWithMaybe fieldInfos

safeLookupTypeName :: TypeName -> Q Name
safeLookupTypeName (TypeName name) = do
  n <- lookupTypeName name
  case n of
    Nothing -> error $ "Cannot find name '" ++ name ++ "'"
    Just x -> return x

getHaskellTypeFor :: ColumnType -> EnvM Type
getHaskellTypeFor ct = case ct of
  "bool"        -> lift $ (ConT) <$> safeLookup' "Bool"
  "int2"        -> lift $ (ConT) <$> safeLookup' "Int16"
  "int4"        -> lift $ (ConT) <$> safeLookup' "Int"
  "int8"        -> lift $ (ConT) <$> safeLookup' "Int64"
  "float4"      -> lift $ (ConT) <$> safeLookup' "Float"
  "float8"      -> lift $ (ConT) <$> safeLookup' "Double"
  "numeric"     -> lift $ (ConT) <$> safeLookup' "Decimal"
  "char"        -> lift $ (ConT) <$> safeLookup' "Char"
  "text"        -> lift $ (ConT) <$> safeLookup' "Text"
  "bytea"       -> lift $ (ConT) <$> safeLookup' "ByteString"
  "date"        -> lift $ (ConT) <$> safeLookup' "Day"
  "timestamp"   -> lift $ (ConT) <$> safeLookup' "LocalTime"
  "timestamptz" -> lift $ (ConT) <$> safeLookup' "UTCTime"
  "time"        -> lift $ (ConT) <$> safeLookup' "TimeOfDay"
  "timetz"      -> lift $ (ConT) <$> safeLookup' "TimeOfDay"
  "interval"    -> lift $ (ConT) <$> safeLookup' "DiffTime"
  "uuid"        -> lift $ (ConT) <$> safeLookup' "UUID"
  "json"        -> lift $ (ConT) <$> safeLookup' "Value"
  "jsonb"       -> lift $ (ConT) <$> safeLookup' "Value"
  "hstore"      -> lift $ (ConT) <$> safeLookup' "HStoreList"
  "varchar"     -> lift $ (ConT) <$> safeLookup' "Text"
  "_varchar"    -> (AppT array) <$> getHaskellTypeFor "varchar"
  "_text"       -> (AppT array) <$> getHaskellTypeFor "varchar"
  "_int4"       -> (AppT array) <$> getHaskellTypeFor "int4"
  other         -> error $ "Unimplemented PostgresQL type conversion for " ++ show other
  where
    safeLookup' :: String -> Q Name
    safeLookup' name = safeLookupTypeName (TypeName name)
    array :: Type
    array = ConT (''[])

makeRawHaskellType :: ColumnInfo -> EnvM Type
makeRawHaskellType ci = do
    getHaskellTypeFor (columnType ci)

makeHaskellTypeWithMaybe :: ColumnInfo -> EnvM Type
makeHaskellTypeWithMaybe ci = do
  nt <- lookupNewtypeForField ci
  typ <- case nt of
    Nothing -> makeRawHaskellType ci
    Just t -> return $ ConT t
  return $ (AppT (ConT ''Maybe) typ)

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

makeOpaleyeTables :: IO Connection -> Options -> Q [Dec]
makeOpaleyeTables getConn opt = do
  dbInfo <- getDbinfo getConn opt
  makeOpaleyeTables' (dbInfo, opt, [])

makeOpaleyeTables' :: Env -> Q [Dec]
makeOpaleyeTables' env = do
  (decs, (_, _, _)) <- runStateT (do
    (_, options, _) <- get
    let names = fst <$> tableOptions options
    let models = (modelName.snd) <$> tableOptions options
    typeClassDecs <- makeModelTypeClass
    tables <- Data.List.concat <$> zipWithM makeOpaleyeTable names models
    lenses <- Data.List.concat <$> zipWithM makeLensesForTable names models
    return $ typeClassDecs ++ tables ++ lenses) env
  return decs
  where
    makeModelTypeClass :: EnvM [Dec]
    makeModelTypeClass = lift $ do
      dbModel <- lookupTypeName "DbModel"
      case dbModel of 
        Just _ -> return []
        Nothing -> do
          Just _ <- lookupTypeName "MonadIO"
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

makeLensesForTable :: TableName -> TypeName -> EnvM [Dec]
makeLensesForTable t r = do
  (_, options, _) <- get
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
      extractDecClasses decs' = fromJust <$> filter isJust (extractClassName <$> decs')
        where
        extractClassName :: Dec -> Maybe String
        extractClassName (ClassD _ name _ _ _) = Just $ nameBase name
        extractClassName _ = Nothing
        
lcFirst :: String -> String
lcFirst [] = []
lcFirst (x:xs) = (toLower x):xs
ucFirst :: String -> String
ucFirst [] = []
ucFirst (x:xs) = (toUpper x):xs

makeOpaleyeTable :: TableName -> TypeName -> EnvM [Dec]
makeOpaleyeTable t r = do
  (dbInfo, options, _) <- get
  let fieldInfos = getFieldInfosForTable dbInfo t
  let tableOptions = getTableOptions t options
  functions <- case includeColumns tableOptions of
    Just _ -> return []
    Nothing -> makeModelInstance fieldInfos
  lift $ do
    Just adapterFunc <- lookupValueName $ makeAdapterName r
    Just constructor <- lookupValueName $ show r
    Just tableTypeName <- lookupTypeName "Table"
    Just tableFunctionName <- lookupValueName "Table"
    pgWriteTypeName <- safeLookupTypeName $ makePGWriteTypeName r
    pgReadTypeName <- safeLookupTypeName $ makePGReadTypeName r
    let funcName = mkName $ makeTablename t 
    let funcType = AppT (AppT (ConT tableTypeName) (ConT pgWriteTypeName)) (ConT pgReadTypeName)
    let signature = SigD funcName funcType
    fieldExps <- (getTableTypes fieldInfos)
    let
      funcExp = AppE (AppE (ConE tableFunctionName) (LitE $ StringL $ show t)) funcExp2
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
        mkExp rq opt ci = let 
                           ty = if (columnDefault ci) then opt else rq 
                         in AppE (VarE ty) (LitE $ StringL $ show $ columnName ci)
    makeModelInstance :: [ColumnInfo] -> EnvM [Dec]
    makeModelInstance fieldInfos = do
      let (Just pField) = getPrimaryKeyField t r
      convertToPgWrite <- lift $ makeConversionFunction
      lift $ do 
        insertExp <- [e|liftIO $ Prelude.head <$> runInsertManyReturning conn $(return $ VarE $ mkName $ makeTablename t) [(toWrite $ constant model)] id |]
        updateExp <- [e|liftIO $ Prelude.head <$> runUpdateReturning conn $(return $ VarE $ mkName $ makeTablename t) (\_ -> toWrite $ constant model) (\f -> ($(return $ VarE $ mkName pField) f) .== (constant $  $(return $ VarE $ mkName pField) model)) id |]
        deleteExp <- [e|liftIO $ runDelete conn $(return $ VarE $ mkName $ makeTablename t) (\f -> ($(return $ VarE $ mkName pField) f) .== (constant $  $(return $ VarE $ mkName pField) model)) |]
        let pat = [VarP $ mkName "conn", VarP $ mkName "model"]
        let insertFunc = FunD (mkName "insertModel") [Clause pat (NormalB insertExp) convertToPgWrite]
        let updateFunc = FunD (mkName "updateModel") [Clause pat (NormalB updateExp) convertToPgWrite]
        let deleteFunc = FunD (mkName "deleteModel") [Clause pat (NormalB deleteExp) []]
        return [InstanceD Nothing [] (AppT (ConT $ mkName "DbModel") (ConT $ mkName $ show r)) [insertFunc, updateFunc, deleteFunc]]
      where
        makeConversionFunction :: Q [Dec]
        makeConversionFunction = do
          let
            pgReadType = ConT $ (mkName $ show $ makePGReadTypeName r)
            pgWriteType = ConT $ (mkName $ show $ makePGWriteTypeName r)
            conversionFunctionSig = SigD (mkName "toWrite") $ AppT (AppT ArrowT pgReadType) pgWriteType
            conversionFunction = FunD (mkName "toWrite") [Clause [makePattern] (NormalB conExp) []]
          return $ [conversionFunctionSig, conversionFunction]
          where
            conExp :: Exp
            conExp = foldl AppE (ConE $ mkName $ show r) $ getFieldExps
            getFieldExps :: [Exp]
            getFieldExps = zipWith getFieldExp fieldInfos [1..]
              where
              getFieldExp :: ColumnInfo -> Int -> Exp
              getFieldExp ci idx = if (columnDefault ci) then (AppE (ConE $ mkName "Just") mkVarExp) else mkVarExp
                where
                  mkVarExp :: Exp
                  mkVarExp = VarE $ mkName $ "a" ++ (show idx)
            makePattern :: Pat
            makePattern = ConP (mkName $ show r) $ VarP <$> (mkName.(\x -> ('a':x)).show) <$>  take (Prelude.length fieldInfos) ([1..]::[Int])
        getPrimaryKeyField :: TableName -> TypeName -> (Maybe String)
        getPrimaryKeyField (TableName _) modelName = case (filter (\ci -> columnPrimary ci)) fieldInfos of
            [primaryField] -> Just $ makeFieldName modelName (columnName primaryField)
            _ -> Nothing
  
makeAdapterName :: TypeName -> String
makeAdapterName (TypeName mn) = 'p':mn

makeOpaleyeModels :: IO Connection -> Options -> Q [Dec]
makeOpaleyeModels getconn opt = do
  dbInfo <-  getDbinfo getconn opt
  makeOpaleyeModels' (dbInfo, opt, [])

makeOpaleyeModels' :: Env -> Q [Dec]
makeOpaleyeModels' env = fst <$> runStateT (do
  newTypeDecs <- makeNewTypes
  (_, options, _) <- get
  let names = fst <$> tableOptions options
  let models = (modelName.snd) <$> tableOptions options
  instances <- makeNewtypeInstances
  decs <- Data.List.concat <$> zipWithM makeOpaleyeModel names models
  return $ newTypeDecs ++ decs ++ instances) env

collectNewTypes :: EnvM [(ColumnInfo, TypeName)]
collectNewTypes = do
  (_, options, _) <- get
  newtypes <- Data.List.concat <$> mapM getNewTypes (tableOptions options)
  filterM isNew newtypes
  where
    isNew :: (ColumnInfo, TypeName) -> EnvM Bool
    isNew (_, TypeName n) = lift $ isNothing <$> lookupTypeName n
    getNewTypes :: (TableName, TableOptions) -> EnvM [(ColumnInfo, TypeName)]
    getNewTypes (tbName, tbOptions) = do
      (dbInfo, _, _) <- get
      let fieldInfos = getFieldInfosForTable dbInfo tbName
      return $ fromJust <$> (filter isJust $ (tryNewType tbOptions) <$> fieldInfos)
    tryNewType :: TableOptions -> ColumnInfo -> Maybe (ColumnInfo, TypeName)
    tryNewType to' ci = (\n -> (ci, n)) <$> lookup (columnName ci) (overrideDefaultTypes to')

makeNewTypes :: EnvM [Dec]
makeNewTypes = do
  nts <- collectNewTypes
  (_, b) <- foldM makeNewType ([], []) nts
  return b
  where
  makeNewType :: ([TypeName], [Dec]) -> (ColumnInfo, TypeName) -> EnvM ([TypeName], [Dec])
  makeNewType (added, decs) (ci, nt_name) = do
    if nt_name `elem` added then (return (added, decs)) else do
      dec <- makeNewType' nt_name
      return (nt_name:added, dec:decs)
    where
      makeNewType' :: TypeName -> EnvM Dec
      makeNewType' (TypeName name) = do
        let bang' = Bang NoSourceUnpackedness NoSourceStrictness
        haskellType <- makeRawHaskellType ci
        return $ NewtypeD [] (mkName name) [] Nothing (NormalC (mkName name) [(bang', haskellType)]) [ConT ''Show, ConT ''Eq, ConT ''Ord, ConT ''Generic]

makeFieldName :: TypeName -> ColumnName -> String
makeFieldName (TypeName modelName) (ColumnName (s:ss)) = "_" ++ (toLower <$> modelName) ++ (toUpper s:replaceUnderscore ss)
makeFieldName (TypeName _) (ColumnName []) = error "Empty column name"

replaceUnderscore :: String -> String
replaceUnderscore ('_':x:xs) = (toUpper x):(replaceUnderscore xs)
replaceUnderscore ('_':xs) = (replaceUnderscore xs)
replaceUnderscore (x:xs) = x:(replaceUnderscore xs)
replaceUnderscore [] = ""

makeOpaleyeModel :: TableName -> TypeName -> EnvM [Dec]
makeOpaleyeModel t r = do
  (dbInfo, options, _) <- get
  let recordName = mkName $ show r
  let recordPolyName = mkName $ show $ makePolyName r
  let fieldInfos = getFieldInfosForTable dbInfo t
  deriveInstances <- lift $ mapM (fmap (ConT).safeLookupTypeName) $ autoDeriveInstances $ getTableOptions t options
  fields <- mapM (lift.newName.show.columnName) fieldInfos
  let rec = DataD [] recordPolyName (tVarBindings fields) Nothing [RecC recordName $ getConstructorArgs $ zip (mkName.(makeFieldName r).columnName <$> fieldInfos) fields] deriveInstances
  (haskell, haskellWithMaybes) <- makeHaskellAlias r recordPolyName fieldInfos
  (pgRead, pgReadWithNulls) <- makePgReadAlias (mkName $ show $ makePGReadTypeName r) recordPolyName fieldInfos
  pgWrite <- makePgWriteAlias (mkName $ show $ makePGWriteTypeName r) recordPolyName fieldInfos
  toAllNullable <- lift $ makeAllNullableFunction fieldInfos
  allNull <- lift $ makeAllNullFunction fieldInfos
  let qrifmw = makeQueryRunnerInstanceForMaybewrapped fieldInfos
  return $ [rec, haskell, haskellWithMaybes, pgRead, pgReadWithNulls, pgWrite] ++ toAllNullable ++ allNull ++ [qrifmw]
  where
    makeQueryRunnerInstanceForMaybewrapped :: [ColumnInfo] -> Dec
    makeQueryRunnerInstanceForMaybewrapped fieldInfos = InstanceD Nothing [] instanceHeadType [fund]
      where
        fund :: Dec
        fund = FunD (mkName "def") [clause']
          where
            clause' :: Clause
            clause' = Clause [] (NormalB exp') makeWithMaybesToHaskell
            exp' :: Exp
            exp' = AppE (AppE (VarE $ mkName "rmap") (VarE funName)) (VarE $ mkName "def")
            funName :: Name
            funName = mkName "fun1"
            makeWithMaybesToHaskell :: [Dec]
            makeWithMaybesToHaskell = let
                TypeName hname = r
                withMaybesName' = ConT $ (mkName $ show $ makeHaskellNameWithMaybes r)
                unMaybefyFunctionSig = SigD funName $ AppT (AppT ArrowT withMaybesName') (AppT (ConT ''Maybe) (ConT $ mkName hname))
                unMaybefyFunction = FunD funName [
                  Clause [makeNothingPattern] (NormalB $ ConE (mkName "Nothing")) [],
                  Clause [makePattern] (NormalB $ funExp) []
                  ]
                in [unMaybefyFunctionSig, unMaybefyFunction]
                where
                  makeNothingPattern :: Pat
                  makeNothingPattern = ConP (mkName $ show r) $ replicate (Prelude.length fieldInfos) $ ConP (mkName "Nothing") []
                  funExp :: Exp
                  funExp = AppE (ConE (mkName "Just")) $ foldl AppE (ConE $ mkName $ show r) $ getFieldExps
                  makePattern :: Pat
                  makePattern = (ConP $ mkName $ show r) $ zipWith getFieldPat fieldInfos [1..]
                    where
                    getFieldPat :: ColumnInfo -> Int -> Pat
                    getFieldPat ci idx = if ((columnNullable) ci) then mkVarPat else (ConP (mkName "Just")[mkVarPat]) 
                      where
                        mkVarPat :: Pat
                        mkVarPat = VarP $ mkName $ "a" ++ (show idx)
                  getFieldExps :: [Exp]
                  getFieldExps =  VarE <$> (mkName.(\x -> ('a':x)).show) <$>  take (Prelude.length fieldInfos) ([1..]::[Int])
        maybeModelType :: Type
        maybeModelType = AppT (ConT $ mkName "Maybe") (ConT $ mkName $ show r)
        nullablesType :: Type
        nullablesType = ConT $ (mkName $ (show $ makePGReadAllNullableTypeName r))
        instanceHeadType :: Type
        instanceHeadType = AppT (AppT (AppT (ConT $ mkName "Default") (ConT $ mkName "QueryRunner")) nullablesType) maybeModelType
    makeAllNullFunction :: [ColumnInfo] -> Q [Dec]
    makeAllNullFunction fieldInfos = do
      let
        pgReadWithNullsType = ConT $ (mkName $ (show $ makePGReadAllNullableTypeName r))
        toAllNullFuncName = makeToAllNullFuncName r
        conversionFunctionSig = SigD (mkName toAllNullFuncName) $ pgReadWithNullsType
        conversionFunction = FunD (mkName toAllNullFuncName) [Clause [] (NormalB conExp) []]
      return $ [conversionFunctionSig, conversionFunction]
      where
        conExp :: Exp
        conExp = foldl AppE (ConE $ mkName $ show r) $ getFieldExps
        getFieldExps :: [Exp]
        getFieldExps = const (VarE $ mkName "Opaleye.null") <$> fieldInfos
    makeAllNullableFunction :: [ColumnInfo] -> Q [Dec]
    makeAllNullableFunction fieldInfos = do
      let
        pgReadType = ConT $ (mkName $ show $ makePGReadTypeName r)
        pgReadWithNullsType = ConT $ (mkName $ (show $ makePGReadAllNullableTypeName r))
        toAllNullFuncName = makeToAllNullableFuncName r
        conversionFunctionSig = SigD (mkName toAllNullFuncName) $ AppT (AppT ArrowT pgReadType) pgReadWithNullsType
        conversionFunction = FunD (mkName toAllNullFuncName) [Clause [makePattern] (NormalB conExp) []]
      return $ [conversionFunctionSig, conversionFunction]
      where
        conExp :: Exp
        conExp = foldl AppE (ConE $ mkName $ show r) $ getFieldExps
        getFieldExps :: [Exp]
        getFieldExps = zipWith getFieldExp fieldInfos [1..]
          where
          getFieldExp :: ColumnInfo -> Int -> Exp
          getFieldExp ci idx = if ((columnNullable) ci) then mkVarExp else (AppE (VarE $ mkName "toNullable") mkVarExp) 
            where
              mkVarExp :: Exp
              mkVarExp = VarE $ mkName $ "a" ++ (show idx)
        makePattern :: Pat
        makePattern = ConP (mkName $ show r) $ VarP <$> (mkName.(\x -> ('a':x)).show) <$>  take (Prelude.length fieldInfos) ([1..]::[Int])
    makeHaskellAlias :: TypeName -> Name -> [ColumnInfo] -> EnvM (Dec, Dec)
    makeHaskellAlias htname@(TypeName tn) poly_name fieldInfos = do
      let hname = mkName tn
      types <- makeHaskellTypes fieldInfos
      maybeTypes <- makeHaskellTypesWithMaybes fieldInfos
      let (TypeName maybeWrappedName) = makeHaskellNameWithMaybes htname
      return $ (TySynD hname [] (full_type types), TySynD (mkName $ maybeWrappedName) [] (full_type maybeTypes))
      where
        full_type :: [Type] -> Type
        full_type typs = foldl AppT (ConT poly_name) typs
    makePgReadAlias :: Name -> Name -> [ColumnInfo] -> EnvM (Dec, Dec)
    makePgReadAlias name modelType fieldInfos = do
      readType <- makePgReadType modelType fieldInfos
      readTypeWithNulls <- makePgReadTypeWithNulls modelType fieldInfos
      let nameWithNulls = mkName $ show $ makePGReadAllNullableTypeName r
      return $ (TySynD name [] readType, TySynD nameWithNulls [] readTypeWithNulls)
    makePgReadTypeWithNulls :: Name -> [ColumnInfo] -> EnvM Type
    makePgReadTypeWithNulls modelType fieldInfos = do
      readTypes <- makeReadTypesWithNulls fieldInfos
      return $ foldl AppT (ConT modelType) readTypes
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
        makeBangType (fieldName, name) = let bang' = Bang NoSourceUnpackedness NoSourceStrictness in (fieldName, bang', VarT name)

makeNewtypeInstances :: EnvM [Dec]
makeNewtypeInstances = do
  newTypes <- groupDups <$> collectNewTypes
  Data.List.concat  <$> (mapM makeInstancesForNewtypeColumn newTypes)
  where
    groupDups :: [(ColumnInfo, TypeName)] -> [(ColumnInfo, Name)]
    groupDups pairs = fmap collect $ nub $ fmap snd pairs
      where
        collect :: TypeName -> (ColumnInfo, Name)
        collect tn = (fromJust $ lookup tn $ swapped, mkName $ show tn)
        swapped :: [(TypeName, ColumnInfo)]
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
        makeFromFieldInstance _ ntName' = do
          let ntNameQ = return $ ConT ntName'
          let ntNameExpQ = return $ ConE ntName'
          lift $ [d|
            instance FromField $(ntNameQ) where
              fromField field bs = fmap $(ntNameExpQ) (fromField field bs)
            |]
        makeQueryRunnerInstance :: ColumnInfo -> Name -> EnvM [Dec]
        makeQueryRunnerInstance cli ntName' = do
          pgDefColType <- getPGColumnType (columnType cli)
          let ntNameQ = return $ ConT ntName'
          lift $ do
            common <- [d|
              instance QueryRunnerColumnDefault $(return pgDefColType) $(ntNameQ) where
                queryRunnerColumnDefault = fieldQueryRunnerColumn
              instance QueryRunnerColumnDefault $(return $ ConT ntName') $(ntNameQ) where
                queryRunnerColumnDefault = fieldQueryRunnerColumn
              |]
            return $ common
        makeDefaultInstance :: ColumnInfo -> Name -> EnvM [Dec]
        makeDefaultInstance cli ntName' = do
          pgDefColType <- getPGColumnType(columnType cli)
          pgConFuncExp <- getPGConFuncExp pgDefColType
          let ntNameQ = return $ ConT ntName'
          if (columnNullable cli)
            then
              (makeDefaultInstanceForNullable cli ntName')
            else 
              if (columnDefault cli) 
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
        makeDefaultInstanceForNullable cli ntName' = do
          pgDefColType <- getPGColumnType(columnType cli)
          pgConFuncExp <- getPGConFuncExp pgDefColType
          let ntNameQ = return $ ConT ntName'
          if (columnDefault cli) 
            then
              lift $ [d|
                instance Default Constant $(ntNameQ) (Column (Nullable $(ntNameQ))) where
                  def = Constant f
                    where
                    f :: $(ntNameQ) -> Column (Nullable $(ntNameQ))
                    f $(return $ ConP ntName' $ [VarP $ mkName "x"]) = toNullable $ unsafeCoerceColumn $ $(return pgConFuncExp) x
                |]
            else
              lift $ [d|
                instance Default Constant $(ntNameQ) (Column $(return pgDefColType)) where
                  def = Constant f
                    where
                    f ($(return $ ConP ntName' $ [VarP $ mkName "x"])) = $(return pgConFuncExp) x
                instance Default Constant $(ntNameQ) (Column $(ntNameQ)) where
                  def = f <$> def
                    where
                    f :: Column $(return pgDefColType) -> Column $(ntNameQ)
                    f  = unsafeCoerceColumn
                |]

getTableOptions :: TableName -> Options -> TableOptions
getTableOptions tname options = fromJust $ lookup tname (tableOptions options)

makeAdaptorAndInstances :: IO Connection -> Options -> Q [Dec]
makeAdaptorAndInstances getConnection opt = do
  dbInfo <- getDbinfo getConnection opt
  makeAdaptorAndInstances' (dbInfo, opt, [])

createCommonInstances :: Q [Dec]
createCommonInstances = do
  ClassI _ i <- reify ''Default
  let instanceTypes = getTypeFromInstanceD <$> i
  defConstant <- [t|Default Constant HStoreList (Column PGJson)|]
  hstoreInstances <- case find (== defConstant) instanceTypes of
    Nothing -> [d|
      instance Default Constant HStoreList (Column PGJson) where
        def = Constant f1
          where
          f1 :: HStoreList -> Column PGJson
          f1 hl = castToType "hstore" $ toStringLit hl
          toStringLit :: HStoreList -> String
          toStringLit hl = let (Escape bs) = toField hl in HDBD.quote (BS.unpack bs)
      instance QueryRunnerColumnDefault PGJson HStoreList where
        queryRunnerColumnDefault = fieldQueryRunnerColumn
      |]
    _ -> return []
  defNumeric <- [t|Default Constant Decimal (Column PGNumeric)|]
  decimalInstances <- case find (== defNumeric) instanceTypes of
    Nothing -> [d|
      instance FromField Decimal where
        fromField field maybebs = (realToFrac :: Rational -> Decimal)  <$> fromField field maybebs
      instance QueryRunnerColumnDefault PGNumeric Decimal where
        queryRunnerColumnDefault = fieldQueryRunnerColumn
      instance Default Constant Decimal (Column PGNumeric) where
        def = Constant f1
          where
          f1 :: Decimal -> (Column PGNumeric)
          f1 x = unsafeCoerceColumn $ pgDouble $ realToFrac x
      |]
    _ -> return []
  return $ hstoreInstances ++ decimalInstances

getTypeFromInstanceD :: Dec -> Type
getTypeFromInstanceD (InstanceD _ _ t _) = t

makeAdaptorAndInstances' :: Env -> Q [Dec]
makeAdaptorAndInstances' env = fst <$> runStateT (do
  (_, options, _) <- get
  let models = (modelName.snd) <$> tableOptions options
  let an = makeAdapterName <$> models
  pn <- lift $ mapM (\x -> fromJust <$> lookupTypeName (show $ makePolyName x)) models
  decs <- lift $ (Data.List.concat <$> zipWithM makeAdaptorAndInstance an pn)
  return $ decs 
  ) env

getProtectedFieldsFor :: Options -> TypeName -> [ColumnName]
getProtectedFieldsFor (Options options) typename' = let
  mktuple x = (modelName x, protectedFields x)
  pl = (mktuple.snd) <$> options
  in fromMaybe [] (lookup typename' pl)

getIncludedFieldsFor :: Options -> TypeName -> Maybe [ColumnName]
getIncludedFieldsFor (Options options) typename' = let
  mktuple x = (modelName x, includeColumns x)
  pl = (mktuple.snd) <$> options
  in fromMaybe Nothing (lookup typename' pl)

makeSecondaryModel :: Name -> TypeName -> [Transformation] -> Options -> Q [Dec]
makeSecondaryModel source target transformations options = do
  [rec, mltr, mrtl] <- TR.transform source target transformations
  let 
    TypeName targetName  = target
    defaultT = (ConT $ mkName "Default")
    queryRunnerT = (ConT $ mkName "QueryRunner")
    pgReadT = (ConT $ mkName $ (nameBase source ++ "PGRead"))
    targetT = (ConT $ mkName $ targetName)
    instanceHeadQr = AppT (AppT (AppT defaultT queryRunnerT) pgReadT) targetT
    instanceHeadDbm = AppT (ConT $ mkName "DbModel") targetT
  d <- defQr mltr
  let 
    qrInstance = InstanceD Nothing [] instanceHeadQr [d]
    cnToString cn = makeFieldName target cn
    protectedFields = (show <$> (getProtected transformations)) ++ (cnToString <$> (getProtectedFieldsFor options (TypeName $ nameBase source)))
  dbMInstance <- if isSourceFull then do
    c <- dbmInstance mrtl mltr
    return [InstanceD Nothing [] instanceHeadDbm c] else return []
  protectedLenses <- makeLenses'' (TypeName $ nameBase source) (RecordSpecDec (return [rec])) protectedFields True []
  normalLenses <- makeLenses'' (TypeName $ nameBase source) (RecordSpecDec (return [rec])) protectedFields False []
  return $ [rec, qrInstance] ++ dbMInstance ++ (filterRecordDecs (protectedLenses ++ normalLenses))
  where
    isSourceFull :: Bool
    isSourceFull = isNothing $ getIncludedFieldsFor options (TypeName $ nameBase source)
    getProtected :: [Transformation] -> [FieldName]
    getProtected transformations' = targetField <$> (filter isProtected transformations')
    filterRecordDecs :: [Dec] -> [Dec]
    filterRecordDecs decs = filter (Prelude.not.isRecordDec) decs
      where
        isRecordDec :: Dec -> Bool
        isRecordDec (DataD _ _ _ _ _ _) = True
        isRecordDec _ = False
    defQr :: Dec -> Q Dec
    defQr fd = do
      exp' <- [e| rmap mltr def |]
      return $ FunD (mkName "def") [Clause [] (NormalB exp') [fd]]
    dbmInstance :: Dec -> Dec -> Q [Dec]
    dbmInstance fd fd2 = do
      expi <- [e| mltr <$> (insertModel conn (mrtl model))|]
      expu <- [e| mltr <$> (updateModel conn (mrtl model))|]
      expd <- [e| deleteModel conn (mrtl model)|]
      let
        ptrn = [VarP $ mkName "conn", VarP $ mkName "model"]
        iFun = FunD (mkName "insertModel") [Clause ptrn (NormalB expi) [fd, fd2]]
        uFun = FunD (mkName "updateModel") [Clause ptrn (NormalB expu) [fd, fd2]]
        dFun = FunD (mkName "deleteModel") [Clause ptrn (NormalB expd) [fd, fd2]]
      return [iFun, uFun, dFun]

makeLenses'':: TypeName -> RecordSpec -> [String] -> Bool -> LensClassGenerated -> Q [Dec]
makeLenses'' modelname recordSpec protected makeProtected clg  = do
  case makeProtected of
    True -> makeProtectedLenses recordSpec clg 
    False -> makeNormalLenses recordSpec clg
  where
    makeProtectedLenses :: RecordSpec -> LensClassGenerated -> Q [Dec]
    makeProtectedLenses recordSpec' clg' = do
      let
        -- The following code extracts list of generated
        -- classes from the state and only generate classes
        -- if they are not on that list.
        lr0 = abbreviatedFields & generateUpdateableOptics .~ False
        lr1 = lr0 & lensField .~ (protectedFieldNamer clg' True)
        lr2 = lr0 & lensField .~ (protectedFieldNamer clg' False)
        lr3 = (lr2 & createClass .~ False )
        in do
          decs1 <- makeLensesWith' lr1 recordSpec'
          decs2 <- makeLensesWith' lr3 recordSpec'
          return $ decs1 ++ decs2
    makeNormalLenses :: RecordSpec -> LensClassGenerated -> Q [Dec]
    makeNormalLenses recordSpec' clg' = do
      let
        lr1 = abbreviatedFields & lensField .~ (normalFieldNamer clg' True)
        lr2 = abbreviatedFields & lensField .~ (normalFieldNamer clg' False)
        lr3 = (lr2 & createClass .~ False )
        in do
          decs1 <- makeLensesWith' lr1 recordSpec'
          decs2 <- makeLensesWith' lr3 recordSpec'
          return $ decs1 ++ decs2
    protectedFieldNamer :: [String] -> Bool -> Name -> [Name] -> Name -> [DefName]
    protectedFieldNamer clgn eec x y fname = let
      sFname = "Has" ++ (ucFirst $ drop ((length $ show $ modelname) + 1) $ nameBase fname)
      prted = elem sFname protected
      in if eec
         then (if (prted && (Prelude.not $ elem sFname clgn)) then (abbreviatedNamer x y fname) else [])
         else (if (prted && (elem sFname clgn)) then (abbreviatedNamer x y fname) else [])
    normalFieldNamer :: [String] -> Bool -> Name -> [Name] -> Name -> [DefName]
    normalFieldNamer clgn eec x y fname = let
      sFname = "Has" ++ (ucFirst $ drop ((length $ show modelname) + 1) $ nameBase fname)
      prted = (Prelude.not $ elem (nameBase fname) protected)
      in if eec
         then (if (prted && (Prelude.not $ elem sFname clgn)) then (abbreviatedNamer x y fname) else [])
         else (if (prted && (elem sFname clgn)) then (abbreviatedNamer x y fname) else [])
    makeLensesWith' :: LensRules -> RecordSpec -> Q [Dec]
    makeLensesWith' lr rs = case rs of
      RecordSpecName n -> makeLensesWith lr n
      RecordSpecDec qd -> declareLensesWith lr qd

makeLenses' :: TypeName -> [String] -> Bool -> EnvM [Dec]
makeLenses' modelName protected makeProtected = do
  (_, _, clg) <- get
  let modelTypeName = mkName $ show $ makePolyName modelName
  lift $ makeLenses'' modelName (RecordSpecName modelTypeName) protected makeProtected clg
