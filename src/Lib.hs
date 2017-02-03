{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings  #-}

module Lib where 

import Database.PostgreSQL.Simple
import Language.Haskell.TH
import Language.Haskell.TH.Syntax hiding (lift)
import Control.Monad.IO.Class
import Data.Char
import Data.Maybe
import Data.Profunctor.Product.TH (makeAdaptorAndInstance)

import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader

data ColumnType = KeyColumn | IntegerColumn  | TextColumn | TimestampColumn

data ColumnInfo = ColumnInfo { columnName ::String, columnType :: ColumnType, columnDefault :: Bool, columnNullable :: Bool}

testFunc2 :: ReaderT () Q (Maybe Name)
testFunc2 = lift $ lookupTypeName "wewq" 

type EnvM a = ReaderT (ConnectInfo, Options) Q a

getColumns :: Connection -> String -> IO [ColumnInfo]
getColumns conn tname = do
  field_rows <- query conn
    "select column_name, data_type, column_default, is_nullable from information_schema.columns where table_name = ?" 
    (Only tname) :: IO [(String, String, Maybe String, String)]
  return $ makeColumnInfo <$> field_rows
  where
    makeColumnInfo :: (String, String, Maybe String, String) -> ColumnInfo
    makeColumnInfo (name, ctype, hasDefault, isNullable) = ColumnInfo name (makeColumnType ctype) (isJust hasDefault) (isNullable == "YES")
    makeColumnType :: String -> ColumnType
    makeColumnType "text" = TextColumn
    makeColumnType "integer" = IntegerColumn

lookupNewtypeForField :: Options -> String -> Maybe Name
lookupNewtypeForField options name = lookup name (overrideDefaultTypes options) 

makePgType :: ColumnInfo -> EnvM Type
makePgType (ColumnInfo dbColumnName ct hasDefault isNullable) = do
  c <- lift $ lookupTypeName "Column"
  (_, options) <- ask
  case c of
    Nothing -> error "Couldn't find opaleye's 'Column' type in scope. Have you imported Opaleye module?"
    Just columnName -> do
      Just n <- lift $ lookupTypeName "Nullable"
      case lookupNewtypeForField options dbColumnName of
        Just pgType -> do
          return $ makeFinalType columnName n pgType
        Nothing -> do
          let columnTypeName = getPGColumnTypeName ct
          p <- lift $ lookupTypeName columnTypeName
          case p of
            Nothing -> error $ "Couldn't find opaleye's column type '" ++ columnTypeName ++ "' in scope"
            Just pgType -> return $ makeFinalType columnName n pgType
  where
    makeFinalType :: Name -> Name -> Name -> Type
    makeFinalType columnName nullableName pgType = let 
                       nn = AppT (ConT columnName) (ConT pgType)
                       in if isNullable then (AppT (ConT columnName) (AppT (ConT nullableName) (ConT pgType)))  else nn 

    getPGColumnTypeName :: ColumnType -> String
    getPGColumnTypeName TextColumn = "PGText"
    getPGColumnTypeName IntegerColumn = "PGInt4"

makeReadTypes :: [ColumnInfo] -> EnvM [Type]
makeReadTypes fieldInfos = mapM makePgType fieldInfos

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

data Options = Options { overrideDefaultTypes :: [(String, Name)] }

defaultOptions = Options []
                            
makeOpaleyeTable :: String -> String -> EnvM [Dec]
makeOpaleyeTable t r = do
  (connectInfo, options) <- ask
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

makeOpaleyeModel :: String -> String -> EnvM [Dec]
makeOpaleyeModel t r = do
  (connectInfo, options) <- ask
  let recordName = mkName r
  let recordPolyName = mkName $ r ++ "Poly"
  fieldInfos <- (lift.runIO) $ do
    conn <- connect connectInfo
    getColumns conn t
  fields <- mapM (lift.newName.columnName) fieldInfos
  let rec = DataD [] recordPolyName (tVarBindings fields) Nothing [RecC recordName $ getConstructorArgs $ zip (mkName.(addPrefix r).columnName <$> fieldInfos) fields] []
  pgRead <- makePgReadAlias (mkName $ makePGReadTypeName r) recordPolyName fieldInfos
  pgWrite <- makePgWriteAlias (mkName $ makePGWriteTypeName r) recordPolyName fieldInfos
  return $ [rec, pgRead, pgWrite] 
  where
    addPrefix :: String -> String -> String
    addPrefix pre (s:ss) = "_" ++ (toLower <$> pre) ++ (toUpper s:ss)
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
