{-# LANGUAGE DeriveLift #-}

module Opaleye.TH.Data where

import Control.Monad.State.Lazy
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

newtype TableName = TableName String deriving (Eq, Lift)
newtype ColumnName = ColumnName String deriving (Eq, Lift)
newtype FieldName = FieldName String deriving (Eq)
newtype TypeName = TypeName String deriving (Eq)

instance Show TableName where
  show (TableName x) = x

instance Show ColumnName where
  show (ColumnName x) = x

instance Show FieldName where
  show (FieldName x) = x

instance Show TypeName where
  show (TypeName x) = x

newtype Options = Options { tableOptions :: [(TableName, TableOptions)] }

data TableOptions = TableOptions {
  modelName :: TypeName
  , overrideDefaultTypes :: [(ColumnName, TypeName)]
  , protectedFields :: [ColumnName]
  , autoDeriveInstances :: [TypeName] 
  , ignoreNullables :: [ColumnName]
  , includeColumns :: Maybe [ColumnName]
}

data Transformation = Transformation {
  targetField :: FieldName,
  targetType :: TypeName,
  sourceFields :: [FieldName],
  sourcesToTarget :: Name,
  targetTosources :: Name,
  includeSources :: Bool,
  isProtected :: Bool
}

data SecondaryModel = SecondaryModel {
  targetModelName :: TypeName,
  transformations :: [Transformation]
}

type ColumnType = String

data ColumnInfo = ColumnInfo {
  columnTableName :: TableName
  , columnName ::ColumnName
  , columnType :: ColumnType
  , columnDefault :: Bool
  , columnNullable :: Bool
  , columnPrimary :: Bool
} deriving (Show, Lift)

data MappedColumnInfo a = MappedColumnInfo ColumnInfo deriving(Show)

class DbField a where
  mappedColumnInfo :: MappedColumnInfo a

type TableInfo = (TableName, [ColumnInfo])
type DbInfo = [TableInfo]

type LensClassGenerated = [String]
type Env = (DbInfo, Options, LensClassGenerated)
type EnvM a = StateT Env Q a
data RecordSpec = RecordSpecName Name | RecordSpecDec DecsQ
