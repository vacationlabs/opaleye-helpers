module Opaleye.TH.Data where

import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Monad.State.Lazy
import Language.Haskell.TH

newtype TableName = TableName String deriving (Eq)
newtype ColumnName = ColumnName String deriving (Eq)
newtype TypeName = TypeName String deriving (Eq)

instance Show TableName where
  show (TableName x) = x

instance Show ColumnName where
  show (ColumnName x) = x

instance Show TypeName where
  show (TypeName x) = x

data Options = Options { tableOptions :: [(TableName, TableOptions)] }

data TableOptions = TableOptions {
  modelName :: TypeName
  , overrideDefaultTypes :: [(ColumnName, TypeName)]
  , protectedFields :: [ColumnName]
  , autoDeriveInstances :: [TypeName] 
  , ignoreNullables :: [ColumnName]
}

data Transformation = Transformation {
  targetField :: ColumnName,
  sourceFields :: [ColumnName],
  includeSources :: Bool
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
} deriving (Show)

type TableInfo = (TableName, [ColumnInfo])
type DbInfo = [TableInfo]

type LensClassGenerated = [String]
type Env = (DbInfo, Options, LensClassGenerated)
type EnvM a = StateT Env Q a
