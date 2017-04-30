{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Opaleye.TH.CommonInstances where

import Opaleye
import VacationLabs.Database.PostgreSQL.Simple.HStore
import Database.PostgreSQL.Simple.FromField
import Data.Profunctor.Product.Default
import qualified Data.ByteString.Char8 as BS
import Data.Decimal
import qualified Opaleye.Internal.HaskellDB.Sql.Default as HDBD
import Opaleye.Internal.PGTypes
import Database.PostgreSQL.Simple.ToField

instance FromField Decimal where
  fromField field maybebs = (realToFrac :: Rational -> Decimal)  <$> fromField field maybebs
instance QueryRunnerColumnDefault PGNumeric Decimal where
  queryRunnerColumnDefault = fieldQueryRunnerColumn
instance Default Constant Decimal (Column PGNumeric) where
  def = Constant f1
    where
    f1 :: Decimal -> (Column PGNumeric)
    f1 x = unsafeCoerceColumn $ pgDouble $ realToFrac x

instance Default Constant HStoreList (Column PGJson) where
  def = Constant f1
    where
    f1 :: HStoreList -> Column PGJson
    f1 hl = castToType "hstore" $ toStringLit hl
    toStringLit :: HStoreList -> String
    toStringLit hl = let (Escape bs) = toField hl in HDBD.quote (BS.unpack bs)
instance QueryRunnerColumnDefault PGJson HStoreList where
  queryRunnerColumnDefault = fieldQueryRunnerColumn
