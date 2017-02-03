{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Main where

import Lib
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.FromField
import Opaleye
import Data.Profunctor.Product.Default
import Data.Profunctor.Product.TH (makeAdaptorAndInstance)
import Control.Monad.Trans.Reader

data UserId = UserId Int

runReaderT  (makeOpaleyeModel "users" "Users") $ (connectInfo, Options [("id", ''UserId)])
makeAdaptorAndInstance ("pUsers") ''UsersPoly
runReaderT (makeOpaleyeTable "users" "Users") $ (connectInfo, Options [("id", ''UserId)])

main :: IO ()
main = return ()

