{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Main where

import Lib
import Database.PostgreSQL.Simple
import Opaleye
import Data.Profunctor.Product.TH (makeAdaptorAndInstance)
import Control.Monad.Trans.Reader

data UserId = UserId Int

runReaderT  (makeOpaleyeModel "users" "Users") $ (defaultConnectInfo { connectPassword = "postgres", connectDatabase = "scratch"}, Options [("id", ''UserId)])
makeAdaptorAndInstance ("pUsers") ''UsersPoly
runReaderT (makeOpaleyeTable "users" "Users") $ (defaultConnectInfo { connectPassword = "postgres", connectDatabase = "scratch"}, defaultOptions)

main :: IO ()
main = return ()

