{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Main where

import Lib
import Database.PostgreSQL.Simple
import Opaleye
import Data.Profunctor.Product.TH (makeAdaptorAndInstance)

$(makeOpaleyeModel defaultConnectInfo { connectPassword = "postgres", connectDatabase = "scratch"} "users" "Users")
$(makeAdaptorAndInstance ("pUsers") ''UsersPoly)
$(makeOpaleyeTable  defaultConnectInfo { connectPassword = "postgres", connectDatabase = "scratch"} "users" "Users")

main :: IO ()
main = return ()

