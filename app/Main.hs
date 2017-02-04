{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Lib
import ModelOptions
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.FromField
import Opaleye
import Data.Profunctor.Product.Default
import Data.Profunctor.Product.TH (makeAdaptorAndInstance)
import Control.Monad.Trans.Reader
import Data.Text
import Data.Vector
import ModelOptions

makeOpaleyeModels (connectInfo, options)
makeAdaptorAndInstances (connectInfo, options)
makeOpaleyeTables (connectInfo, options)
makeArrayInstances

getUserRows :: IO [(User, Product)]
getUserRows = do
  conn <- connect defaultConnectInfo { connectDatabase = "scratch"}
  runQuery conn $ query
  where
    query :: Opaleye.Query (UserPGRead, ProductPGRead)
    query = joinF
      (\a b -> (a, b))
      (\User {_userId = id} Product {_productUser_id = puid} -> id .== puid)
      (queryTable usersTable)
      (queryTable productsTable)

insertToUsers :: IO ()
insertToUsers = do
  conn <- connect defaultConnectInfo { connectDatabase = "scratch"}
  runInsert conn usersTable (constant $ User (Just $ UserId 6) ("User 6" ::Text) ("five@mail" :: Text) (fromList ["a", "b", "c"] :: Vector Text) (fromList [1,2,3] :: Vector Int))
  return ()
  
main :: IO ()
main = do
  rows <- getUserRows
  putStrLn $ show rows

--main :: IO ()
--main = return ()

