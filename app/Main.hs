{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Lib
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.FromField
import Opaleye
import Data.Profunctor.Product.Default
import Data.Profunctor.Product.TH (makeAdaptorAndInstance)
import Control.Monad.Trans.Reader
import Data.Text

data UserId = UserId Int
data ProductId = ProductId Int

runReaderT  (makeOpaleyeModel "users" "User") $ (connectInfo, Options [("id", ''UserId)] [''UserId])
makeAdaptorAndInstance ("pUser") ''UserPoly
runReaderT (makeOpaleyeTable "users" "User") $ (connectInfo, Options [("id", ''UserId)] [''UserId])


runReaderT  (makeOpaleyeModel "products" "Product") $ (connectInfo, Options [("id", ''ProductId), ("user_id", ''UserId)] [''ProductId])
makeAdaptorAndInstance ("pProduct") ''ProductPoly
runReaderT (makeOpaleyeTable "products" "Product") $ (connectInfo, Options [("id", ''ProductId), ("user_id", ''UserId)] [''ProductId])


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
  runInsert conn usersTable (constant $ User (Just $ UserId 5) ("User 5" ::Text) ("five@mail" :: Text))
  return ()
  
main :: IO ()
main = do
  rows <- getUserRows
  putStrLn $ show $ Prelude.length rows

