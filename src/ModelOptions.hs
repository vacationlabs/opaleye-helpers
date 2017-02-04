{-# LANGUAGE TemplateHaskell #-}
module ModelOptions where

import Lib

options = Options [
   ("users", TableOptions "User" [("id", "UserId")] ["UserId"])
  ,("products", TableOptions "Product" [("id", "ProductId"), ("user_id", "UserId")] ["ProductId"])
  ]

