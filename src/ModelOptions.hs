{-# LANGUAGE TemplateHaskell #-}
module ModelOptions where

import Lib

options = Options [
   ("users", usersOptions)
  ,("products", productsOptions)
  ]

usersOptions = TableOptions {
  modelName = "User",
  overrideDefaultTypes = [
    ("id", "UserId")
  ],
  generateInstancesFor = ["UserId"]
}

productsOptions = TableOptions {
  modelName = "Product",
  overrideDefaultTypes = [
    ("id", "ProductId"),
    ("user_id", "UserId")
  ],
  generateInstancesFor = ["ProductId"]
}


    

