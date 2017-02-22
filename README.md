# th-opaleye

This is a Template Haskell lib that generates boilerplates that helps to work with Opaleye.

You need to put the configuration for this in another haskell file, and import it in the main file
where you are going to make the calls to the TH functions

So this can be your Main.hs file

```
  import OpaleyeThConfig

  makeOpaleyeModels (connectInfo, options)
  makeAdaptorAndInstances (connectInfo, options)
  makeOpaleyeTables (connectInfo, options)

```

The arguments to the functions are the postgresqlSimple's connectInfo and options which is of type

```
data Options = Options { tableOptions :: [(String, TableOptions)] }
```

The first element of tuple is the table name and TableOptions is defined as 

```
data TableOptions = TableOptions { modelName :: String, overrideDefaultTypes :: [(String, String)], protectedFields :: [String] }
```

The `modelName` is the name of the Haskell type of this table.

The `overrideDefaultTypes` field lists fields that should be mapped to a custom datatype, and is a tuple of format (db_column_name, newtype_name)

The `protectedFields` field is used to denote fields that should only get getters, when generating lenses.

A sample OpaleyeTHConfig.hs file

```
import Opaleye.TH
import Database.PostgreSQL.Simple

options = Options [
   ("users", usersOptions),   
   ("products", productsOptions)
  ]

usersOptions = TableOptions {
  modelName = "User",
  overrideDefaultTypes = [
    ("key", "UserId"),
    ("email", "Email")
  ],
  protectedFields = ["email"]
}

productsOptions = TableOptions {
  modelName = "Product",
  overrideDefaultTypes = [
    ("key", "ProductId"),
    ("user_id", "UserId")
  ],
  protectedFields = []
}

connectInfo = defaultConnectInfo { connectPassword = "postgres", connectDatabase = "scratch"}    

```    

