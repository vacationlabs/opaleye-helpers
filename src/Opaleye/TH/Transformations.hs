{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings  #-}

module Opaleye.TH.Transformations where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Opaleye.TH.Data
import Debug.Trace

transform :: Name -> [Transformation] -> Q Dec
transform name transformation = do
  info <- reify name
  case info of
    TyConI (TySynD _ [] typeTree) ->
      let 
        recordName = getRecordName typeTree
        recordArgs = getTypeArgs typeTree
        in transformType recordName recordArgs transformation
    _ -> error "Require a type synonym"

-- returns innermost ConT
getRecordName :: Type -> Name
getRecordName (AppT (ConT n) _) = n
getRecordName (AppT a _) = getRecordName a

-- returns type arguments to Constructor
getTypeArgs :: Type -> [Type]
getTypeArgs = reverse.getTypeArgs'
  where
  getTypeArgs' :: Type -> [Type]
  getTypeArgs' (ConT n) =  []
  getTypeArgs' (AppT a b) =  (b:getTypeArgs a)

transformType :: Name -> [Type] -> [Transformation] -> Q Dec
transformType recName args transformation = do
  info <- reify recName
  case info of
    TyConI dec -> do
      let fieldsAndType = getFieldNamesAndTypes dec args
      trace (show fieldsAndType) $ return ()
      return $ FunD (mkName "l") []
    _ -> error "Require a type constructor"

getFieldNamesAndTypes :: Dec -> [Type] -> [(Name, Type)]
getFieldNamesAndTypes cons args = case cons of
  DataD [] _ argvs Nothing [RecC _ fieldTypes] [] -> 
    let argvals = zip (extractTVName <$> argvs) args in makeFieldNamesAndTypes fieldTypes argvals
  _ -> error "Require a record definition"
  where
    extractTVName :: TyVarBndr -> Name
    extractTVName (KindedTV name _) = name
    makeFieldNamesAndTypes :: [VarBangType] -> [(Name, Type)] -> [(Name, Type)]
    makeFieldNamesAndTypes vt argl = makeTuple <$> vt
      where
        makeTuple :: VarBangType -> (Name, Type)
        makeTuple (fieldName, _, typ@(ConT _)) = (fieldName, typ)
        makeTuple (fieldName, _, VarT vn) = case lookup vn argl of
          Just t -> (fieldName, t)
          Nothing -> error "Cannot find matching type for type"
