{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings  #-}

module Opaleye.TH.Transformations (transform) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Opaleye.TH.Data
import Data.Char
import Debug.Trace

--transform :: Name -> TypeName -> [Transformation] -> Q (Dec, Dec, Dec)
transform :: Name -> TypeName -> [Transformation] -> Q [Dec]
transform name targetName transformation = do
  info <- reify name
  case info of
    TyConI (TySynD _ [] typeTree) ->
      let 
        recordName = getRecordName typeTree
        recordArgs = getTypeArgs typeTree
        in do
          (r, rs) <- getTransformerFunctions recordName recordArgs transformation targetName
          return $ [r] ++ concatMap (\(a, b, c) -> [b, c]) rs
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
  getTypeArgs' (AppT a b) =  (b:getTypeArgs' a)

getTransformerFunctions :: Name -> [Type] -> [Transformation] -> TypeName -> Q (Dec, [(ColumnName, Dec, Dec)])
getTransformerFunctions recName args transformation (TypeName target) = do
  info <- reify recName
  case info of
    TyConI dec@(DataD [] _ _ Nothing [RecC conName fieldTypes] []) -> do
      let
        fieldsAndType = getFieldNamesAndTypes dec args
        newFields = makeRecordFields fieldsAndType ("_" ++ (nameBase conName)) ("_" ++ (lcFirst target)) transformation
        targetRecordD = DataD [] (mkName target) [] Nothing [RecC (mkName target) newFields] [] 
      return $ (targetRecordD, (makeTransformationFunction conName fieldsAndType newFields (mkName target)) <$> transformation)
    _ -> error "Require a type constructor"

emptyFunc = FunD (mkName "s") [Clause [] (NormalB $ LitE $ IntegerL 3) []]

makeTransformationFunction :: Name -> [(ColumnName, Type)] -> [(Name, Bang, Type)] -> Name -> Transformation -> (ColumnName, Dec, Dec)
makeTransformationFunction
  sourceName
  fieldsAndTypes
  newFields
  targetName 
  (Transformation targetField@(ColumnName targetFieldName) targetType sourceFields sourcesToTarget targetTosources _)  = (targetField, makeLtR, makeRtL)
    where
      makeLtR :: Dec
      makeLtR = let
        (pat, exp) = foldl makePatternAndExp ([], VarE sourcesToTarget) $ zip fieldsAndTypes [1..]
        pattern = ConP sourceName $ reverse pat
        in FunD (mkName (targetFieldName ++ "LtR")) [Clause [pattern] (NormalB exp) []]
          where
          makeVarName :: Int -> Name
          makeVarName index = mkName ("a" ++ show index)
          makePatternAndExp :: ([Pat], Exp) -> ((ColumnName, Type), Int) -> ([Pat], Exp)
          makePatternAndExp (pl, exp)((cn, t), index) = let
            tr = (cn `elem` sourceFields)
            p = if tr then VarP $ makeVarName index  else WildP
            x = if tr then AppE exp (VarE $ makeVarName index) else exp
            in (p:pl, x)
      makeRtL :: Dec
      makeRtL = let
        pattern = foldl makePattern [] newFields 
        in FunD (mkName (targetFieldName ++ "RtL")) [Clause [ConP targetName pattern] (NormalB $ AppE (VarE targetTosources) (VarE $ mkName "x")) []]
          where
          makePattern :: [Pat] -> (Name, Bang, Type) -> [Pat]
          makePattern pl (name, _, _) = let p = if (targetFieldName == (nameBase name)) then (VarP $ mkName "x") else WildP in (p:pl)
    
makeRecordFields :: [(ColumnName, Type)] -> String -> String -> [Transformation] -> [VarBangType]
makeRecordFields fieldsAndTypes rmPrifix addPrx transformations = let
  fieldsRemoved = foldl removeFields fieldsAndTypes transformations
  prefixRemoved = addPrefix <$> (removePrefix <$> fieldsRemoved)
  fieldsAdded = foldl addFields prefixRemoved transformations
  in makeVarBangTypes fieldsAdded
  where
    removePrefix :: (ColumnName, Type) -> (ColumnName, Type)
    removePrefix (ColumnName cn, t) = (ColumnName (drop (length rmPrifix) cn), t)
    addPrefix :: (ColumnName, Type) -> (ColumnName, Type)
    addPrefix (ColumnName cn, t) = (ColumnName (addPrx ++ cn), t)
    makeVarBangTypes :: [(ColumnName, Type)] -> [VarBangType]
    makeVarBangTypes l = makeVarBangType <$> l
      where
        makeVarBangType :: (ColumnName, Type) -> VarBangType
        makeVarBangType (ColumnName c, t) = (mkName c, Bang NoSourceUnpackedness NoSourceStrictness, t)
    addFields :: [(ColumnName, Type)] -> Transformation -> [(ColumnName, Type)]
    addFields l (Transformation {targetField = tf, targetType = TypeName tn}) = (tf, ConT $ mkName tn):l
    removeFields :: [(ColumnName, Type)] -> Transformation -> [(ColumnName, Type)]
    removeFields fieldsAndTypes (Transformation {sourceFields = sf, includeSources = False }) =
      filter (\(c, _)-> not $ c `elem` sf) fieldsAndTypes
    removeFields fieldsAndTypes _  = fieldsAndTypes

getFieldNamesAndTypes :: Dec -> [Type] -> [(ColumnName, Type)]
getFieldNamesAndTypes cons args = case cons of
  DataD [] recName argvs Nothing [RecC _ fieldTypes] [] -> 
    let
      fls = makeFieldNamesAndTypes fieldTypes argvals
      argvals = zip (extractTVName <$> argvs) args
      in fls
  _ -> error "Require a record definition"
  where
    extractTVName :: TyVarBndr -> Name
    extractTVName (KindedTV name _) = name
    makeFieldNamesAndTypes :: [VarBangType] -> [(Name, Type)] -> [(ColumnName, Type)]
    makeFieldNamesAndTypes vt argl = makeTuple <$> vt
      where
        makeTuple :: VarBangType -> (ColumnName, Type)
        makeTuple (fieldName, _, typ@(ConT _)) = (ColumnName $ nameBase fieldName, typ)
        makeTuple (fieldName, _, VarT vn) = case lookup vn argl of
          Just t -> (ColumnName $ nameBase fieldName, t)
          Nothing -> error "Cannot find matching type for type"

lcFirst :: String -> String
lcFirst (x:xs) = (toLower x):xs
ucFirst :: String -> String
ucFirst (x:xs) = (toUpper x):xs
