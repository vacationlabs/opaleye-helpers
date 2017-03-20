{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings  #-}

module Opaleye.TH.Transformations (transform) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Opaleye.TH.Data
import Data.Char
import Data.Maybe

transform :: Name -> TypeName -> [Transformation] -> Q [Dec]
transform name targetName transformation = do
  info <- reify name
  case info of
    TyConI (TySynD _ [] typeTree) ->
      let 
        recordName = getRecordName typeTree
        recordArgs = getTypeArgs typeTree
        in do
          TyConI datad <- reify recordName
          (r, newToOld, a) <- getTransformerFunctions datad recordArgs transformation targetName
          let rs = (\(FieldName a', b, c) -> (mkName a', (b, c))) <$> a
          return [r, mlTr newToOld r datad recordArgs rs, mrTl transformation ((\(a', b)-> (b,a')) <$> newToOld) r datad rs]
    _ -> error "Require a type synonym"
    where
      mlTr :: [(Name, Maybe FieldName)] -> Dec -> Dec -> [Type] -> [(Name, (Dec, Dec))] -> Dec
      mlTr 
        newToOld
        (DataD [] _ [] Nothing [RecC tConName newFields] _)
        (datad@(DataD [] _ _ _ [RecC conName _] _))
        typeargs l = FunD (mkName "mltr") [Clause  [ptrn] (NormalB exp') allFunctions]
          where
            allFunctions = fmap (\(_, (a, _)) -> a) l
            fieldNameAndTypes = getFieldNamesAndTypes datad typeargs
            indexedFieldNames :: [(FieldName, Int)]
            indexedFieldNames = zip (fst <$> fieldNameAndTypes) [1..]
            ptrn = AsP (mkName "x") $ ConP conName (fmap (\(_, a) -> VarP $ mkName ("a" ++ (show a))) $ indexedFieldNames)
            exp' = foldl AppE (ConE tConName) (mkExp <$> newFields)
              where
                mkExp :: (Name, Bang, Type) -> Exp
                mkExp (name', _, _) = case lookup name' l of
                  Just (FunD n _, _) -> AppE (VarE n) (VarE $ mkName "x")
                  Just _ -> error "Unexpected varbangtype"
                  Nothing -> case lookup name' newToOld of
                    Just (Just colname) -> case lookup colname indexedFieldNames of
                      Just index -> VarE $ mkName ("a" ++ show index)
                      _ -> error "Cannot find old field name for transformed record field"
                    _ -> error "Cannot find old field name for transformed record field"
      mlTr _ _ _ _ _ = error "Unexpected patterns" 
      mrTl :: [Transformation] -> [(Maybe FieldName, Name)] -> Dec -> Dec -> [(Name, (Dec, Dec))] -> Dec
      mrTl
        transformations
        oldToNew
        (DataD [] _ [] Nothing [RecC tConName newFields] _)
        (DataD [] _ _ _ [RecC conName rightFields] _)
        l
        =
        FunD (mkName "mrtl") [Clause  [ptrn] (NormalB exp') allFunctions]
          where
            indexedFieldNames :: [(FieldName, Int)]
            indexedFieldNames = zip ((\(a, _, _) -> FieldName $ nameBase a) <$> newFields) [1..]
            ptrn = AsP (mkName "x") $ ConP tConName (fmap (\(_, a) -> VarP $ mkName ("a" ++ (show a))) $ indexedFieldNames)
            exp' = foldl AppE (ConE conName) (mkExp <$> rightFields)
              where
                indexTuplePatterns = foldl indexTuplePattern [] transformations
                indexTuplePattern :: [(FieldName, String)] -> Transformation -> [(FieldName, String)]
                indexTuplePattern ll (Transformation {targetField = FieldName tf, sourceFields = sf}) =
                  let
                    sourceVars :: [(FieldName, String)]
                    sourceVars = zip sf $ fmap (\(_, b) -> tf ++ (show b)) $ zip (replicate (length sf) tf) ([1..] :: [Int]) 
                    in ll ++ sourceVars
                mkExp :: (Name, Bang, Type) -> Exp
                mkExp (nameBase -> name', _, _) = case lookup (Just $ FieldName $ name') oldToNew of
                  Just (nameBase -> newName') -> case lookup (FieldName $ newName') indexedFieldNames of
                    Just index -> VarE $ mkName ("a" ++ show index)
                    _ -> error "error"
                  Nothing -> case lookup (FieldName $ nameBase name) indexTuplePatterns of
                    Just argName -> VarE $ mkName argName
                    _ -> error "error"
            allFunctions = (fmap (\(_, (_, b)) -> b) l) ++ (makeExtractionFunctions transformations)
            makeExtractionFunctions :: [Transformation] -> [Dec]
            makeExtractionFunctions xs = (makeTransformationFunction' "asd") <$> xs
              where
                makeTransformationFunction' :: String -> Transformation -> Dec
                makeTransformationFunction' _ (Transformation { targetField = FieldName tf, sourceFields = sf })
                  = ValD ptrn' (NormalB $ AppE (VarE mkFn) (VarE $ mkName "x")) []
                  where
                    mkTupeCon = "(" ++ (replicate (length sf -1) ',') ++ ")"
                    ptrn' = ConP (mkName $ mkTupeCon) (((VarP).mkName) <$> tfCounted)
                    tfCounted = (\(a, b) -> (a ++ (show b))) <$> zip (replicate (length sf) tf) ([1..] :: [Int])
                    mkFn :: Name
                    mkFn = (mkName $ tf ++ "RtL")
      mrTl _ _ _ _ _ = error "Unexpected pattern"

-- returns innermost ConT
getRecordName :: Type -> Name
getRecordName (AppT (ConT n) _) = n
getRecordName (AppT a _) = getRecordName a
getRecordName _ = error "Expecting an AppT"

-- returns type arguments to Constructor
getTypeArgs :: Type -> [Type]
getTypeArgs = reverse.getTypeArgs'
  where
  getTypeArgs' :: Type -> [Type]
  getTypeArgs' (ConT _) =  []
  getTypeArgs' (AppT a b) =  (b:getTypeArgs' a)
  getTypeArgs' _ = error "Expecting a type constructor or AppT"

getTransformerFunctions :: Dec -> [Type] -> [Transformation] -> TypeName -> Q (Dec, [(Name, Maybe FieldName)], [(FieldName, Dec, Dec)])
getTransformerFunctions dec@(DataD [] _ _ Nothing [RecC conName _] _) args transformation (TypeName target) = do
      let
        fieldsAndType = getFieldNamesAndTypes dec args
        newFields = makeRecordFields fieldsAndType ("_" ++ (nameBase conName)) ("_" ++ (lcFirst target)) transformation
        newFieldsWithoutMapping = fst <$> newFields
        newFieldsMapping = (\((a, _, _), d) -> (a, d)) <$> newFields
        targetRecordD = DataD [] (mkName target) [] Nothing [RecC (mkName target) newFieldsWithoutMapping] [ConT ''Show] 
      return $ (targetRecordD, newFieldsMapping, (makeTransformationFunction conName fieldsAndType newFieldsWithoutMapping (mkName target)) <$> transformation)
getTransformerFunctions _ _ _ _ = error "Require a type constructor"

makeTransformationFunction :: Name -> [(FieldName, Type)] -> [VarBangType] -> Name -> Transformation -> (FieldName, Dec, Dec)
makeTransformationFunction
  sourceName
  fieldsAndTypes
  newFields
  targetName 
  (Transformation targetField@(FieldName targetFieldName) _ sourceFields sourcesToTarget targetTosources _ _)  = (targetField, makeLtR, makeRtL)
    where
      makeLtR :: Dec
      makeLtR = let
        validate = and $ isPresent <$> sourceFields
          where
            isPresent :: FieldName -> Bool
            isPresent cn = if isNothing $ lookup cn fieldsAndTypes then error $ "One of the src fields, " ++ (show cn) ++ " was not found. Available fields are " ++ (show fieldsAndTypes) else True
        (pat, expl) = if validate then (foldl makePatternAndExp ([], []) $ zip fieldsAndTypes [1..]) else (error $ "One of the source fields in " ++ (show sourceFields) ++ " could not be found")
        fullExp = foldl AppE (VarE sourcesToTarget) $ sortAndExtractExp expl
          where
            sortAndExtractExp :: [(FieldName, Exp)] -> [Exp]
            sortAndExtractExp ls = fmap expForCol sourceFields
              where
              expForCol :: FieldName -> Exp
              expForCol cn = case (lookup cn ls) of
                Just exp' -> exp'
                _ -> error "Cannot find exp for column"
        ptrn = ConP sourceName $ reverse pat
        in FunD (mkName (targetFieldName ++ "LtR")) [Clause [ptrn] (NormalB fullExp) []]
          where
          makeVarName :: Int -> Name
          makeVarName index = mkName ("a" ++ show index)
          makePatternAndExp :: ([Pat], [(FieldName, Exp)]) -> ((FieldName, Type), Int) -> ([Pat], [(FieldName, Exp)])
          makePatternAndExp (pl, exp')((cn, _), index) = let
            tr = (cn `elem` sourceFields)
            p = if tr then VarP $ makeVarName index  else WildP
            x = if tr then (cn, VarE $ makeVarName index):exp' else exp'
            in (p:pl, x)
      makeRtL :: Dec
      makeRtL = let
        ptrn = foldl makePattern [] newFields 
        in FunD (mkName (targetFieldName ++ "RtL")) [Clause [ConP targetName (reverse ptrn)] (NormalB $ AppE (VarE targetTosources) (VarE $ mkName "x")) []]
          where
          makePattern :: [Pat] -> (Name, Bang, Type) -> [Pat]
          makePattern pl (name, _, _) = let p = if (targetFieldName == (nameBase name)) then (VarP $ mkName "x") else WildP in (p:pl)
    
makeRecordFields :: [(FieldName, Type)] -> String -> String -> [Transformation] -> [(VarBangType, Maybe FieldName)]
makeRecordFields fieldsAndTypes rmPrifix addPrx transformations = let
  fieldsRemoved = foldl removeFields fieldsAndTypes transformations
  fieldsWithOldMapping = (\(a, b) -> (a, b, Just a)) <$> fieldsRemoved
  prefixRemoved = addPrefix <$> (removePrefix <$> fieldsWithOldMapping)
  fieldsAdded = prefixRemoved  ++ (makeNewFields transformations)
  in makeVarBangTypes fieldsAdded
  where
    removePrefix :: (FieldName, Type, Maybe FieldName) -> (FieldName, Type, Maybe FieldName)
    removePrefix (FieldName cn, t, x) = (FieldName (drop (length rmPrifix) cn), t, x)
    addPrefix :: (FieldName, Type, Maybe FieldName) -> (FieldName, Type, Maybe FieldName)
    addPrefix (FieldName cn, t, x) = (FieldName (addPrx ++ cn), t, x)
    makeVarBangTypes :: [(FieldName, Type, Maybe FieldName)] -> [(VarBangType, Maybe FieldName)]
    makeVarBangTypes l = makeVarBangType <$> l
      where
        makeVarBangType :: (FieldName, Type, Maybe FieldName) -> (VarBangType, Maybe FieldName)
        makeVarBangType (FieldName c, t, x) = ((mkName c, Bang NoSourceUnpackedness NoSourceStrictness, t), x)
    makeNewFields :: [Transformation] -> [(FieldName, Type, Maybe FieldName)]
    makeNewFields l = (\Transformation {targetField = tf, targetType = TypeName tn} -> (tf, ConT $ mkName tn, Nothing)) <$> l
    removeFields :: [(FieldName, Type)] -> Transformation -> [(FieldName, Type)]
    removeFields f (Transformation {sourceFields = sf, includeSources = False }) =
      if (and $ validate <$> sf) then filter (\(c, _)-> not $ c `elem` sf) f else error $ "One of the source fields in " ++ show sf ++ " was not found"
      where
        validate src_f = if isNothing $ lookup src_f fieldsAndTypes 
                           then error $ "Source field " ++ (show src_f) ++ " was not found. Available fields are, " ++ (show $ fst <$> fieldsAndTypes) 
                           else True
    removeFields f _  = f

getFieldNamesAndTypes :: Dec -> [Type] -> [(FieldName, Type)]
getFieldNamesAndTypes cons args = case cons of
  DataD [] _ argvs Nothing [RecC _ fieldTypes] _ -> 
    let
      fls = makeFieldNamesAndTypes fieldTypes argvals
      argvals = zip (extractTVName <$> argvs) args
      in fls
  _ -> error "Require a record definition"
  where
    extractTVName :: TyVarBndr -> Name
    extractTVName (KindedTV name _) = name
    extractTVName _ = error "Expecting a KindedTv"
    makeFieldNamesAndTypes :: [VarBangType] -> [(Name, Type)] -> [(FieldName, Type)]
    makeFieldNamesAndTypes vt argl = makeTuple <$> vt
      where
        makeTuple :: VarBangType -> (FieldName, Type)
        makeTuple (fieldName, _, typ@(ConT _)) = (FieldName $ nameBase fieldName, typ)
        makeTuple (fieldName, _, VarT vn) = case lookup vn argl of
          Just t -> (FieldName $ nameBase fieldName, t)
          Nothing -> error "Cannot find matching type for type"
        makeTuple _ = error "Unexpected patterns"

lcFirst :: String -> String
lcFirst [] = []
lcFirst (x:xs) = (toLower x):xs
