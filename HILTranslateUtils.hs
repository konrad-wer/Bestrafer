{-# LANGUAGE TemplateHaskell #-}

module HILTranslateUtils where

import AST
import CommonUtils
import Control.Lens hiding (op)
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set

type ConstructorsArities = Map.Map String Int

data TranslateState = TranslateState
  {
    _freshVarNum :: Int,
    _constrArities :: ConstructorsArities
  }

makeLenses ''TranslateState

prefixSourceVariables :: Expr p -> Expr p
prefixSourceVariables (EVar    p x) = EVar p ("s_" ++ x)
prefixSourceVariables e@EUnit   {} = e
prefixSourceVariables e@EBool   {} = e
prefixSourceVariables e@EInt    {} = e
prefixSourceVariables e@EFloat  {} = e
prefixSourceVariables e@EChar   {} = e
prefixSourceVariables e@EString {} = e
prefixSourceVariables (ELambda p x e) = ELambda p ("s_" ++ x) $ prefixSourceVariables e
prefixSourceVariables (ESpine  p e s) = ESpine p (prefixSourceVariables e) (prefixSourceVariables <$> s)
prefixSourceVariables (EDef    p f e) = EDef p ("s_" ++ f) $ prefixSourceVariables e
prefixSourceVariables (EAnnot  p e t) = EAnnot p (prefixSourceVariables e) t
prefixSourceVariables (ETuple  p es n) = ETuple p (prefixSourceVariables <$> es) n
prefixSourceVariables (EConstr p c args) = EConstr p c $ prefixSourceVariables <$> args
prefixSourceVariables (ECase   p es bs) = ECase p (prefixSourceVariables <$> es) (prefixSourceVariablesInBranch <$> bs)
prefixSourceVariables (EIf     p e1 e2 e3) =
  EIf p (prefixSourceVariables e1) (prefixSourceVariables e2) (prefixSourceVariables e3)
prefixSourceVariables (ELet    p x e1 e2) = ELet p ("s_" ++ x) (prefixSourceVariables e1) (prefixSourceVariables e2)
prefixSourceVariables (ERec    p t x e1 e2) = ERec p t ("s_" ++ x) (prefixSourceVariables e1) (prefixSourceVariables e2)
prefixSourceVariables (EBinOp  p op e1 e2) = EBinOp p op (prefixSourceVariables e1) (prefixSourceVariables e2)
prefixSourceVariables (EUnOp   p op e) = EUnOp p op $ prefixSourceVariables e
prefixSourceVariables (ETry    p e cs) = ETry p (prefixSourceVariables e) $ prefixSourceVariablesInCatch <$> cs
prefixSourceVariables (EError  p e) = EError p $ prefixSourceVariables e

prefixSourceVariablesInBranch :: Branch p -> Branch p
prefixSourceVariablesInBranch (ptrns, e, p) =
  (prefixSourceVariablesInPattern <$> ptrns, prefixSourceVariables e, p)

prefixSourceVariablesInPattern :: Pattern p -> Pattern p
prefixSourceVariablesInPattern (PVar    p x) = PVar p ("s_" ++ x)
prefixSourceVariablesInPattern (PTuple  p ptrns n) = PTuple p (prefixSourceVariablesInPattern <$> ptrns) n
prefixSourceVariablesInPattern ptrn@PWild   {} = ptrn
prefixSourceVariablesInPattern ptrn@PUnit   {} = ptrn
prefixSourceVariablesInPattern ptrn@PBool   {} = ptrn
prefixSourceVariablesInPattern ptrn@PInt    {} = ptrn
prefixSourceVariablesInPattern ptrn@PFloat  {} = ptrn
prefixSourceVariablesInPattern ptrn@PChar   {} = ptrn
prefixSourceVariablesInPattern ptrn@PString {} = ptrn
prefixSourceVariablesInPattern (PConstr p c args) = PConstr p c $ prefixSourceVariablesInPattern <$> args

prefixSourceVariablesInCatch :: Catch p -> Catch p
prefixSourceVariablesInCatch (BestraferException p exc Nothing, e) =
  (BestraferException p exc Nothing, prefixSourceVariables e)
prefixSourceVariablesInCatch (BestraferException p exc (Just x), e) =
  (BestraferException p exc (Just ("s_" ++ x)), prefixSourceVariables e)

freshVar :: State TranslateState Var
freshVar = do
  n <- view freshVarNum <$> get
  modify $ over freshVarNum (+ 1)
  return $ ("g_" ++) $ show n

uniquifyVariable :: Var -> State TranslateState Var
uniquifyVariable x = do
  n <- view freshVarNum <$> get
  modify $ over freshVarNum (+ 1)
  return $ (++ x) . ("let_" ++) $ show n

data TranslateContextEntry = Captured Int | Self
type TranslateContext = Map.Map Var TranslateContextEntry

alfaConvert :: Var -> Var -> Expr p -> Expr p
alfaConvert x y e@(EVar p z)
  | x == z = EVar p y
  | otherwise = e
alfaConvert _ _  e@EUnit   {} = e
alfaConvert _ _  e@EBool   {} = e
alfaConvert _ _  e@EInt    {} = e
alfaConvert _ _  e@EFloat  {} = e
alfaConvert _ _  e@EChar   {} = e
alfaConvert _ _  e@EString {} = e
alfaConvert x y e@(ELambda p z body)
  | x == z = e
  | otherwise = ELambda p z $ alfaConvert x y body
alfaConvert x y (ESpine p e es) = ESpine p (alfaConvert x y e) (alfaConvert x y <$> es)
alfaConvert x y e@(EDef p z body)
  | x == z = e
  | otherwise = EDef p z $ alfaConvert x y body
alfaConvert x y e@(ERec p t z e1 e2)
  | x == z = e
  | otherwise = ERec p t z (alfaConvert x y e1) (alfaConvert x y e2)
alfaConvert x y (EAnnot p e t) = EAnnot p (alfaConvert x y e) t
alfaConvert x y (ETuple p es n) = ETuple p (alfaConvert x y <$> es) n
alfaConvert x y (EConstr p constr es) = EConstr p constr $ alfaConvert x y <$> es
alfaConvert x y (ECase p es branches) = ECase p (alfaConvert x y <$> es) (alfaConvertBranch x y <$> branches)
alfaConvert x y (EIf p e1 e2 e3) = EIf p (alfaConvert x y e1) (alfaConvert x y e2) (alfaConvert x y e3)
alfaConvert x y (ELet p z e1 e2)
  | x == z = ELet p z (alfaConvert x y e1) e2
  | otherwise = ELet p z (alfaConvert x y e1) (alfaConvert x y e2)
alfaConvert x y (EBinOp p binOp e1 e2) = EBinOp p binOp (alfaConvert x y e1) (alfaConvert x y e2)
alfaConvert x y (EUnOp p unOp e) = EUnOp p unOp $ alfaConvert x y e
alfaConvert x y (ETry p e catches) = ETry p (alfaConvert x y e) (alfaConvertCatch x y <$> catches)
alfaConvert x y (EError p e) = EError p $ alfaConvert x y e

alfaConvertBranch ::  Var -> Var -> Branch p -> Branch p
alfaConvertBranch x y b@(ptrn, e, p)
  | or $ isVarInPattern x <$> ptrn = b
  | otherwise = (ptrn, alfaConvert x y e, p)

alfaConvertCatch ::  Var -> Var -> Catch p -> Catch p
alfaConvertCatch x y (exc@(BestraferException _ _ Nothing), e) = (exc, alfaConvert x y e)
alfaConvertCatch x y catch@(exc@(BestraferException _ _ (Just z)), e)
  | x == z = catch
  | otherwise = (exc, alfaConvert x y e)

getGlobalNames :: Program p -> Set.Set Var
getGlobalNames [] = Set.empty
getGlobalNames (EDef _ name _ : defs) = name `Set.insert` getGlobalNames defs
getGlobalNames ( _ : defs) = getGlobalNames defs
