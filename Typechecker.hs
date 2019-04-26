module Typechecker where

import AST
import TypecheckerUtils
import qualified Data.Set as Set

checkTypeWellFormednessWithPrnc :: Context -> Type -> Principality -> p -> Either (Error p) ()
checkTypeWellFormednessWithPrnc c t NotPrincipal p = checkTypeWellFormedness c t p
checkTypeWellFormednessWithPrnc c t Principal p =
  case Set.toList . freeExistentialVariables $ t of
    [] -> checkTypeWellFormedness c t p
    vars -> Left $ TypeFormednessPrcFEVError p vars

checkTypeWellFormedness :: Context -> Type -> p -> Either (Error p) ()
checkTypeWellFormedness _ TUnit _ = return ()
checkTypeWellFormedness c (TArrow t1 t2) p = checkTypeWellFormedness c t1 p >> checkTypeWellFormedness c t2 p
checkTypeWellFormedness c (TCoproduct t1 t2) p = checkTypeWellFormedness c t1 p >> checkTypeWellFormedness c t2 p
checkTypeWellFormedness c (TProduct t1 t2) p = checkTypeWellFormedness c t1 p >> checkTypeWellFormedness c t2 p
checkTypeWellFormedness c (TImp pr t) p = checkPropWellFormedness c pr p >> checkTypeWellFormedness c t p
checkTypeWellFormedness c (TAnd t pr) p = checkTypeWellFormedness c t p >> checkPropWellFormedness c pr p
checkTypeWellFormedness c (TUniversal x k t) p = checkTypeWellFormedness (CTypeVar (U $ UTypeVar x) k : c) t p
checkTypeWellFormedness c (TExistential x k t) p = checkTypeWellFormedness (CTypeVar (E $ ETypeVar x) k : c) t p
checkTypeWellFormedness c (TVec n t) p = checkMonotypeHasKind c n p KNat >> checkTypeWellFormedness c t p
checkTypeWellFormedness c (TEVar x) p =
  case eTypeVarContextLookup c x of
    Just (CTypeVar _ KStar) -> return ()
    Just (CETypeVar _ KStar _) -> return ()
    Just (CTypeVar _ KNat) -> Left $ TypeHasWrongKindError p (TEVar x) KStar KNat
    Just (CETypeVar _ KNat _) -> Left $ TypeHasWrongKindError p (TEVar x) KStar KNat
    Nothing -> Left $ UndeclaredETypeVarError p x
    _ -> Left $ InternalCompilerError p "eTypeVarContextLookup"
checkTypeWellFormedness c (TUVar x) p =
  case unsolvedTypeVarContextLookup c (U x) of
    Just (CTypeVar _ KStar) -> return ()
    Just (CTypeVar _ KNat) -> Left $ TypeHasWrongKindError p (TUVar x) KStar KNat
    Nothing -> Left $ UndeclaredUTypeVarError p x
    _ -> Left $ InternalCompilerError p "checkTypeWellFormedness"

checkMonotypeHasKind :: Context -> Monotype -> p -> Kind -> Either (Error p) ()
checkMonotypeHasKind c m p k1 = do
  k2 <- inferMonotypeKind c m p
  if k1 == k2 then
    return ()
  else
    Left $ MonotypeHasWrongKindError p m k1 k2

inferMonotypeKind :: Context -> Monotype -> p -> Either (Error p) Kind
inferMonotypeKind _ MUnit _ = return KStar
inferMonotypeKind _ MZero _ = return KNat
inferMonotypeKind c (MSucc n) p = checkMonotypeHasKind c n p KNat >> return KNat
inferMonotypeKind c (MArrow m1 m2) p = checkMonotypeHasKind c m1 p KStar >> checkMonotypeHasKind c m2 p KStar >> return KStar
inferMonotypeKind c (MCoproduct m1 m2) p = checkMonotypeHasKind c m1 p KStar >> checkMonotypeHasKind c m2 p KStar >> return KStar
inferMonotypeKind c (MProduct m1 m2) p = checkMonotypeHasKind c m1 p KStar >> checkMonotypeHasKind c m2 p KStar >> return KStar
inferMonotypeKind c (MEVar x) p =
  case eTypeVarContextLookup c x of
    Just (CTypeVar _ k) -> return k
    Just (CETypeVar _ k _) -> return k
    _ ->  Left $ UndeclaredETypeVarError p x
inferMonotypeKind c (MUVar x) p =
  case unsolvedTypeVarContextLookup c (U x) of
    Just (CTypeVar _ k) -> return k
    _ -> Left $ UndeclaredUTypeVarError p x

checkPropWellFormedness :: Context -> Proposition -> p -> Either (Error p) ()
checkPropWellFormedness c (m1, m2) p = inferMonotypeKind c m1 p >>= checkMonotypeHasKind c m2 p

subtype :: Context -> Type -> Polarity -> Type -> p -> Either (Error p) Context
subtype c t1 pol t2 p
  | not (headedByUniversal t1) && not (headedByExistential t1) &&
    not (headedByUniversal t2) && not (headedByExistential t2) = equivalentType c t1 t2 p
  | headedByUniversal t1 && not (headedByUniversal t2) && neg pol = undefined
  | headedByUniversal t2 && neg pol = undefined
  | headedByExistential t1 && pos pol = undefined
  | not (headedByExistential t1) && headedByExistential t2 && pos pol = undefined
  | pos pol && (neg . polarity $ t1) && (nonpos . polarity $ t2) = subtype c t1 Negative t2 p
  | pos pol && (nonpos . polarity $ t1) && (neg . polarity $ t2) = subtype c t1 Negative t2 p
  | neg pol && (pos . polarity $ t1) && (nonneg . polarity $ t2) = subtype c t1 Positive t2 p
  | neg pol && (nonneg . polarity $ t1) && (pos . polarity $ t2) = subtype c t1 Positive t2 p
  | otherwise = undefined

equivalentType :: Context -> Type -> Type -> p -> Either (Error p) Context
equivalentType = undefined

checkExpr :: Context -> Expr p -> Type -> Principality -> Either (Error p) Context
checkExpr c (EUnit _) TUnit _ = return c
checkExpr c (EUnit p) (TEVar a) _ = eTypeVarContextReplace c a MUnit [] p
checkExpr c (ELambda _ x e) (TArrow t1 t2) pr = do
  c2 <- checkExpr (CVar x t1 pr : CMarker : c) e t2 pr
  return $ dropContextToMarker c2
checkExpr c (ELambda p x e) (TEVar a) _ =
  let a1 = ETypeVar $ eTypeVarName a ++ "-1" in
  let a2 = ETypeVar $ eTypeVarName a ++ "-2" in do
  c2 <- eTypeVarContextReplace c a (MArrow (MEVar a1) (MEVar a2)) [CTypeVar (E a1) KStar, CTypeVar (E a2) KStar] p
  c3 <- checkExpr (CVar x (TEVar a1) NotPrincipal : CMarker : c2) e (TEVar a2) NotPrincipal
  return $ dropContextToMarker c3
checkExpr c (EPair _ e1 e2) (TProduct t1 t2) pr = do
  c2 <- checkExpr c e1 t1 pr
  checkExpr c2 e2 t2 pr
checkExpr c (EPair p e1 e2) (TEVar a) _ =
  let a1 = ETypeVar $ eTypeVarName a ++ "-1" in
  let a2 = ETypeVar $ eTypeVarName a ++ "-2" in do
  c2 <- eTypeVarContextReplace c a (MProduct (MEVar a1) (MEVar a2)) [CTypeVar (E a1) KStar, CTypeVar (E a2) KStar] p
  c3 <- checkExpr c2 e1 (TEVar a1) NotPrincipal
  checkExpr c3 e2 (TEVar a2) NotPrincipal
checkExpr c (EInjk _ e k) (TCoproduct t1 t2) pr = checkExpr c e ([t1, t2] !! k) pr
checkExpr c (EInjk p e k) (TEVar a) _ =
  let a1 = ETypeVar $ eTypeVarName a ++ "-1" in
  let a2 = ETypeVar $ eTypeVarName a ++ "-2" in do
  c2 <- eTypeVarContextReplace c a (MCoproduct (MEVar a1) (MEVar a2)) [CTypeVar (E a1) KStar, CTypeVar (E a2) KStar] p
  checkExpr c2 e ([TEVar a1, TEVar a2] !! k) NotPrincipal
checkExpr _ _ _ _ = undefined

inferExpr :: Context -> Expr p -> Either (Error p) (Type, Principality, Context)
inferExpr c (EVar p x) = do
  (CVar _ t pr) <- varContextLookup c x p
  t2 <- applyContextToType c t p
  return (t2, pr, c)
inferExpr c (EAnnot p e t) = do
  checkTypeWellFormednessWithPrnc c t Principal p
  t2 <- applyContextToType c t p
  c2 <- checkExpr c e t2 Principal
  return (t2, Principal, c2)
inferExpr _ _ = undefined
