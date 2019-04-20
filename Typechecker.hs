module Typechecker where

import AST

data Error p
  = UndeclaredVariable p Var
  | InternalCompilerError String
  | ETypeVarMismatchError p Monotype Monotype
  | UndeclaredETypeVar p Var
  | TypeFormednessEVarNotDeclaredError p Var
  | TypeFormednessUVarNotDeclaredError p Var
  | TypeFormednessInvalidKindError p Var
  | CheckKindHasWrongKindError p Kind Kind
  | CheckKindEVarNotDeclaredError p Var
  | CheckKindUVarNotDeclaredError p Var
  | MonotypeIsNotTypeError p Monotype
  deriving (Show, Eq)

varContextLookup :: Context -> Var -> p -> Either (Error p) ContextEntry
varContextLookup  (entry @ (CVar y _ _): c) x p
  | x == y = return entry
  | otherwise = varContextLookup c x p
varContextLookup (_ : c) x p = varContextLookup c x p
varContextLookup [] x p = Left $ UndeclaredVariable p x

uTypeVarEqContextLookup :: Context -> UTypeVar -> Maybe ContextEntry
uTypeVarEqContextLookup (entry @ (CUTypeVarEq b _) : c) a
  | a == b = return entry
  | otherwise = uTypeVarEqContextLookup c a
uTypeVarEqContextLookup (_ : c) a = uTypeVarEqContextLookup c a
uTypeVarEqContextLookup [] _ = Nothing

solvedETypeVarContextLookup :: Context -> ETypeVar -> Maybe ContextEntry
solvedETypeVarContextLookup (entry @ (CETypeVar b _ _) : c) a
  | a == b = return entry
  | otherwise = solvedETypeVarContextLookup c a
solvedETypeVarContextLookup (_ : c) a = solvedETypeVarContextLookup c a
solvedETypeVarContextLookup [] _ = Nothing

eTypeVarContextLookup :: Context -> ETypeVar -> Maybe ContextEntry
eTypeVarContextLookup (entry @ (CETypeVar b _ _) : c) a
  | a == b = return entry
  | otherwise = eTypeVarContextLookup c a
eTypeVarContextLookup (entry @ (CTypeVar (E b) _) : c) a
  | a == b = return entry
  | otherwise = eTypeVarContextLookup c a
eTypeVarContextLookup (_ : c) a = eTypeVarContextLookup c a
eTypeVarContextLookup [] _ = Nothing

unsolvedTypeVarContextLookup :: Context -> TypeVar -> Maybe ContextEntry
unsolvedTypeVarContextLookup (entry @ (CTypeVar b _) : c) a
  | a == b = return entry
  | otherwise = unsolvedTypeVarContextLookup c a
unsolvedTypeVarContextLookup (_ : c) a = unsolvedTypeVarContextLookup c a
unsolvedTypeVarContextLookup [] _ = Nothing

eTypeVarContextReplace :: Context -> ETypeVar -> Monotype -> p -> Either (Error p) Context
eTypeVarContextReplace c @ (entry @ (CETypeVar (ETypeVar b) _ tau) : ct) (ETypeVar a) sigma p
  | a == b && tau == sigma = return c
  | a == b && tau /= sigma = Left $ ETypeVarMismatchError p tau sigma
  | otherwise = (:) entry <$> eTypeVarContextReplace ct (ETypeVar a) sigma p
eTypeVarContextReplace (entry @  (CTypeVar (E (ETypeVar b)) k) : ct) (ETypeVar a) sigma p
  | a == b = return $ CETypeVar (ETypeVar a) k sigma : ct
  | otherwise = (:) entry <$> eTypeVarContextReplace ct (ETypeVar a) sigma p
eTypeVarContextReplace (entry : ct) a sigma p = (:) entry <$> eTypeVarContextReplace ct a sigma p
eTypeVarContextReplace [] (ETypeVar a) _ p = Left $ UndeclaredETypeVar p a

monotypeToType :: Monotype -> p -> Either (Error p) Type
monotypeToType MUnit _ = return TUnit
monotypeToType (MArrow m1 m2) p = TArrow <$> monotypeToType m1 p <*> monotypeToType m2 p
monotypeToType (MCoproduct m1 m2) p = TCoproduct <$> monotypeToType m1 p <*> monotypeToType m2 p
monotypeToType (MProduct m1 m2) p = TProduct <$> monotypeToType m1 p <*> monotypeToType m2 p
monotypeToType (MEVar x) _ = return $ TEVar x
monotypeToType (MUVar x) _ = return $ TUVar x
monotypeToType n p = Left $ MonotypeIsNotTypeError p n

applyContextToType :: Context -> Type -> p-> Either (Error p) Type
applyContextToType c (TUVar u) p =
  case uTypeVarEqContextLookup c u of
    Just (CUTypeVarEq _ tau) -> monotypeToType (applyContextToMonotype c tau) p
    _ -> return $ TUVar u
applyContextToType c (TImp pr t) p = TImp (applyContextToProposition c pr) <$> applyContextToType c t p
applyContextToType c (TAnd t pr) p = TAnd <$> applyContextToType c t p <*> pure (applyContextToProposition c pr)
applyContextToType c (TArrow t1 t2) p = TArrow <$> applyContextToType c t1 p <*> applyContextToType c t2 p
applyContextToType c (TCoproduct t1 t2) p = TCoproduct <$> applyContextToType c t1 p <*> applyContextToType c t2 p
applyContextToType c (TProduct t1 t2) p = TProduct <$> applyContextToType c t1 p <*> applyContextToType c t2 p
applyContextToType c (TVec n t) p = TVec (applyContextToMonotype c n) <$> applyContextToType c t p
applyContextToType c (TEVar e) p =
  case solvedETypeVarContextLookup c e of
    Just (CETypeVar _ _ tau) -> monotypeToType (applyContextToMonotype c tau) p
    _ -> return $ TEVar e
applyContextToType c (TUniversal a k t) p = TUniversal a k <$> applyContextToType c t p
applyContextToType c (TExistential a k t) p = TExistential a k <$> applyContextToType c t p
applyContextToType _ TUnit _ = return TUnit

applyContextToMonotype :: Context -> Monotype -> Monotype
applyContextToMonotype c (MUVar u) =
  case uTypeVarEqContextLookup c u of
    Just (CUTypeVarEq _ tau) -> applyContextToMonotype c tau
    _ -> MUVar u
applyContextToMonotype c (MArrow m1 m2) = MArrow (applyContextToMonotype c m1) (applyContextToMonotype c m2)
applyContextToMonotype c (MCoproduct m1 m2) = MCoproduct (applyContextToMonotype c m1) (applyContextToMonotype c m2)
applyContextToMonotype c (MProduct m1 m2) = MProduct (applyContextToMonotype c m1) (applyContextToMonotype c m2)
applyContextToMonotype c (MEVar e) =
  case solvedETypeVarContextLookup c e of
    Just (CETypeVar _ _ tau) -> applyContextToMonotype c tau
    _ -> MEVar e
applyContextToMonotype _ MUnit = MUnit
applyContextToMonotype _ MZero = MZero
applyContextToMonotype c (MSucc n) = applyContextToMonotype c n

applyContextToProposition :: Context -> Proposition -> Proposition
applyContextToProposition c (m1, m2) = (applyContextToMonotype c m1, applyContextToMonotype c m2)

checkTypeWellFormednessWithPrnc :: Context -> Type -> Principality -> p -> Either (Error p) ()
checkTypeWellFormednessWithPrnc c t NotPrincipal p = checkTypeWellFormedness c t p
checkTypeWellFormednessWithPrnc _ _ Principal _ = undefined

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
checkTypeWellFormedness c (TEVar x @ (ETypeVar name)) p =
  case eTypeVarContextLookup c x of
    Just (CTypeVar _ KStar) -> return ()
    Just (CETypeVar _ KStar _) -> return ()
    Nothing -> Left $ TypeFormednessEVarNotDeclaredError p name
    _ -> Left $ TypeFormednessInvalidKindError p name
checkTypeWellFormedness c (TUVar x  @ (UTypeVar name)) p =
  case unsolvedTypeVarContextLookup c (U x) of
    Just (CTypeVar _ KStar) -> return ()
    Nothing -> Left $ TypeFormednessUVarNotDeclaredError p name
    _ -> Left $ TypeFormednessInvalidKindError p name

checkMonotypeHasKind :: Context -> Monotype -> p -> Kind -> Either (Error p) ()
checkMonotypeHasKind c m p k1 = do
  k2 <- inferMonotypeKind c m p
  if k1 == k2 then
    return ()
  else
    Left $ CheckKindHasWrongKindError p k1 k2

inferMonotypeKind :: Context -> Monotype -> p -> Either (Error p) Kind
inferMonotypeKind _ MUnit _ = return KStar
inferMonotypeKind _ MZero _ = return KNat
inferMonotypeKind c (MSucc n) p = checkMonotypeHasKind c n p KNat >> return KNat
inferMonotypeKind c (MArrow m1 m2) p = checkMonotypeHasKind c m1 p KStar >> checkMonotypeHasKind c m2 p KStar >> return KStar
inferMonotypeKind c (MCoproduct m1 m2) p = checkMonotypeHasKind c m1 p KStar >> checkMonotypeHasKind c m2 p KStar >> return KStar
inferMonotypeKind c (MProduct m1 m2) p = checkMonotypeHasKind c m1 p KStar >> checkMonotypeHasKind c m2 p KStar >> return KStar
inferMonotypeKind c (MEVar x @ (ETypeVar name)) p =
  case eTypeVarContextLookup c x of
    Just (CTypeVar _ k) -> return k
    Just (CETypeVar _ k _) -> return k
    _ ->  Left $ CheckKindEVarNotDeclaredError p name
inferMonotypeKind c (MUVar x @ (UTypeVar name)) p =
  case unsolvedTypeVarContextLookup c (U x) of
    Just (CTypeVar _ k) -> return k
    _ -> Left $ CheckKindUVarNotDeclaredError p name

checkPropWellFormedness :: Context -> Proposition -> p -> Either (Error p) ()
checkPropWellFormedness c (m1, m2) p = inferMonotypeKind c m1 p >>= checkMonotypeHasKind c m2 p

checkExpr :: Context -> Expr p -> Type -> Principality -> Either (Error p) Context
checkExpr c (EUnit _) TUnit _ = return c
checkExpr c (EUnit p) (TEVar a) _ = eTypeVarContextReplace c a MUnit p
checkExpr _ _ _ _ = undefined

-- checkValue :: Context -> Value p -> Type -> Principality -> Either (Error p) Context
-- checkValue _ _ _ = undefined

inferExpr :: Context -> Expr p -> Either (Error p) (Type, Principality, Context)
inferExpr c (EVar p x) = do
  (CVar _ t pr) <- varContextLookup c x p
  t2 <- applyContextToType c t p
  return (t2, pr, c)

inferExpr _ _ = undefined
-- inferValue :: Context -> Value p -> Either (Error p) (Type, Principality, Context)
-- inferValue _ _ = undefined
