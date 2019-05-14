module Typechecker where

import AST
import TypecheckerUtils
import qualified Data.Set as Set
import Control.Monad.State

import Control.Lens hiding (Context)

checkTypeWellFormednessWithPrnc :: Context -> Type -> Principality -> p -> Either (Error p) ()
checkTypeWellFormednessWithPrnc c t NotPrincipal p = checkTypeWellFormedness c t p
checkTypeWellFormednessWithPrnc c t Principal p =
  case Set.toList . freeExistentialVariables $ t of
    [] -> checkTypeWellFormedness c t p
    vars -> Left $ TypeFormednessPrcFEVError p vars

checkTypeWellFormedness :: Context -> Type -> p -> Either (Error p) ()
checkTypeWellFormedness _ TUnit _   = return ()
checkTypeWellFormedness _ TBool _   = return ()
checkTypeWellFormedness _ TInt _    = return ()
checkTypeWellFormedness _ TFloat _  = return ()
checkTypeWellFormedness _ TChar _   = return ()
checkTypeWellFormedness _ TString _ = return ()
checkTypeWellFormedness c (TArrow t1 t2) p = checkTypeWellFormedness c t1 p >> checkTypeWellFormedness c t2 p
checkTypeWellFormedness c (TCoproduct t1 t2) p = checkTypeWellFormedness c t1 p >> checkTypeWellFormedness c t2 p
checkTypeWellFormedness c (TProduct ts _) p = foldM_ ((.)(.)(.) (flip (checkTypeWellFormedness c) p) (flip const)) () ts
checkTypeWellFormedness c (TImp pr t) p = checkPropWellFormedness c pr p >> checkTypeWellFormedness c t p
checkTypeWellFormedness c (TAnd t pr) p = checkTypeWellFormedness c t p >> checkPropWellFormedness c pr p
checkTypeWellFormedness c (TUniversal x k t) p = checkTypeWellFormedness (CTypeVar (U x) k : c) t p
checkTypeWellFormedness c (TExistential x k t) p = checkTypeWellFormedness (CTypeVar (U x) k : c) t p
checkTypeWellFormedness c (TVec n t) p = checkMonotypeHasKind c n p KNat >> checkTypeWellFormedness c t p
checkTypeWellFormedness c (TEVar x) p =
  case typeVarContextLookup c $ eTypeVarName x of
    Just (CTypeVar (E _) KStar) -> return ()
    Just (CETypeVar _ KStar _) -> return ()
    Just (CTypeVar (E _) KNat) -> Left $ TypeHasWrongKindError p (TEVar x) KStar KNat
    Just (CETypeVar _ KNat _) -> Left $ TypeHasWrongKindError p (TEVar x) KStar KNat
    _ -> Left $ UndeclaredETypeVarError p x
checkTypeWellFormedness c (TUVar x) p =
  case typeVarContextLookup c $ uTypeVarName x of
    Just (CTypeVar (U _) KStar) -> return ()
    Just (CTypeVar (U _) KNat) -> Left $ TypeHasWrongKindError p (TUVar x) KStar KNat
    _ -> Left $ UndeclaredUTypeVarError p x

checkMonotypeHasKind :: Context -> Monotype -> p -> Kind -> Either (Error p) ()
checkMonotypeHasKind c m p k1 = do
  k2 <- inferMonotypeKind c m p
  if k1 == k2 then
    return ()
  else
    Left $ MonotypeHasWrongKindError p m k1 k2

inferMonotypeKind :: Context -> Monotype -> p -> Either (Error p) Kind
inferMonotypeKind _ MUnit _   = return KStar
inferMonotypeKind _ MBool _   = return KStar
inferMonotypeKind _ MInt _    = return KStar
inferMonotypeKind _ MFloat _  = return KStar
inferMonotypeKind _ MChar _   = return KStar
inferMonotypeKind _ MString _ = return KStar
inferMonotypeKind _ MZero _   = return KNat
inferMonotypeKind c (MSucc n) p = checkMonotypeHasKind c n p KNat >> return KNat
inferMonotypeKind c (MArrow m1 m2) p = checkMonotypeHasKind c m1 p KStar >> checkMonotypeHasKind c m2 p KStar >> return KStar
inferMonotypeKind c (MCoproduct m1 m2) p = checkMonotypeHasKind c m1 p KStar >> checkMonotypeHasKind c m2 p KStar >> return KStar
inferMonotypeKind c (MProduct ms _) p = foldM_ ((.)(.)(.) (flip (flip (checkMonotypeHasKind c) p) KStar) (flip const)) () ms >> return KStar
inferMonotypeKind c (MEVar x) p =
  case typeVarContextLookup c $ eTypeVarName x of
    Just (CTypeVar (E _) k) -> return k
    Just (CETypeVar _ k _) -> return k
    _ ->  Left $ UndeclaredETypeVarError p x
inferMonotypeKind c (MUVar x) p =
  case typeVarContextLookup c $ uTypeVarName x of
    Just (CTypeVar (U _) k) -> return k
    _ -> Left $ UndeclaredUTypeVarError p x

checkPropWellFormedness :: Context -> Proposition -> p -> Either (Error p) ()
checkPropWellFormedness c (m1, m2) p = inferMonotypeKind c m1 p >>= checkMonotypeHasKind c m2 p

subtype :: Context -> Type -> Polarity -> Type -> p -> StateT TypecheckerState (Either (Error p)) Context
subtype c t1 pol t2 p
  | not (headedByUniversal t1) && not (headedByExistential t1) &&
    not (headedByUniversal t2) && not (headedByExistential t2) = equivalentType c t1 t2 p
  | headedByUniversal t1 && not (headedByUniversal t2) && neg pol = do
      let (TUniversal (UTypeVar a) k t) = t1
      e <- ETypeVar . ("#" ++) . show . view freshVarNum <$> get
      modify $ over freshVarNum (+ 1)
      c2 <- subtype (CTypeVar (E e) k : CMarker : c) (substituteUVarInType (UTypeVar a) (E e) t) Negative t2 p
      return $ dropContextToMarker c2
  | headedByUniversal t2 && neg pol = do
      let (TUniversal (UTypeVar b) k t) = t2
      u <- UTypeVar . ("#" ++) . show . view freshVarNum <$> get
      modify $ over freshVarNum (+ 1)
      c2 <- subtype (CTypeVar (U u) k : CMarker : c) t1 Negative (substituteUVarInType (UTypeVar b) (U u) t) p
      return $ dropContextToMarker c2
  | headedByExistential t1 && pos pol = do
      let (TExistential (UTypeVar a) k t) = t1
      u <- UTypeVar . ("#" ++) . show . view freshVarNum <$> get
      modify $ over freshVarNum (+ 1)
      c2 <- subtype (CTypeVar (U u) k : CMarker : c) (substituteUVarInType (UTypeVar a) (U u) t) Positive t2 p
      return $ dropContextToMarker c2
  | not (headedByExistential t1) && headedByExistential t2 && pos pol = do
      let TExistential (UTypeVar b) k t = t2
      e <- ETypeVar . ("#" ++) . show . view freshVarNum <$> get
      modify $ over freshVarNum (+ 1)
      c2 <- subtype (CTypeVar (E e) k : CMarker : c) t1 Positive (substituteUVarInType (UTypeVar b) (E e) t) p
      return $ dropContextToMarker c2
  | pos pol && (neg . polarity $ t1) && (nonpos . polarity $ t2) = subtype c t1 Negative t2 p
  | pos pol && (nonpos . polarity $ t1) && (neg . polarity $ t2) = subtype c t1 Negative t2 p
  | neg pol && (pos . polarity $ t1) && (nonneg . polarity $ t2) = subtype c t1 Positive t2 p
  | neg pol && (nonneg . polarity $ t1) && (pos . polarity $ t2) = subtype c t1 Positive t2 p
  | otherwise = lift . Left $ NotSubtypeError p t1 t2

equivalentTypeBinary ::
  Context
  -> Type -> Type
  -> Type -> Type -> p
  -> StateT TypecheckerState (Either (Error p)) Context
equivalentTypeBinary c a1 a2 b1 b2 p = do
  c2 <- equivalentType c a1 b1 p
  a2' <- lift $ applyContextToType c2 a2 p
  b2' <- lift $ applyContextToType c2 b2 p
  equivalentType c2 a2' b2' p

equivalentPropositionalType ::
  Context
 -> Proposition -> Proposition
 -> Type -> Type -> p
 -> StateT TypecheckerState (Either (Error p)) Context
equivalentPropositionalType c q1 q2 a b p = do
  c2 <- lift $ equivalentProp c q1 q2 p
  a' <- lift $ applyContextToType c2 a p
  b' <- lift $ applyContextToType c2 b p
  equivalentType c2 a' b' p

equivalentQuantifierType ::
  Context
  -> UTypeVar -> Type
  -> UTypeVar -> Type
  -> Kind -> p
  -> StateT TypecheckerState (Either (Error p)) Context
equivalentQuantifierType c x1 t1 x2 t2 k p = do
  u <- UTypeVar . ("#" ++) . show . view freshVarNum <$> get
  modify $ over freshVarNum (+ 1)
  let t1' = substituteUVarInType x1 (U u) t1
  let t2' = substituteUVarInType x2 (U u) t2
  c2 <- equivalentType (CTypeVar (U u) k : CMarker : c) t1' t2' p
  return $ dropContextToMarker c2

equivalentType :: Context -> Type -> Type -> p -> StateT TypecheckerState (Either (Error p)) Context
equivalentType c TUnit   TUnit _   = return c
equivalentType c TBool   TBool _   = return c
equivalentType c TInt    TInt _    = return c
equivalentType c TFloat  TFloat _  = return c
equivalentType c TChar   TChar _   = return c
equivalentType c TString TString _ = return c
equivalentType c (TArrow a1 a2) (TArrow b1 b2) p = equivalentTypeBinary c a1 a2 b1 b2 p
equivalentType c (TCoproduct a1 a2) (TCoproduct b1 b2) p = equivalentTypeBinary c a1 a2 b1 b2 p
equivalentType c (TProduct (t1 : ts1) n1) (TProduct (t2 : ts2) n2) p =
  if n1 /= n2 then
    lift $ Left (TypesNotEquivalentError p (TProduct (t1 : ts1) n1) (TProduct (t2 : ts2) n2))
  else do
    c2 <- equivalentType c t1 t2 p
    foldM aux c2 $ zip ts1 ts2
  where
    aux _c (tl, tr) = do
      tl' <- lift $ applyContextToType _c tl p
      tr' <- lift $ applyContextToType _c tr p
      equivalentType _c tl' tr' p
equivalentType c (TVec n1 t1) (TVec n2 t2) p = do
  c2 <- lift $ checkEquation c n1 n2 KNat p
  t1'<- lift $ applyContextToType c2 t1 p
  t2'<- lift $ applyContextToType c2 t2 p
  equivalentType c2 t1' t2' p
equivalentType c (TImp q1 a) (TImp q2 b) p = equivalentPropositionalType c q1 q2 a b p
equivalentType c (TAnd a q1) (TAnd b q2) p = equivalentPropositionalType c q1 q2 a b p
equivalentType c (TUniversal x1 k1 t1) (TUniversal x2 k2 t2) p
  | k1 /= k2 = lift $ Left (TypesNotEquivalentError p (TUniversal x1 k1 t1) (TUniversal x2 k2 t2))
  | otherwise =  equivalentQuantifierType c x1 t1 x2 t2 k1 p
equivalentType c (TExistential x1 k1 t1) (TExistential x2 k2 t2) p
  | k1 /= k2 = lift $ Left (TypesNotEquivalentError p (TExistential x1 k1 t1) (TExistential x2 k2 t2))
  | otherwise =  equivalentQuantifierType c x1 t1 x2 t2 k1 p
equivalentType c (TUVar a) (TUVar b) p
  | a == b = return c
  | otherwise = lift $ Left (TypesNotEquivalentError p (TUVar a) (TUVar b))
equivalentType c t1 @ (TEVar a) t2 p
  | t1 == t2 = return c
  | otherwise = do
      m <- lift $ typeToMonotype t2 p
      if eTypeVarName a `Set.member` freeVariablesOfMonotype m then
        lift $ Left (TypesNotEquivalentError p t1 t2)
      else
        lift $ instantiateEVar c a m KStar p
equivalentType c t1 (TEVar b) p = do
  m <- lift $ typeToMonotype t1 p
  if eTypeVarName b `Set.member` freeVariablesOfMonotype m then
    lift $ Left (TypesNotEquivalentError p t1 $ TEVar b)
  else
    lift $ instantiateEVar c b m KStar p
equivalentType _ t1 t2 p = lift $ Left (TypesNotEquivalentError p t1 t2)

equivalentProp :: Context -> Proposition -> Proposition -> p -> Either (Error p) Context
equivalentProp c (p1, p2) (q1, q2) p = do
  k <- inferMonotypeKind c p1 p
  checkMonotypeHasKind c p2 p k
  checkMonotypeHasKind c q1 p k
  checkMonotypeHasKind c q2 p k
  c2 <- checkEquation c p1 q1 k p
  p2' <- applyContextToMonotype c2 p2 p
  q2' <- applyContextToMonotype c2 q2 p
  checkEquation c2 p2' q2' k p

instantiateEVarBinary ::
  Context
  -> ETypeVar -> ETypeVar
  -> Monotype -> Monotype
  -> p -> Either (Error p) Context
instantiateEVarBinary c a1 a2 m1 m2 p = do
  c2 <- instantiateEVar c a1 m1 KStar p
  m2'<- applyContextToMonotype c2 m2 p
  instantiateEVar c2 a2 m2' KStar p

instantiateEVar :: Context -> ETypeVar -> Monotype -> Kind -> p -> Either (Error p) Context
instantiateEVar c a MZero   KNat p  = eTypeVarContextReplace c a KNat  MZero   [] p
instantiateEVar c a MUnit   KStar p = eTypeVarContextReplace c a KStar MUnit   [] p
instantiateEVar c a MBool   KStar p = eTypeVarContextReplace c a KStar MBool   [] p
instantiateEVar c a MInt    KStar p = eTypeVarContextReplace c a KStar MInt    [] p
instantiateEVar c a MFloat  KStar p = eTypeVarContextReplace c a KStar MFloat  [] p
instantiateEVar c a MChar   KStar p = eTypeVarContextReplace c a KStar MChar   [] p
instantiateEVar c a MString KStar p = eTypeVarContextReplace c a KStar MString [] p
instantiateEVar c a (MSucc n) KNat p = do
  let a1 = ETypeVar $ eTypeVarName a ++ "-1"
  c2 <- eTypeVarContextReplace c a KNat (MSucc $ MEVar a1) [CTypeVar (E a1) KNat] p
  instantiateEVar c2 a1 n KNat p
instantiateEVar c a (MArrow m1 m2) KStar p = do
  let (a1, a2) = generateSubETypeVars a
  c2 <- eTypeVarContextReplace c a KStar (MArrow (MEVar a1) (MEVar a2)) [CTypeVar (E a1) KStar, CTypeVar (E a2) KStar] p
  instantiateEVarBinary c2 a1 a2 m1 m2 p
instantiateEVar c a (MCoproduct m1 m2) KStar p = do
  let (a1, a2) = generateSubETypeVars a
  c2 <- eTypeVarContextReplace c a KStar (MCoproduct (MEVar a1) (MEVar a2)) [CTypeVar (E a1) KStar, CTypeVar (E a2) KStar] p
  instantiateEVarBinary c2 a1 a2 m1 m2 p
instantiateEVar c a (MProduct (m1 : ms) n) KStar p = do
  let a1 : as = generateSubETypeVarsList a n
  c2 <- eTypeVarContextReplace c a KStar (MProduct (map MEVar (a1 : as)) n) (map (flip CTypeVar KStar . E) $ a1 : as) p
  c3 <-instantiateEVar c2 a1 m1 KStar p
  foldM aux c3 $ zip as ms
  where
    aux _c  (_a, m) = do
      m'<- applyContextToMonotype _c m p
      instantiateEVar _c _a m' KStar p
instantiateEVar c a (MEVar b) k1 p
  | a == b = do
      case typeVarContextLookup c (eTypeVarName a) of
        Just (CTypeVar (E _) k) -> if k == k1 then return () else Left $ ETypeVarKindMismatchError p a k k1
        Just (CETypeVar _ k _) -> if k == k1 then return () else Left $ ETypeVarKindMismatchError p a k k1
        _ ->  Left $ UndeclaredETypeVarError p a
      return c
  | otherwise = do
      c2 <- takeContextToETypeVar a c p
      replaceB <- case typeVarContextLookup c2 (eTypeVarName b) of
        Just (CTypeVar (E _) k) -> if k == k1 then return True else Left $ ETypeVarKindMismatchError p b k k1
        Just (CETypeVar _ k _)  -> if k == k1 then return True else Left $ ETypeVarKindMismatchError p a k k1
        Nothing -> return False
        _ ->  Left $ UndeclaredETypeVarError p b
      if replaceB then
        eTypeVarContextReplace c b k1 (MEVar a) [] p
      else (do
        c3 <- dropContextToETypeVar a c p
        checkMonotypeHasKind c3 (MEVar b) p k1
        eTypeVarContextReplace c a k1 (MEVar b) [] p)
instantiateEVar c a m k p = do
  c2 <- dropContextToETypeVar a c p
  checkMonotypeHasKind c2 m p k
  eTypeVarContextReplace c a k m [] p

checkEquationBinary ::
  Context
  -> Monotype -> Monotype
  -> Monotype -> Monotype
  -> p -> Either (Error p) Context
checkEquationBinary c m1 m2 n1 n2 p = do
  c2 <- checkEquation c m1 n1 KStar p
  m2' <- applyContextToMonotype c2 m2 p
  n2' <- applyContextToMonotype c2 n2 p
  checkEquation c2 m2' n2' KStar p

checkEquation :: Context -> Monotype -> Monotype -> Kind -> p -> Either (Error p) Context
checkEquation c MUnit   MUnit   KStar _ = return c
checkEquation c MBool   MBool   KStar _ = return c
checkEquation c MInt    MInt    KStar _ = return c
checkEquation c MFloat  MFloat  KStar _ = return c
checkEquation c MChar   MChar   KStar _ = return c
checkEquation c MString MString KStar _ = return c
checkEquation c MZero   MZero   KNat _  = return c
checkEquation c (MUVar a) (MUVar b) k p
  | a == b = return c
  | otherwise = Left $ EquationFalseError p (MUVar a) (MUVar b) k
checkEquation c (MArrow m1 m2) (MArrow n1 n2) KStar p = checkEquationBinary c m1 m2 n1 n2 p
checkEquation c (MCoproduct m1 m2) (MCoproduct n1 n2) KStar p = checkEquationBinary c m1 m2 n1 n2 p
checkEquation c (MProduct (m1 : ms1) n1) (MProduct (m2 : ms2) n2) KStar p =
  if n1 /= n2 then
    Left (EquationFalseError p (MProduct (m1 : ms1) n1) (MProduct (m2 : ms2) n2) KStar)
  else do
    c2 <- checkEquation c m1 m2 KStar p
    foldM aux c2 $ zip ms1 ms2
  where
    aux _c (ml, mr) = do
      ml' <- applyContextToMonotype _c ml p
      mr' <- applyContextToMonotype _c mr p
      checkEquation _c ml' mr' KStar p
checkEquation c (MSucc n1) (MSucc n2) KNat p = checkEquation c n1 n2 KNat p
checkEquation c m1 @ (MEVar a) m2 k p
  | m1 == m2 = return c
  | eTypeVarName a `Set.member` freeVariablesOfMonotype m2 = Left $ EquationFalseError p m1 m2 k
  | otherwise = instantiateEVar c a m2 k p
checkEquation c m1 m2 @ (MEVar b) k p
  | eTypeVarName b `Set.member` freeVariablesOfMonotype m1 = Left $ EquationFalseError p m1 m2 k
  | otherwise = instantiateEVar c b m1 k p
checkEquation _ m1 m2 k p = Left $ EquationFalseError p m1 m2 k

checkExpr :: Context -> Expr p -> Type -> Principality -> StateT TypecheckerState (Either (Error p)) Context
checkExpr c (EUnit _)     TUnit _   = return c
checkExpr c (EBool _ _)   TBool _   = return c
checkExpr c (EInt _ _)    TInt _    = return c
checkExpr c (EFloat _ _)  TFloat _  = return c
checkExpr c (EChar _ _)   TChar _   = return c
checkExpr c (EString _ _) TString _ = return c
checkExpr c (EUnit p)     (TEVar a) _ = lift $ eTypeVarContextReplace c a KStar MUnit   [] p
checkExpr c (EBool p _)   (TEVar a) _ = lift $ eTypeVarContextReplace c a KStar MBool   [] p
checkExpr c (EInt p _)    (TEVar a) _ = lift $ eTypeVarContextReplace c a KStar MInt    [] p
checkExpr c (EFloat p _)  (TEVar a) _ = lift $ eTypeVarContextReplace c a KStar MFloat  [] p
checkExpr c (EChar p _)   (TEVar a) _ = lift $ eTypeVarContextReplace c a KStar MChar   [] p
checkExpr c (EString p _) (TEVar a) _ = lift $ eTypeVarContextReplace c a KStar MString [] p
checkExpr c (ELambda _ x e) (TArrow t1 t2) pr = do
  c2 <- checkExpr (CVar x t1 pr : CMarker : c) e t2 pr
  return $ dropContextToMarker c2
checkExpr c (ELambda p x e) (TEVar a) _ = do
  let (a1, a2) = generateSubETypeVars a
  c2 <- lift $ eTypeVarContextReplace c a KStar (MArrow (MEVar a1) (MEVar a2)) [CTypeVar (E a1) KStar, CTypeVar (E a2) KStar] p
  c3 <- checkExpr (CVar x (TEVar a1) NotPrincipal : CMarker : c2) e (TEVar a2) NotPrincipal
  return $ dropContextToMarker c3
checkExpr c (ETuple p (e1 : es) n1) (TProduct (t1 : ts) n2) pr =
  if n1 /= n2 then
    lift $ Left (TypecheckingError (ETuple p (e1 : es) n1) (TProduct (t1 : ts) n2))
  else do
    c2 <- checkExpr c e1 t1 pr
    foldM aux c2 $ zip es ts
  where
    aux _c (e, t) = do
      t' <- lift $ applyContextToType _c t p
      checkExpr _c e t' pr
checkExpr c (ETuple p (e1 : es) n) (TEVar a) _ = do
  let a1 : as = generateSubETypeVarsList a n
  c2 <- lift $ eTypeVarContextReplace c a KStar (MProduct (map MEVar (a1 : as)) n) (map (flip CTypeVar KStar . E) $ a1 : as) p
  c3 <- checkExpr c2 e1 (TEVar a1) NotPrincipal
  foldM aux c3 $ zip es $ map TEVar as
  where
    aux _c (e, t) = do
      t' <- lift $ applyContextToType _c t p
      checkExpr _c e t' NotPrincipal
checkExpr c (EInjk _ e k) (TCoproduct t1 t2) pr = checkExpr c e ([t1, t2] !! k) pr
checkExpr c (EInjk p e k) (TEVar a) _ = do
  let (a1, a2) = generateSubETypeVars a
  c2 <- lift $ eTypeVarContextReplace c a KStar (MCoproduct (MEVar a1) (MEVar a2)) [CTypeVar (E a1) KStar, CTypeVar (E a2) KStar] p
  checkExpr c2 e ([TEVar a1, TEVar a2] !! k) NotPrincipal
checkExpr c e t _ = do
  (t2, _, c2) <- inferExpr c e
  subtype c2 t2 (joinPolarity (polarity t) (polarity t2)) t $ getPos e

inferExpr :: Context -> Expr p -> StateT TypecheckerState (Either (Error p)) (Type, Principality, Context)
inferExpr c (EVar p x) = do
  (CVar _ t pr) <- lift $ varContextLookup c x p
  t2 <- lift $ applyContextToType c t p
  return (t2, pr, c)
inferExpr c (EAnnot p e t) = do
  lift $ checkTypeWellFormednessWithPrnc c t Principal p
  t2 <- lift $ applyContextToType c t p
  c2 <- checkExpr c e t2 Principal
  return (t2, Principal, c2)
inferExpr _ _ = undefined
