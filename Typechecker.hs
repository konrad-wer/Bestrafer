module Typechecker where

import AST
import CommonUtils
import TypecheckerUtils
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Monad.State
import Control.Monad.Trans.Maybe

import Control.Lens hiding (Context)

checkedIntroductionForm :: Expr p -> Bool
checkedIntroductionForm EUnit {}   = True
checkedIntroductionForm EBool {}   = True
checkedIntroductionForm EInt {}    = True
checkedIntroductionForm EFloat {}  = True
checkedIntroductionForm EChar {}   = True
checkedIntroductionForm EString {} = True
checkedIntroductionForm ELambda {} = True
checkedIntroductionForm ETuple {}  = True
--checkedIntroductionForm EConstr {} = True
checkedIntroductionForm ENil {}    = True
checkedIntroductionForm ECons {}   = True
checkedIntroductionForm _ = False --Left $ ExprNotCheckedIntroductionFormError e t

checkBranchWellFormedness :: Branch p -> Either (TypeError p) ()
checkBranchWellFormedness b @ (branchPtrns, _, _) = do
  let varList = branchPtrns >>= getVars
  if (Set.size . Set.fromList $ varList) == length varList then
    return ()
  else
    Left $ DuplicateVarsInBranchError b
  where
    getVars (PVar    _ x) = return  x
    getVars (PTuple  _ ptrns _) = ptrns >>= getVars
    getVars (PNil    _) = mzero
    getVars (PCons   _ ptrn1 ptrn2) = getVars ptrn1 `mplus` getVars ptrn2
    getVars (PWild   _) = mzero
    getVars (PUnit   _) = mzero
    getVars (PBool   _ _) = mzero
    getVars (PInt    _ _) = mzero
    getVars (PFloat  _ _) = mzero
    getVars (PChar   _ _) = mzero
    getVars (PString _ _) = mzero
    getVars (PConstr _ _ ptrns) = ptrns >>= getVars

checkTypeWellFormednessWithPrnc :: p -> Context -> Type -> Principality -> StateT TypecheckerState (Either (TypeError p)) ()
checkTypeWellFormednessWithPrnc p c t NotPrincipal = checkTypeWellFormedness p c t
checkTypeWellFormednessWithPrnc p c t Principal =
  case Set.toList . freeExistentialVariables $ t of
    [] -> checkTypeWellFormedness p c t
    vars -> lift . Left $ TypeFormednessPrcFEVError p vars

checkGADTParameterWellFormedness ::
  p -> Context -> (GADTDefParameter, GADTParameter)
  -> StateT TypecheckerState (Either (TypeError p)) ()
checkGADTParameterWellFormedness p c (GADTDefParamType _, ParameterType t) = checkTypeWellFormedness p c t
checkGADTParameterWellFormedness p c (GADTDefParamMonotype k, ParameterMonotype m) = checkMonotypeHasKind p c m k
checkGADTParameterWellFormedness p c (GADTDefParamType _, ParameterMonotype m) =
  lift (monotypeToType p m) >>= checkTypeWellFormedness p c
checkGADTParameterWellFormedness p c (GADTDefParamMonotype k, ParameterType t) =
  lift (typeToMonotype p t) >>= flip (checkMonotypeHasKind p c) k

checkTypeWellFormedness :: p -> Context -> Type -> StateT TypecheckerState (Either (TypeError p)) ()
checkTypeWellFormedness _ _ TUnit   = return ()
checkTypeWellFormedness _ _ TBool   = return ()
checkTypeWellFormedness _ _ TInt    = return ()
checkTypeWellFormedness _ _ TFloat  = return ()
checkTypeWellFormedness _ _ TChar   = return ()
checkTypeWellFormedness _ _ TString = return ()
checkTypeWellFormedness p c (TArrow t1 t2)  = checkTypeWellFormedness p c t1 >> checkTypeWellFormedness p c t2
checkTypeWellFormedness p c (TGADT name ts) = do
  gadtDefParams <- Map.lookup name . view gadtDefs <$> get
  case gadtDefParams of
    Nothing -> lift . Left $ UndeclaredGADTError p name
    Just params
      | length params /= length ts -> lift . Left $ MismatchedGADTArityError p name (length params) $ length ts
      | otherwise -> foldM_ ((.)(.)(.) (checkGADTParameterWellFormedness p c) (flip const)) () $ zip params ts
checkTypeWellFormedness p c (TProduct ts _) = foldM_ ((.)(.)(.) (checkTypeWellFormedness p c) (flip const)) () ts
checkTypeWellFormedness p c (TImp pr t) = checkPropWellFormedness p c pr >> checkTypeWellFormedness p c t
checkTypeWellFormedness p c (TAnd t pr) = checkTypeWellFormedness p c t >> checkPropWellFormedness p c pr
checkTypeWellFormedness p c (TUniversal x k t) = checkTypeWellFormedness p (CTypeVar (U x) k : c) t
checkTypeWellFormedness p c (TExistential x k t) = checkTypeWellFormedness p (CTypeVar (U x) k : c) t
checkTypeWellFormedness p c (TVec n t) = checkMonotypeHasKind p c n KNat >> checkTypeWellFormedness p c t
checkTypeWellFormedness p c (TEVar x) =
  case typeVarContextLookup c $ eTypeVarName x of
    Just (CTypeVar (E _) KStar) -> return ()
    Just (CETypeVar _ KStar _) -> return ()
    Just (CTypeVar (E _) KNat) -> lift . Left $ TypeHasWrongKindError p (TEVar x) KStar KNat
    Just (CETypeVar _ KNat _) -> lift . Left $ TypeHasWrongKindError p (TEVar x) KStar KNat
    _ -> lift . Left $ UndeclaredETypeVarError p x
checkTypeWellFormedness p c (TUVar x) =
  case typeVarContextLookup c $ uTypeVarName x of
    Just (CTypeVar (U _) KStar) -> return ()
    Just (CTypeVar (U _) KNat) -> lift . Left $ TypeHasWrongKindError p (TUVar x) KStar KNat
    _ -> lift . Left $ UndeclaredUTypeVarError p x

checkPropWellFormedness :: p -> Context -> Proposition -> StateT TypecheckerState (Either (TypeError p)) ()
checkPropWellFormedness p c (m1, m2) = inferMonotypeKind p c m1 >>= checkMonotypeHasKind p c m2

checkMonotypeHasKind :: p -> Context -> Monotype -> Kind -> StateT TypecheckerState (Either (TypeError p)) ()
checkMonotypeHasKind p c m k1 = do
  k2 <- inferMonotypeKind p c m
  if k1 == k2 then
    return ()
  else
    lift . Left $ MonotypeHasWrongKindError p m k1 k2

inferMonotypeKind :: p -> Context -> Monotype -> StateT TypecheckerState (Either (TypeError p)) Kind
inferMonotypeKind _ _ MUnit   = return KStar
inferMonotypeKind _ _ MBool   = return KStar
inferMonotypeKind _ _ MInt    = return KStar
inferMonotypeKind _ _ MFloat  = return KStar
inferMonotypeKind _ _ MChar   = return KStar
inferMonotypeKind _ _ MString = return KStar
inferMonotypeKind _ _ MZero   = return KNat
inferMonotypeKind p c (MSucc n) = checkMonotypeHasKind p c n KNat >> return KNat
inferMonotypeKind p c (MArrow m1 m2)  = checkMonotypeHasKind p c m1 KStar >> checkMonotypeHasKind p c m2 KStar >> return KStar
inferMonotypeKind p c (MGADT name ms) = do
  gadtDefParams <- Map.lookup name . view gadtDefs <$> get
  case gadtDefParams of
    Nothing -> lift . Left $ UndeclaredGADTError p name
    Just params
      | length params /= length ms -> lift . Left $ MismatchedGADTArityError p name (length params) $ length ms
      | otherwise -> let mparams = map paramToKind params in
        foldM_ ((.)(.)(.) (uncurry (checkMonotypeHasKind p c)) (flip const)) () (zip ms mparams) >> return KStar
  where
    paramToKind GADTDefParamType {} = KStar
    paramToKind (GADTDefParamMonotype k) = k
inferMonotypeKind p c (MProduct ms _) = foldM_ ((.)(.)(.) (flip (checkMonotypeHasKind p c) KStar) (flip const)) () ms >> return KStar
inferMonotypeKind p c (MEVar x) =
  case typeVarContextLookup c $ eTypeVarName x of
    Just (CTypeVar (E _) k) -> return k
    Just (CETypeVar _ k _) -> return k
    _ ->  lift . Left $ UndeclaredETypeVarError p x
inferMonotypeKind p c (MUVar x) =
  case typeVarContextLookup c $ uTypeVarName x of
    Just (CTypeVar (U _) k) -> return k
    _ -> lift . Left $ UndeclaredUTypeVarError p x

subtype :: Context -> Type -> Polarity -> Type -> p -> StateT TypecheckerState (Either (TypeError p)) Context
subtype c t1 pol t2 p
  | not (headedByUniversal t1) && not (headedByExistential t1) &&
    not (headedByUniversal t2) && not (headedByExistential t2) = equivalentType c t1 t2 p
  | headedByUniversal t1 && not (headedByUniversal t2) && neg pol = do
      let (TUniversal (UTypeVar a) k t) = t1
      e <- ETypeVar <$> generateFreshTypeVarName "subtype" a
      c2 <- subtype (CTypeVar (E e) k : CMarker : c) (substituteUVarInType (UTypeVar a) (E e) t) Negative t2 p
      return $ dropContextToMarker c2
  | headedByUniversal t2 && neg pol = do
      let (TUniversal (UTypeVar b) k t) = t2
      u <- UTypeVar <$> generateFreshTypeVarName "subtype" b
      c2 <- subtype (CTypeVar (U u) k : CMarker : c) t1 Negative (substituteUVarInType (UTypeVar b) (U u) t) p
      return $ dropContextToMarker c2
  | headedByExistential t1 && pos pol = do
      let (TExistential (UTypeVar a) k t) = t1
      u <- UTypeVar <$> generateFreshTypeVarName "subtype" a
      c2 <- subtype (CTypeVar (U u) k : CMarker : c) (substituteUVarInType (UTypeVar a) (U u) t) Positive t2 p
      return $ dropContextToMarker c2
  | not (headedByExistential t1) && headedByExistential t2 && pos pol = do
      let TExistential (UTypeVar b) k t = t2
      e <- ETypeVar <$> generateFreshTypeVarName "subtype" b
      c2 <- subtype (CTypeVar (E e) k : CMarker : c) t1 Positive (substituteUVarInType (UTypeVar b) (E e) t) p
      return $ dropContextToMarker c2
  | pos pol && (neg . polarity $ t1) && (nonpos . polarity $ t2) = subtype c t1 Negative t2 p
  | pos pol && (nonpos . polarity $ t1) && (neg . polarity $ t2) = subtype c t1 Negative t2 p
  | neg pol && (pos . polarity $ t1) && (nonneg . polarity $ t2) = subtype c t1 Positive t2 p
  | neg pol && (nonneg . polarity $ t1) && (pos . polarity $ t2) = subtype c t1 Positive t2 p
  | otherwise = lift . Left $ NotSubtypeError p t1 t2

equivalentGADTParameter ::
  Context -> GADTParameter -> GADTParameter
  -> p -> StateT TypecheckerState (Either (TypeError p)) Context
equivalentGADTParameter c (ParameterType t1) (ParameterType t2) p = equivalentType c t1 t2 p
equivalentGADTParameter c (ParameterMonotype m1) (ParameterMonotype m2) p = do
  k <- inferMonotypeKind p c m1
  checkMonotypeHasKind p c m1 k
  checkEquation c m1 m2 k p
equivalentGADTParameter c (ParameterType t1) (ParameterMonotype m2) p = do
  m1 <- lift $ typeToMonotype p t1
  checkEquation c m1 m2 KStar p
equivalentGADTParameter c (ParameterMonotype m1) (ParameterType t2) p = do
  m2 <- lift $ typeToMonotype p t2
  checkEquation c m1 m2 KStar p

equivalentPropositionalType ::
  Context
 -> Proposition -> Proposition
 -> Type -> Type -> p
 -> StateT TypecheckerState (Either (TypeError p)) Context
equivalentPropositionalType c q1 q2 a b p = do
  c2 <- equivalentProp c q1 q2 p
  a' <- lift $ applyContextToType p c2 a
  b' <- lift $ applyContextToType p c2 b
  equivalentType c2 a' b' p

equivalentQuantifierType ::
  Context
  -> UTypeVar -> Type
  -> UTypeVar -> Type
  -> Kind -> p
  -> StateT TypecheckerState (Either (TypeError p)) Context
equivalentQuantifierType c x1 t1 x2 t2 k p = do
  u <- UTypeVar <$> generateFreshTypeVarName "equivalentQuantifierType" (uTypeVarName x1 ++ " " ++ uTypeVarName x2)
  let t1' = substituteUVarInType x1 (U u) t1
  let t2' = substituteUVarInType x2 (U u) t2
  c2 <- equivalentType (CTypeVar (U u) k : CMarker : c) t1' t2' p
  return $ dropContextToMarker c2

equivalentType :: Context -> Type -> Type -> p -> StateT TypecheckerState (Either (TypeError p)) Context
equivalentType c TUnit   TUnit _   = return c
equivalentType c TBool   TBool _   = return c
equivalentType c TInt    TInt _    = return c
equivalentType c TFloat  TFloat _  = return c
equivalentType c TChar   TChar _   = return c
equivalentType c TString TString _ = return c
equivalentType c (TArrow a1 a2) (TArrow b1 b2) p = do
  c2 <- equivalentType c a1 b1 p
  a2' <- lift $ applyContextToType p c2 a2
  b2' <- lift $ applyContextToType p c2 b2
  equivalentType c2 a2' b2' p
equivalentType c (TGADT n1 (t1 : ts1)) (TGADT n2 (t2 : ts2)) p
   | n1 /= n2 = lift . Left $ TypesNotEquivalentError p (TGADT n1 ts1) (TGADT n2 ts2)
   | otherwise = do
     c2 <- equivalentGADTParameter c t1 t2 p
     foldM aux c2 $ zip ts1 ts2
     where
       aux _c (tl, tr) = do
         tl' <- lift $ applyContextToGADTParameter p _c tl
         tr' <- lift $ applyContextToGADTParameter p _c tr
         equivalentGADTParameter _c tl' tr' p
equivalentType c (TProduct (t1 : ts1) n1) (TProduct (t2 : ts2) n2) p
   | n1 /= n2 = lift . Left $ TypesNotEquivalentError p (TProduct (t1 : ts1) n1) (TProduct (t2 : ts2) n2)
   | otherwise = do
     c2 <- equivalentType c t1 t2 p
     foldM aux c2 $ zip ts1 ts2
     where
       aux _c (tl, tr) = do
         tl' <- lift $ applyContextToType p _c tl
         tr' <- lift $ applyContextToType p _c tr
         equivalentType _c tl' tr' p
equivalentType c (TVec n1 t1) (TVec n2 t2) p = do
  c2 <- checkEquation c n1 n2 KNat p
  t1'<- lift $ applyContextToType p c2 t1
  t2'<- lift $ applyContextToType p c2 t2
  equivalentType c2 t1' t2' p
equivalentType c (TImp q1 a) (TImp q2 b) p = equivalentPropositionalType c q1 q2 a b p
equivalentType c (TAnd a q1) (TAnd b q2) p = equivalentPropositionalType c q1 q2 a b p
equivalentType c (TUniversal x1 k1 t1) (TUniversal x2 k2 t2) p
  | k1 /= k2 = lift . Left $ TypesNotEquivalentError p (TUniversal x1 k1 t1) (TUniversal x2 k2 t2)
  | otherwise =  equivalentQuantifierType c x1 t1 x2 t2 k1 p
equivalentType c (TExistential x1 k1 t1) (TExistential x2 k2 t2) p
  | k1 /= k2 = lift . Left $ TypesNotEquivalentError p (TExistential x1 k1 t1) (TExistential x2 k2 t2)
  | otherwise =  equivalentQuantifierType c x1 t1 x2 t2 k1 p
equivalentType c (TUVar a) (TUVar b) p
  | a == b = return c
  | otherwise = lift . Left $ TypesNotEquivalentError p (TUVar a) (TUVar b)
equivalentType c t1 @ (TEVar a) t2 p
  | t1 == t2 = return c
  | otherwise = do
      m <- lift $ typeToMonotype p t2
      if eTypeVarName a `Set.member` freeVariablesOfMonotype m then
        lift . Left $ TypesNotEquivalentError p t1 t2
      else
        instantiateEVar c a m KStar p
equivalentType c t1 (TEVar b) p = do
  m <- lift $ typeToMonotype p t1
  if eTypeVarName b `Set.member` freeVariablesOfMonotype m then
    lift . Left $ TypesNotEquivalentError p t1 $ TEVar b
  else
    instantiateEVar c b m KStar p
equivalentType _ t1 t2 p = lift . Left $ TypesNotEquivalentError p t1 t2

equivalentProp :: Context -> Proposition -> Proposition -> p -> StateT TypecheckerState (Either (TypeError p)) Context
equivalentProp c (p1, p2) (q1, q2) p = do
  k <- inferMonotypeKind p c p1
  checkMonotypeHasKind p c p2 k
  checkMonotypeHasKind p c q1 k
  checkMonotypeHasKind p c q2 k
  c2 <- checkEquation c p1 q1 k p
  p2' <- lift $ applyContextToMonotype p c2 p2
  q2' <- lift $ applyContextToMonotype p c2 q2
  checkEquation c2 p2' q2' k p

instantiateEVarNAry :: Context -> [ETypeVar] -> [(Monotype, Kind)] -> p -> StateT TypecheckerState (Either (TypeError p))Context
instantiateEVarNAry c [] [] _ = return c
instantiateEVarNAry c (a1 : as) ((m1, k1) : mks) p = do
  c2 <- instantiateEVar c a1 m1 k1 p
  foldM aux c2 $ zip as mks
  where
    aux _c  (_a, (m, k)) = do
      m'<- lift $ applyContextToMonotype p _c m
      instantiateEVar _c _a m' k p
instantiateEVarNAry _ _ _ p = lift . Left $ InternalCompilerTypeError p "instantiateEVarNAry"

instantiateEVar :: Context -> ETypeVar -> Monotype -> Kind -> p -> StateT TypecheckerState (Either (TypeError p)) Context
instantiateEVar c a MZero   KNat p  = lift $ eTypeVarContextReplace c a KNat  MZero   [] p
instantiateEVar c a MUnit   KStar p = lift $ eTypeVarContextReplace c a KStar MUnit   [] p
instantiateEVar c a MBool   KStar p = lift $ eTypeVarContextReplace c a KStar MBool   [] p
instantiateEVar c a MInt    KStar p = lift $ eTypeVarContextReplace c a KStar MInt    [] p
instantiateEVar c a MFloat  KStar p = lift $ eTypeVarContextReplace c a KStar MFloat  [] p
instantiateEVar c a MChar   KStar p = lift $ eTypeVarContextReplace c a KStar MChar   [] p
instantiateEVar c a MString KStar p = lift $ eTypeVarContextReplace c a KStar MString [] p
instantiateEVar c a (MSucc n) KNat p = do
  let a1 = ETypeVar $ eTypeVarName a ++ "-1"
  c2 <- lift $ eTypeVarContextReplace c a KNat (MSucc $ MEVar a1) [CTypeVar (E a1) KNat] p
  instantiateEVar c2 a1 n KNat p
instantiateEVar c a (MArrow m1 m2) KStar p = do
  let (a1, a2) = generateSubETypeVars a
  c2 <- lift $ eTypeVarContextReplace c a KStar (MArrow (MEVar a1) (MEVar a2)) [CTypeVar (E a1) KStar, CTypeVar (E a2) KStar] p
  c3 <- instantiateEVar c2 a1 m1 KStar p
  m2'<- lift $ applyContextToMonotype p c3 m2
  instantiateEVar c3 a2 m2' KStar p
instantiateEVar c a (MGADT n ms) KStar p = do
  let as = generateSubETypeVarsList a $ length ms
  ks <- mapM (inferMonotypeKind p c) ms
  c2 <- lift $ eTypeVarContextReplace c a KStar (MGADT n (map MEVar as)) (zipWith (CTypeVar . E) as ks) p
  instantiateEVarNAry c2 as (zip ms ks) p
instantiateEVar c a (MProduct ms n) KStar p = do
  let as = generateSubETypeVarsList a n
  c2 <- lift $ eTypeVarContextReplace c a KStar (MProduct (map MEVar as) n) (map (flip CTypeVar KStar . E) as) p
  instantiateEVarNAry c2 as (map (flip (,) KStar) ms) p
instantiateEVar c a (MEVar b) k1 p
  | a == b = do
      case typeVarContextLookup c (eTypeVarName a) of
        Just (CTypeVar (E _) k) -> if k == k1 then return () else lift . Left $ ETypeVarKindMismatchError p a k k1
        Just (CETypeVar _ k _) -> if k == k1 then return () else lift . Left $ ETypeVarKindMismatchError p a k k1
        _ ->  lift . Left $ UndeclaredETypeVarError p a
      return c
  | otherwise = do
      c2 <- lift $ takeContextToETypeVar a c p
      replaceB <- case typeVarContextLookup c2 (eTypeVarName b) of
        Just (CTypeVar (E _) k) -> if k == k1 then return True else lift . Left $ ETypeVarKindMismatchError p b k k1
        Just (CETypeVar _ k _)  -> if k == k1 then return True else lift . Left $ ETypeVarKindMismatchError p a k k1
        Nothing -> return False
        _ ->  lift . Left $ UndeclaredETypeVarError p b
      if replaceB then
        lift $ eTypeVarContextReplace c b k1 (MEVar a) [] p
      else (do
        c3 <- lift $ dropContextToETypeVar a c p
        checkMonotypeHasKind p c3 (MEVar b) k1
        lift $ eTypeVarContextReplace c a k1 (MEVar b) [] p)
instantiateEVar c a m k p = do
  c2 <- lift $ dropContextToETypeVar a c p
  checkMonotypeHasKind p c2 m k
  lift $ eTypeVarContextReplace c a k m [] p

checkEquationNAry :: Context -> [Monotype] -> [Monotype] -> [Kind] -> p -> StateT TypecheckerState (Either (TypeError p)) Context
checkEquationNAry c [] [] [] _ = return c
checkEquationNAry c (m1 : ms1) (m2 : ms2) (k1 : ks) p = do
  c2 <- checkEquation c m1 m2 k1 p
  foldM aux c2 (((,,) <$> ms1) `z` ms2 `z` ks)
  where
    z = zipWith ($)
    aux _c (ml, mr, k) = do
      ml' <- lift $ applyContextToMonotype p _c ml
      mr' <- lift $ applyContextToMonotype p _c mr
      checkEquation _c ml' mr' k p
checkEquationNAry _ _ _ _ p = lift . Left $ InternalCompilerTypeError p "checkEquationNAry"

checkEquation :: Context -> Monotype -> Monotype -> Kind -> p -> StateT TypecheckerState (Either (TypeError p)) Context
checkEquation c MUnit   MUnit   KStar _ = return c
checkEquation c MBool   MBool   KStar _ = return c
checkEquation c MInt    MInt    KStar _ = return c
checkEquation c MFloat  MFloat  KStar _ = return c
checkEquation c MChar   MChar   KStar _ = return c
checkEquation c MString MString KStar _ = return c
checkEquation c MZero   MZero   KNat  _ = return c
checkEquation c (MUVar a) (MUVar b) k p
  | a == b = return c
  | otherwise = lift . Left $ EquationFalseError p (MUVar a) (MUVar b) k
checkEquation c (MArrow m1 m2) (MArrow n1 n2) KStar p = do
  c2 <- checkEquation c m1 n1 KStar p
  m2' <- lift $ applyContextToMonotype p c2 m2
  n2' <- lift $ applyContextToMonotype p c2 n2
  checkEquation c2 m2' n2' KStar p
checkEquation c (MGADT n1 ms1) (MGADT n2 ms2) KStar p
  | n1 /= n2 = lift . Left $ EquationFalseError p (MGADT n1 ms1) (MGADT n2 ms2) KStar
  | otherwise = do
    ks <- mapM (inferMonotypeKind p c) ms1
    checkEquationNAry c ms1 ms2 ks p
checkEquation c (MProduct ms1 n1) (MProduct ms2 n2) KStar p
  | n1 /= n2 = lift . Left $ EquationFalseError p (MProduct ms1 n1) (MProduct ms2 n2) KStar
  | otherwise = checkEquationNAry c ms1 ms2 (map (const KStar) ms1) p
checkEquation c (MSucc n1) (MSucc n2) KNat p = checkEquation c n1 n2 KNat p
checkEquation c m1 @ (MEVar a) m2 k p
  | m1 == m2 = return c
  | eTypeVarName a `Set.member` freeVariablesOfMonotype m2 = lift . Left $ EquationFalseError p m1 m2 k
  | otherwise = instantiateEVar c a m2 k p
checkEquation c m1 m2 @ (MEVar b) k p
  | eTypeVarName b `Set.member` freeVariablesOfMonotype m1 = lift . Left $ EquationFalseError p m1 m2 k
  | otherwise = instantiateEVar c b m1 k p
checkEquation _ m1 m2 k p = lift . Left $ EquationFalseError p m1 m2 k

checkPropTrue :: Context -> Proposition -> p ->  StateT TypecheckerState (Either (TypeError p)) Context
checkPropTrue c (m1, m2) p = do
  k <- inferMonotypeKind p c m1
  checkEquation c m1 m2 k p

eliminatePropEquation :: Context -> Proposition -> p -> MaybeT (StateT TypecheckerState (Either (TypeError p))) Context
eliminatePropEquation c (m1, m2) p = do
  k <- lift $ inferMonotypeKind p c m1
  eliminateEquation c m1 m2 k p

headConstructorClash :: Monotype -> Monotype -> Bool
headConstructorClash MZero (MSucc _) = True
headConstructorClash (MSucc _) MZero = True
headConstructorClash MZero _ = False
headConstructorClash _ MZero = False
headConstructorClash (MSucc _) _ = False
headConstructorClash _ (MSucc _) = False
headConstructorClash MUnit           MUnit           = False
headConstructorClash MBool           MBool           = False
headConstructorClash MInt            MInt            = False
headConstructorClash MFloat          MFloat          = False
headConstructorClash MChar           MChar           = False
headConstructorClash MString         MString         = False
headConstructorClash (MUVar _)       _               = False
headConstructorClash _               (MUVar _)       = False
headConstructorClash (MEVar _)       _               = False
headConstructorClash _               (MEVar _)       = False
headConstructorClash (MArrow _ _)    (MArrow _ _)    = False
headConstructorClash (MGADT n1 _)    (MGADT n2 _)    = n1 /= n2
headConstructorClash (MProduct _ n1) (MProduct _ n2) = n1 /= n2
headConstructorClash _ _ = True

eliminateEquationNAry :: Context -> [Monotype] -> [Monotype] -> [Kind] -> p -> MaybeT (StateT TypecheckerState (Either (TypeError p))) Context
eliminateEquationNAry c [] [] [] _ = return c
eliminateEquationNAry c (m1 : ms1) (m2 : ms2) (k1 : ks) p = do
  c2 <- eliminateEquation c m1 m2 k1 p
  foldM aux c2 (((,,) <$> ms1) `z` ms2 `z` ks)
  where
    z = zipWith ($)
    aux _c (ml, mr, k) = do
      ml' <- lift . lift $ applyContextToMonotype p _c ml
      mr' <- lift . lift $ applyContextToMonotype p _c mr
      eliminateEquation _c ml' mr' k p
eliminateEquationNAry _ _ _ _ p = lift . lift . Left $ InternalCompilerTypeError p "eliminateEquationNAry"

eliminateEquationOneUVar :: Context -> UTypeVar -> Monotype -> Kind -> p -> MaybeT (StateT TypecheckerState (Either (TypeError p))) Context
eliminateEquationOneUVar c a m _ p
  | MUVar a /= m && uTypeVarName a `Set.member` freeVariablesOfMonotype m = fail "InFreeVars"
  | not $ Set.member (uTypeVarName a) (freeVariablesOfMonotype m) = do
      c2 <- lift . lift $ takeContextToUTypeVar a c p
      case uTypeVarEqContextLookup c2 a of
        Nothing -> return (CUTypeVarEq a m : c)
        Just (CUTypeVarEq _ m') -> lift . lift . Left $ EquationAlreadyExistsError p a m' m
        _ -> lift . lift . Left $ InternalCompilerTypeError p "eliminateEquationOneUVar"
  | otherwise = lift . lift . Left $ InternalCompilerTypeError p "eliminateEquationOneUVar"

eliminateEquation :: Context -> Monotype -> Monotype -> Kind -> p -> MaybeT (StateT TypecheckerState (Either (TypeError p))) Context
eliminateEquation c MUnit   MUnit   KStar _ = return c
eliminateEquation c MInt    MInt    KStar _ = return c
eliminateEquation c MBool   MBool   KStar _ = return c
eliminateEquation c MFloat  MFloat  KStar _ = return c
eliminateEquation c MChar   MChar   KStar _ = return c
eliminateEquation c MString MString KStar _ = return c
eliminateEquation c MZero   MZero   KNat  _ = return c
eliminateEquation c (MSucc n1) (MSucc n2) KNat p = eliminateEquation c n1 n2 KNat p
eliminateEquation c (MArrow a1 a2) (MArrow b1 b2) KStar p = do
  c2 <- eliminateEquation c a1 b1 KStar p
  a2' <- lift . lift $ applyContextToMonotype p c2 a2
  b2' <- lift . lift $ applyContextToMonotype p c2 b2
  eliminateEquation c2 a2' b2' KStar p
eliminateEquation c (MProduct ms1 n1) (MProduct ms2 n2) KStar p
  | n1 /= n2 = fail "Head clash"
  | otherwise = eliminateEquationNAry c ms1 ms2 (map (const KStar) ms1) p
eliminateEquation c (MGADT n1 ms1) (MGADT n2 ms2) KStar p
  | n1 /= n2 = fail "Head clash"
  | otherwise = do
    ks <- lift $ mapM (inferMonotypeKind p c) ms1
    eliminateEquationNAry c ms1 ms2 ks p
eliminateEquation c (MUVar a) (MUVar b) _ p
  | a == b = return c
  | otherwise = do
      c2 <- lift . lift $ takeContextToUTypeVar a c p
      case uTypeVarEqContextLookup c2 a of
        Nothing -> return (CUTypeVarEq a (MUVar b) : c)
        Just (CUTypeVarEq _ m) -> lift . lift . Left $ EquationAlreadyExistsError p a m (MUVar b)
        _ -> lift . lift . Left $ InternalCompilerTypeError p "eliminateEquation"
eliminateEquation c (MUVar a) m k p = eliminateEquationOneUVar c a m k p
eliminateEquation c m (MUVar a) k p = eliminateEquationOneUVar c a m k p
eliminateEquation _ m1 m2 k p
  | headConstructorClash m1 m2 = fail "Head clash"
  | otherwise = lift . lift . Left $ EliminateEquationError p m1 m2 k

inferSpine ::
  Context -> Spine p -> Type -> Principality
  -> StateT TypecheckerState (Either (TypeError p)) (Type, Principality, Context)
inferSpine c [] t pr = return (t, pr, c)
inferSpine c (e : s) (TArrow t1 t2) pr = do
  c2 <- checkExpr c e t1 pr
  t2' <- lift $ applyContextToType (getPos e) c2 t2
  inferSpine c2 s t2' pr
inferSpine c (e : s) (TImp q t) pr = do
  c2 <- checkPropTrue c q $ getPos e
  t' <- lift $ applyContextToType (getPos e) c2 t
  inferSpine c2 (e : s) t' pr
inferSpine c s @ (_ : _) (TUniversal u k t) _ = do
  e <- ETypeVar <$> generateFreshTypeVarName "inferSpine" (uTypeVarName u)
  inferSpine (CTypeVar (E e) k : c) s (substituteUVarInType u (E e) t) NotPrincipal
inferSpine c (e : s) (TEVar a) NotPrincipal = do
  let (a1, a2) = generateSubETypeVars a
  c2 <- lift $ eTypeVarContextReplace c a KStar (MArrow (MEVar a1) (MEVar a2)) [CTypeVar (E a1) KStar, CTypeVar (E a2) KStar] $ getPos e
  inferSpine c2 (e : s) (TArrow (TEVar a1) (TEVar a2)) NotPrincipal
inferSpine _ (e : _) t _ = lift . Left $ SpineInferenceError e t

inferSpineRecoverPrnc ::
  Context -> Spine p -> Type -> Principality
  -> StateT TypecheckerState (Either (TypeError p)) (Type, Principality, Context)
inferSpineRecoverPrnc c s t pr = do
  (t2, pr2, c2) <- inferSpine c s t pr
  if pr == Principal && pr2 == NotPrincipal && null (freeExistentialVariables t2) then
    return (t2, Principal, c2)
  else
    return (t2, pr2, c2)

checkExpr :: Context -> Expr p -> Type -> Principality -> StateT TypecheckerState (Either (TypeError p)) Context
checkExpr context expression checkedType principality =
  case (context, expression, checkedType, principality) of
    (c, EUnit _,     TUnit, _)   -> return c
    (c, EBool _ _,   TBool, _)   -> return c
    (c, EInt _ _,    TInt, _)    -> return c
    (c, EFloat _ _,  TFloat, _)  -> return c
    (c, EChar _ _,   TChar, _)   -> return c
    (c, EString _ _, TString, _) -> return c
    (c, EUnit p,     TEVar a, NotPrincipal) -> lift $ eTypeVarContextReplace c a KStar MUnit   [] p
    (c, EBool p _,   TEVar a, NotPrincipal) -> lift $ eTypeVarContextReplace c a KStar MBool   [] p
    (c, EInt p _,    TEVar a, NotPrincipal) -> lift $ eTypeVarContextReplace c a KStar MInt    [] p
    (c, EFloat p _,  TEVar a, NotPrincipal) -> lift $ eTypeVarContextReplace c a KStar MFloat  [] p
    (c, EChar p _,   TEVar a, NotPrincipal) -> lift $ eTypeVarContextReplace c a KStar MChar   [] p
    (c, EString p _, TEVar a, NotPrincipal) -> lift $ eTypeVarContextReplace c a KStar MString [] p
    (c, EIf p e1 e2 e3, t, pr) -> do
      c2 <- checkExpr c e1 TBool pr
      t' <- lift $ applyContextToType p c2 t
      c3 <- checkExpr c2 e2 t' pr
      t'' <- lift $ applyContextToType p c3 t'
      checkExpr c3 e3 t'' pr
    (c, ELet p x e1 e2, t, pr1) -> do
      (t2, pr2, c2) <- inferExpr c e1
      t' <- lift $ applyContextToType p c2 t
      dropContextToMarker <$> checkExpr (CVar x t2 pr2 : CMarker : c2) e2 t' pr1
    (c, EBinOp p (BinOp opr) e1 e2, t, pr) ->
      checkExpr c (ESpine p (EVar p opr) [e1, e2]) t pr
    (c, EUnOp p UnOpPlus e, t, pr) ->
      checkExpr c (ESpine p (EVar p "+u") [e]) t pr
    (c, EUnOp p UnOpMinus e, t, pr) ->
      checkExpr c (ESpine p (EVar p "-u") [e]) t pr
    (c, EUnOp p UnOpPlusFloat e, t, pr) ->
      checkExpr c (ESpine p (EVar p "+.u") [e]) t pr
    (c, EUnOp p UnOpMinusFloat e, t, pr) ->
      checkExpr c (ESpine p (EVar p "-.u") [e]) t pr
    (c, EUnOp p UnOpNot e, t, pr) ->
      checkExpr c (ESpine p (EVar p "!u") [e]) t pr
    (c, ECase p e bs, t1, pr1) -> do
      (t2, pr2, c2) <- inferExpr c e
      t1' <- lift $ applyContextToType p c2 t1
      t2' <- lift $ applyContextToType p c2 t2
      c3 <- checkBranches c2 bs [t2'] pr2 t1' pr1
      t2'' <- lift $ applyContextToType p c3 t2'
      checkCoverage p c3 bs [t2''] pr2
      return c3
    (c, e, TUniversal a k t, pr) | checkedIntroductionForm e ->
      dropContextToMarker <$> checkExpr (CTypeVar (U a) k : CMarker : c) e t pr
    (c, e, TExistential a k t, _) | checkedIntroductionForm e -> do
      a' <- ETypeVar <$> generateFreshTypeVarName "checkExpr" (uTypeVarName a)
      checkExpr (CTypeVar (E  a') k : c) e (substituteUVarInType a (E a') t) NotPrincipal
    (c, e, TImp prop t, Principal) | checkedIntroductionForm e -> do
      contextOrContradiction <- runMaybeT $ eliminatePropEquation (CMarker : c) prop $ getPos e
      case contextOrContradiction of
        Nothing -> return c
        Just c2 -> do
          t' <- lift $ applyContextToType (getPos e) c2 t
          dropContextToMarker <$> checkExpr c2 e t' Principal
    (c, e, TAnd t prop, pr) | exprIsNotACase e -> do
      c2 <- checkPropTrue c prop $ getPos e
      t' <- lift $ applyContextToType (getPos e) c2 t
      checkExpr c2 e t' pr
    (c, ELambda _ x e, TArrow t1 t2, pr) -> do
      c2 <- checkExpr (CVar x t1 pr : CMarker : c) e t2 pr
      return $ dropContextToMarker c2
    (c, ELambda p x e, TEVar a, NotPrincipal) -> do
      let (a1, a2) = generateSubETypeVars a
      c2 <- lift $ eTypeVarContextReplace c a KStar (MArrow (MEVar a1) (MEVar a2)) [CTypeVar (E a1) KStar, CTypeVar (E a2) KStar] p
      c3 <- checkExpr (CVar x (TEVar a1) NotPrincipal : CMarker : c2) e (TEVar a2) NotPrincipal
      return $ dropContextToMarker c3
    (c, ETuple p (e1 : es) n1, TProduct (t1 : ts) n2, pr) ->
      if n1 /= n2 then
        lift . Left $ ProductArityError (ETuple p (e1 : es) n1) (TProduct (t1 : ts) n2)
      else do
        c2 <- checkExpr c e1 t1 pr
        foldM aux c2 $ zip es ts
      where
        aux _c (e, t) = do
          t' <- lift $ applyContextToType p _c t
          checkExpr _c e t' pr
    (c, ETuple p (e1 : es) n, TEVar a, NotPrincipal) -> do
      let a1 : as = generateSubETypeVarsList a n
      c2 <- lift $ eTypeVarContextReplace c a KStar (MProduct (map MEVar (a1 : as)) n) (map (flip CTypeVar KStar . E) $ a1 : as) p
      c3 <- checkExpr c2 e1 (TEVar a1) NotPrincipal
      foldM aux c3 $ zip es $ map TEVar as
      where
        aux _c (e, t) = do
          t' <- lift $ applyContextToType p _c t
          checkExpr _c e t' NotPrincipal
    (c, EConstr p constrName es, TGADT typeName ts, pr) -> do
      lookupRes <- Map.lookup constrName . view constrContext <$> get
      case lookupRes of
        Nothing -> lift . Left $ UndeclaredConstructorError (EConstr p constrName es) constrName
        Just constr
          | constrTypeName constr /= typeName ->
            lift . Left $ MismatchedConstructorError (EConstr p constrName es) (constrTypeName constr) typeName
          | length (constrArgsTemplates constr) /= length es ->
            lift . Left $ MismatchedConstructorArityError (EConstr p constrName es) constrName (length $ constrArgsTemplates constr) (length es)
          | otherwise -> do
            evars <- generateFreshTypeVars (E . ETypeVar) "checkExpr" (map (uTypeVarName . fst) (constrUVars constr))
            let tsMap = Map.fromList (zip (constrTypeParmsTemplate constr) ts)
            let uvarsToFreshEvars = zip (map fst (constrUVars constr)) evars
            let tArgs = map (flip (foldl (flip $ uncurry substituteUVarInTypeTemplate)) uvarsToFreshEvars) $ constrArgsTemplates constr
            let tProps = map (flip (foldl (flip $ uncurry substituteUVarInPropTemplate)) uvarsToFreshEvars) $ constrProps constr
            args <- lift $ mapM (typeFromTemplate tsMap p) tArgs
            props <- lift $ mapM (propositionFromTemplate tsMap p) tProps
            let c2 = zipWith CTypeVar evars (map snd $ constrUVars constr) ++ CMarker : c
            c3 <- foldM auxProp c2 props
            dropContextToMarker <$> foldM auxType c3 (zip es args)
      where
        auxProp _c prop = do
          prop' <- lift $ applyContextToProposition p _c prop
          checkPropTrue _c prop' p
        auxType _c (e, t) = do
          t' <- lift $ applyContextToType p _c t
          checkExpr _c e t' pr
    (c, ENil p, TVec n _, _) -> checkPropTrue c (n, MZero) p
    (c, ECons p e1 e2, TVec n t, pr) -> do
      a <- ETypeVar <$> generateFreshTypeVarName "checkExpr" ""
      c2 <- checkPropTrue (CTypeVar (E a) KNat : CMarker : c) (n, MSucc (MEVar a)) p
      t' <- lift $ applyContextToType p c2 t
      c3 <- checkExpr c2 e1 t' pr
      t'' <- lift $ applyContextToType p c2 (TVec (MEVar a) t)
      dropContextToMarker <$> checkExpr c3 e2 t'' pr
    (c, e, t, _) -> do
      (t2, _, c2) <- inferExpr c e
      subtype c2 t2 (joinPolarity (polarity t) (polarity t2)) t $ getPos e

inferExpr :: Context -> Expr p -> StateT TypecheckerState (Either (TypeError p)) (Type, Principality, Context)
inferExpr c (ERec _ _ e) = inferExpr c e
inferExpr c (ETuple _ es n) = do
  (ts, pr, c') <- foldM aux ([], Principal, c) es
  return (TProduct (reverse ts) n, pr, c')
  where
    aux (ts, pr1, c1) e = do
      (t, pr2, c2) <- inferExpr c1 e
      return (t : ts, pr1 `prncAnd` pr2, c2)
    prncAnd Principal Principal = Principal
    prncAnd _ _ = NotPrincipal
inferExpr c (EVar p x) = do
  (CVar _ t pr) <- varContextLookup c x p
  t2 <- lift $ applyContextToType p c t
  return (t2, pr, c)
inferExpr c (EAnnot p e t) = do
  checkTypeWellFormednessWithPrnc p c t Principal
  t2 <- lift $ applyContextToType p c t
  c2 <- checkExpr c e t2 Principal
  t3 <- lift $ applyContextToType p c2 t2
  return (t3, Principal, c2)
inferExpr c (EConstr p constrName es) = do
    lookupRes <- Map.lookup constrName . view constrContext <$> get
    case lookupRes of
      Nothing -> lift . Left $ UndeclaredConstructorError (EConstr p constrName es) constrName
      Just constr -> inferSpineRecoverPrnc c es (constrFunVersion constr) Principal
inferExpr c (ESpine _ e s) = do
  (t, pr, c2) <- inferExpr c e
  inferSpineRecoverPrnc c2 s t pr
inferExpr _ e = lift . Left $ TypeInferenceError e

checkBranches ::
  Context -> [Branch p] -> [Type] -> Principality -> Type -> Principality
  -> StateT TypecheckerState (Either (TypeError p)) Context
checkBranches c [] _ _ _ _ = return c
checkBranches c (b : bs) ts pr1 t pr2 = do
  lift $ checkBranchWellFormedness b
  c2 <- checkBranch c b ts pr1 t pr2
  ts' <- mapM (lift . applyContextToType (getPosFromBranch b) c2) ts
  checkBranches c2 bs ts' pr1 t pr2

checkBranch ::
  Context -> Branch p -> [Type] -> Principality -> Type -> Principality
  -> StateT TypecheckerState (Either (TypeError p)) Context
checkBranch c ([], e, _) [] _ te pr = checkExpr c e te pr
checkBranch _ ([], _, p) _ _ _ _ = lift . Left $ TooShortPatternError p
checkBranch _ (_, _, p) [] _ _ _ = lift . Left $ TooLongPatternError p
checkBranch c b (TAnd t _ : ts) NotPrincipal te pr = checkBranch c b (t : ts) NotPrincipal te pr
checkBranch c b (TAnd t prop : ts) Principal te pr =
  checkBranchIncorporatingProps (getPosFromBranch b) c [prop] b (t : ts) Principal te pr
checkBranch c b (TExistential u k t : ts) pr1 te pr2 =
  dropContextToMarker <$> checkBranch (CTypeVar (U u) k : CMarker : c) b (t : ts) pr1 te pr2
checkBranch c (PUnit   _   : ptrns, e, p) (TUnit : ts)   pr1 te pr2 = checkBranch c (ptrns, e, p) ts pr1 te pr2
checkBranch c (PBool   _ _ : ptrns, e, p) (TBool : ts)   pr1 te pr2 = checkBranch c (ptrns, e, p) ts pr1 te pr2
checkBranch c (PInt    _ _ : ptrns, e, p) (TInt  : ts)   pr1 te pr2 = checkBranch c (ptrns, e, p) ts pr1 te pr2
checkBranch c (PFloat  _ _ : ptrns, e, p) (TFloat : ts)  pr1 te pr2 = checkBranch c (ptrns, e, p) ts pr1 te pr2
checkBranch c (PChar   _ _ : ptrns, e, p) (TChar: ts)    pr1 te pr2 = checkBranch c (ptrns, e, p) ts pr1 te pr2
checkBranch c (PString _ _ : ptrns, e, p) (TString : ts) pr1 te pr2 = checkBranch c (ptrns, e, p) ts pr1 te pr2
checkBranch c (PTuple p1 pargs n1 : ptrns, e, p2) (TProduct targs n2 : ts) pr1 te pr2
  | n1 /= n2 = lift . Left $ MismatchedProductArityInPatternError (PTuple p1 pargs n1) (TProduct targs n2)
  | otherwise = checkBranch c (pargs ++ ptrns, e, p2) (targs ++ ts) pr1 te pr2
checkBranch c (PWild _ : ptrns, e, p) (_ : ts) pr1 te pr2 = checkBranch c (ptrns, e, p) ts pr1 te pr2
checkBranch c (PVar _ x : ptrns, e, p) (t : ts) pr1 te pr2 =
  dropContextToMarker <$> checkBranch (CVar x t Principal : CMarker : c) (ptrns, e, p) ts pr1 te pr2
checkBranch c (PNil _ : ptrns, e, p) (TVec {} : ts) NotPrincipal te pr =
  checkBranch c (ptrns, e, p) ts NotPrincipal te pr
checkBranch c (PCons _ x xs : ptrns, e, p) (TVec _ t : ts) NotPrincipal te pr = do
  n <- UTypeVar <$> generateFreshTypeVarName "checkBranch" ""
  let c2 = CTypeVar (U n) KNat : CMarker : c
  dropContextToMarker <$> checkBranch c2 (x : xs : ptrns, e, p) (t : TVec (MUVar n) t : ts) NotPrincipal te pr
checkBranch c (PNil p1 : ptrns, e, p2) (TVec n _ : ts) Principal te pr =
  checkBranchIncorporatingProps p1 c [(n, MZero)] (ptrns, e, p2) ts Principal te pr
checkBranch c (PCons p1 x xs : ptrns, e, p2) (TVec n1 t : ts) Principal te pr = do
  n2 <- UTypeVar <$> generateFreshTypeVarName "checkBranch" ""
  let c2 = CTypeVar (U n2) KNat : CMarker : c
  let prop = (n1, MSucc $ MUVar n2)
  let b = (x : xs : ptrns, e, p2)
  let ts' = t : TVec (MUVar n2) t : ts
  dropContextToMarker <$> checkBranchIncorporatingProps p1 c2 [prop] b ts' Principal te pr
checkBranch c (PConstr p1 constrName pargs : ptrns, e, p2) (TGADT typeName params : ts) pr1 te pr2 = do
  lookupRes <- Map.lookup constrName . view constrContext <$> get
  case lookupRes of
    Nothing -> lift . Left $ UndeclaredConstructorInPatternError (PConstr p1 constrName pargs) constrName
    Just constr
      | constrTypeName constr /= typeName ->
        lift . Left $ MismatchedConstructorInPatternError (PConstr p1 constrName pargs) (constrTypeName constr) typeName
      | length (constrArgsTemplates constr) /= length pargs ->
        lift . Left $ MismatchedConstructorArityInPatternError
        (PConstr p1 constrName pargs) constrName
        (length $ constrArgsTemplates constr) (length pargs)
      | otherwise -> do
        uvars <- generateFreshTypeVars (U . UTypeVar) "checkBranch" (map (uTypeVarName . fst) (constrUVars constr))
        let paramsMap = Map.fromList (zip (constrTypeParmsTemplate constr) params)
        let uvarsToFreshUvars = zip (map fst (constrUVars constr)) uvars
        let tArgs = map (flip (foldl (flip $ uncurry substituteUVarInTypeTemplate)) uvarsToFreshUvars) $ constrArgsTemplates constr
        let tProps = map (flip (foldl (flip $ uncurry substituteUVarInPropTemplate)) uvarsToFreshUvars) $ constrProps constr
        args <- lift $ mapM (typeFromTemplate paramsMap p1) tArgs
        props <- lift $ mapM (propositionFromTemplate paramsMap p1) tProps
        let c2 = zipWith CTypeVar uvars (map snd $ constrUVars constr) ++ CMarker : c
        case pr1 of
          NotPrincipal -> dropContextToMarker <$> checkBranch c2 (pargs ++ ptrns, e, p2) (args ++ ts) pr1 te pr2
          Principal -> dropContextToMarker <$> checkBranchIncorporatingProps p1 c2 props (pargs ++ ptrns, e, p2) (args ++ ts) pr1 te pr2
checkBranch _ (ptrn : _, _, _) (t : _) _ _ _ = lift . Left $ PatternMatchingTypecheckingError ptrn t

checkBranchIncorporatingProps ::
 p -> Context -> [Proposition] -> Branch p -> [Type] -> Principality -> Type -> Principality
 -> StateT TypecheckerState (Either (TypeError p)) Context
checkBranchIncorporatingProps _ c [] b ts Principal te pr =
  checkBranch c b ts Principal te pr
checkBranchIncorporatingProps p c (prop : props) b ts Principal te pr = do
  unificationResult <- runMaybeT $ eliminatePropEquation (CMarker : c) prop p
  case unificationResult of
    Nothing -> return c
    Just c2 -> do
      ts' <- mapM (lift . applyContextToType (getPosFromBranch b) c2) ts
      dropContextToMarker <$> checkBranchIncorporatingProps p c2 props b ts' Principal te pr
checkBranchIncorporatingProps p _ _ _ _ NotPrincipal _ _ = lift . Left $ InternalCompilerTypeError p "checkBranchIncorporatingProps"

checkCoverage ::
  p -> Context -> [Branch p] -> [Type] -> Principality
  -> StateT TypecheckerState (Either (TypeError p)) ()
checkCoverage _ _ (([], _, _) : _) [] _ = return ()
checkCoverage p c bs (TUnit : ts) pr = do
  bs' <- expandUnitPatterns bs
  checkCoverage p c bs' ts pr
checkCoverage p c bs (TBool : ts) pr = do
  (falsePtrns, truePtrns) <- expandBoolPatterns bs
  checkCoverage p c falsePtrns ts pr
  checkCoverage p c truePtrns ts pr
checkCoverage p c bs (TInt : ts) pr = do
  bs' <- expandIntPatterns bs
  checkCoverage p c bs' ts pr
checkCoverage p c bs (TFloat : ts) pr = do
  bs' <- expandFloatPatterns bs
  checkCoverage p c bs' ts pr
checkCoverage p c bs (TChar : ts) pr = do
  bs' <- expandCharPatterns bs
  checkCoverage p c bs' ts pr
checkCoverage p c bs (TString : ts) pr = do
  bs' <- expandStringPatterns bs
  checkCoverage p c bs' ts pr
checkCoverage p c bs (TProduct args n : ts) pr = do
  bs' <- expandTuplePatterns n bs
  checkCoverage p c bs' (args ++ ts) pr
checkCoverage p c bs (TExistential a k t : ts) pr =
  checkCoverage p (CTypeVar (U a) k : c) bs (t : ts) pr
checkCoverage p c bs (TAnd t _ : ts) NotPrincipal =
  checkCoverage p c bs (t : ts) NotPrincipal
checkCoverage p c bs (TAnd t prop : ts) Principal =
  checkCoverageAssumingProps p c [prop] bs (t : ts) Principal
checkCoverage p c bs (TVec n1 t : ts) pr = do
  guarded <- vecPatternsGuarded bs
  if guarded then do
    (nilPtrns, consPtrns) <- expandVecPatterns bs
    n2 <- UTypeVar <$> generateFreshTypeVarName "checkCoverage" ""
    case pr of
      NotPrincipal -> do
        checkCoverage p c nilPtrns ts pr
        checkCoverage p (CTypeVar (U n2) KNat : c) consPtrns (t : TVec (MUVar n2) t : ts) pr
      Principal -> do
        checkCoverageAssumingProps p c [(n1, MZero)] nilPtrns ts pr
        let props = [(n1, MSucc $ MUVar n2)]
        let ts' = t : TVec (MUVar n2) t : ts
        checkCoverageAssumingProps p (CTypeVar (U n2) KNat : c) props consPtrns ts' pr
  else do
    bs' <- expandVarPatterns bs
    checkCoverage p c bs' ts pr
checkCoverage p c bs (TGADT typeName params : ts) pr = do
  guarded <- gadtPatternsGuarded typeName bs
  if guarded then do
    ptrns <- Map.toList <$> expandGADTPatterns typeName bs
    iterM (checkConstrCoverage p c params ts pr) ptrns
  else do
    bs' <- expandVarPatterns bs
    checkCoverage p c bs' ts pr
checkCoverage p c bs (_ : ts) pr = do
  bs' <- expandVarPatterns bs
  checkCoverage p c bs' ts pr
checkCoverage p _ _ _ _ = lift . Left $ PatternMatchingNonExhaustiveError p

checkConstrCoverage ::
  p -> Context -> [GADTParameter] -> [Type] -> Principality
  -> (String, [Branch p]) -> StateT TypecheckerState (Either (TypeError p)) ()
checkConstrCoverage p c params ts pr (constrName, bs) = do
  lookupRes <- Map.lookup constrName . view constrContext <$> get
  case lookupRes of
    Nothing -> lift . Left $ InternalCompilerTypeError p "checkConstrCoverage"
    Just constr -> do
      uvars <- generateFreshTypeVars (U . UTypeVar) "checkConstrCoverage" (map (uTypeVarName . fst) (constrUVars constr))
      let paramsMap = Map.fromList (zip (constrTypeParmsTemplate constr) params)
      let uvarsToFreshUvars = zip (map fst (constrUVars constr)) uvars
      let tArgs = map (flip (foldl (flip $ uncurry substituteUVarInTypeTemplate)) uvarsToFreshUvars) $ constrArgsTemplates constr
      let tProps = map (flip (foldl (flip $ uncurry substituteUVarInPropTemplate)) uvarsToFreshUvars) $ constrProps constr
      args <- lift $ mapM (typeFromTemplate paramsMap p) tArgs
      props <- lift $ mapM (propositionFromTemplate paramsMap p) tProps
      let c2 = zipWith CTypeVar uvars (map snd $ constrUVars constr) ++ c
      case pr of
        NotPrincipal -> checkCoverage p c2 bs (args ++ ts) pr
        Principal -> checkCoverageAssumingProps p c2 props bs(args ++ ts) pr

checkCoverageAssumingProps ::
   p -> Context -> [Proposition] -> [Branch p] -> [Type] -> Principality
  -> StateT TypecheckerState (Either (TypeError p)) ()
checkCoverageAssumingProps p c [] bs ts Principal = checkCoverage p c bs ts Principal
checkCoverageAssumingProps p c ((m1, m2) : props) bs ts Principal = do
  m1' <- lift $ applyContextToMonotype p c m1
  m2' <- lift $ applyContextToMonotype p c m2
  unificationResult <- runMaybeT $ eliminatePropEquation c (m1', m2') p
  case unificationResult of
    Nothing -> return ()
    Just c2 -> do
      ts' <- mapM (lift . applyContextToType p c2) ts
      checkCoverageAssumingProps p c2 props bs ts' Principal
checkCoverageAssumingProps p _ _ _ _ NotPrincipal = lift . Left $ InternalCompilerTypeError p "checkCoverageAssumingProps"
