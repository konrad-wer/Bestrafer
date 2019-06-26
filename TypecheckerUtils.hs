{-# LANGUAGE TemplateHaskell #-}

module TypecheckerUtils where

import AST
import CommonUtils
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Lens hiding (Context)
import Control.Monad.State

data Error p
  = UndeclaredVariableError p Var
  | UndeclaredGADTError p String
  | UndeclaredConstructorError (Expr p)
  | MismatchedGADTArityError p String Int Int
  | MismatchedConstructorError (Expr p) String String
  | MismatchedConstructorArityError (Expr p) Int Int
  | InternalCompilerError p String
  | ETypeVarTypeMismatchError p ETypeVar Monotype Monotype
  | ETypeVarKindMismatchError p ETypeVar Kind Kind
  | UndeclaredETypeVarError p ETypeVar
  | UndeclaredUTypeVarError p UTypeVar
  | TypeHasWrongKindError p Type Kind Kind
  | MonotypeHasWrongKindError p Monotype Kind Kind
  | MonotypeIsNotTypeError p Monotype
  | TypeIsNotMonotypeError p Type
  | TypeFormednessPrcFEVError p [ETypeVar]
  | TypesNotEquivalentError p Type Type
  | EquationFalseError p Monotype Monotype Kind
  | NotSubtypeError p Type Type
  | TypecheckingError (Expr p) Type
  | InjIndexOutOfBoundError (Expr p) Type
  | SpineInferenceError p Type
  | TypeInferenceError (Expr p)
  | EquationAlreadyExistsError p UTypeVar Monotype Monotype
  | EliminateEquationError p Monotype Monotype Kind
  | ExprNotCheckedIntroductionFormError (Expr p)
  | ExprIsACaseError (Expr p)
  | TooLongPatternError p
  | TooShortPatternError p
  | MismatchedProductArityInPatternError (Pattern p) Type
  | VarPatternHeadedByExistsOrAndError (Pattern p) Type
  | ExpectedPrincipalTypeInPatternError (Branch p)
  | UndeclaredConstructorInPatternError (Pattern p)
  | MismatchedConstructorInPatternError (Pattern p) String String
  | MismatchedConstructorArityInPatternError (Pattern p) Int Int
  | PatternMatchingTypecheckingError (Pattern p) Type
  | PatternTypeError String (Pattern p)
  | NotConstructorOfError (Pattern p) String
  | ExpectedPrincipalTypeInCoverageError p
  | PatternMatchingNonExhaustive p
  deriving (Show)

data TypecheckerState = TypecheckerState {_freshVarNum :: Integer, _constrContext :: ConstructorsContext, _gadtArities :: GADTArities}

makeLenses ''TypecheckerState

--simple utils------------------------------------------------------------------

generateSubETypeVars :: ETypeVar -> (ETypeVar, ETypeVar)
generateSubETypeVars a = (ETypeVar $ eTypeVarName a ++ "-1", ETypeVar $ eTypeVarName a ++ "-2")

generateSubETypeVarsList :: ETypeVar -> Int -> [ETypeVar]
generateSubETypeVarsList a n = [ETypeVar $ eTypeVarName a ++ "-" ++ show k | k <- [1..n]]

generateFreshTypeVars :: (String -> TypeVar) -> Integer -> StateT TypecheckerState (Either (Error p)) [TypeVar]
generateFreshTypeVars f n = do
   firstFreshVarNum <- view freshVarNum <$> get
   modify $ over freshVarNum (+ n)
   return $ map (f . ("#" ++) . show) [firstFreshVarNum .. firstFreshVarNum + n]

--exprUtils---------------------------------------------------------------------

exprIsNotACase :: Expr p -> Either (Error p) ()
exprIsNotACase e @ ECase {} = Left $ ExprIsACaseError e
exprIsNotACase _ = return ()

--polarity utils----------------------------------------------------------------

polarity :: Type -> Polarity
polarity TUniversal {} = Negative
polarity TExistential {} = Positive
polarity _ = Neutral

pos :: Polarity -> Bool
pos Positive = True
pos _ = False

neg :: Polarity -> Bool
neg Negative = True
neg _ = False

nonpos :: Polarity -> Bool
nonpos Positive = False
nonpos _ = True

nonneg :: Polarity -> Bool
nonneg Negative = False
nonneg _ = True

joinPolarity :: Polarity -> Polarity -> Polarity
joinPolarity Positive _ = Positive
joinPolarity Negative _ = Negative
joinPolarity Neutral Positive = Positive
joinPolarity Neutral Negative = Negative
joinPolarity Neutral Neutral = Negative

headedByUniversal :: Type -> Bool
headedByUniversal TUniversal {} = True
headedByUniversal _ = False

headedByExistential :: Type -> Bool
headedByExistential TExistential {} = True
headedByExistential _ = False

headedByAnd :: Type -> Bool
headedByAnd TAnd {} = True
headedByAnd _ = False

--TemplateUtils-----------------------------------------------------------------

typeFromGADTParameterTemplate :: [GADTParameter] -> p -> GADTParameterTemplate -> Either (Error p) GADTParameter
typeFromGADTParameterTemplate prms p (ParameterTypeT tt)     = ParameterType     <$> typeFromTemplate prms p tt
typeFromGADTParameterTemplate prms p (ParameterMonotypeT mt) = ParameterMonotype <$> monotypeFromTemplate prms p mt

typeFromTemplate :: [GADTParameter] -> p -> TypeTemplate -> Either (Error p) Type
typeFromTemplate _ _ TTUnit   = return TUnit
typeFromTemplate _ _ TTBool   = return TBool
typeFromTemplate _ _ TTInt    = return TInt
typeFromTemplate _ _ TTFloat  = return TFloat
typeFromTemplate _ _ TTChar   = return TChar
typeFromTemplate _ _ TTString = return TString
typeFromTemplate prms p (TTArrow tt1 tt2) = TArrow   <$> typeFromTemplate prms p tt1 <*> typeFromTemplate prms p tt2
typeFromTemplate prms p (TTGADT n tts)    = TGADT n  <$> mapM (typeFromGADTParameterTemplate prms p) tts
typeFromTemplate prms p (TTProduct tts n) = TProduct <$> mapM (typeFromTemplate prms p) tts <*> return n
typeFromTemplate _ _    (TTUVar u) = return $ TUVar u
typeFromTemplate _ _    (TTEVar e) = return $ TEVar e
typeFromTemplate prms p (TTUniversal u k tt)   = TUniversal u k    <$> typeFromTemplate prms p tt
typeFromTemplate prms p (TTExistential u k tt) = TExistential u k  <$> typeFromTemplate prms p tt
typeFromTemplate prms p (TTImp pt tt) = TImp <$> propositionFromTemplate prms p pt <*> typeFromTemplate prms p tt
typeFromTemplate prms p (TTAnd tt pt) = TAnd <$> typeFromTemplate prms p tt <*> propositionFromTemplate prms p pt
typeFromTemplate prms p (TTVec nt tt) = TVec <$> monotypeFromTemplate prms p nt <*> typeFromTemplate prms p tt
typeFromTemplate prms p (TTParam i) =
  case prms !! i of
    ParameterType t -> return t
    ParameterMonotype m -> monotypeToType p m

propositionFromTemplate :: [GADTParameter] -> p -> PropositionTemplate -> Either (Error p) Proposition
propositionFromTemplate prms p (pt1, pt2) = do
  p1 <- monotypeFromTemplate prms p pt1
  p2 <- monotypeFromTemplate prms p pt2
  return (p1, p2)

monotypeFromTemplate :: [GADTParameter] -> p -> MonotypeTemplate -> Either (Error p) Monotype
monotypeFromTemplate _ _ MTUnit     = return MUnit
monotypeFromTemplate _ _ MTBool     = return MBool
monotypeFromTemplate _ _ MTInt      = return MInt
monotypeFromTemplate _ _ MTFloat    = return MFloat
monotypeFromTemplate _ _ MTChar     = return MChar
monotypeFromTemplate _ _ MTString   = return MString
monotypeFromTemplate _ _ MTZero     = return MZero
monotypeFromTemplate _ _ (MTUVar u) = return $ MUVar u
monotypeFromTemplate _ _ (MTEVar e) = return $ MEVar e
monotypeFromTemplate prms p (MTSucc n)        = MSucc    <$> monotypeFromTemplate prms p n
monotypeFromTemplate prms p (MTArrow tt1 tt2) = MArrow   <$> monotypeFromTemplate prms p tt1 <*> monotypeFromTemplate prms p tt2
monotypeFromTemplate prms p (MTGADT n tts)    = MGADT n  <$> mapM (monotypeFromTemplate prms p) tts
monotypeFromTemplate prms p (MTProduct tts n) = MProduct <$> mapM (monotypeFromTemplate prms p) tts <*> return n
monotypeFromTemplate prms p (MTParam i) =
  case prms !! i of
    ParameterType t -> typeToMonotype p t
    ParameterMonotype m -> return m

--Free variables computing utils -----------------------------------------------

freeExistentialVariablesOfGADTParameter :: GADTParameter -> Set.Set ETypeVar
freeExistentialVariablesOfGADTParameter (ParameterType t)     = freeExistentialVariables t
freeExistentialVariablesOfGADTParameter (ParameterMonotype m) = freeExistentialVariablesOfMonotype m

freeExistentialVariables :: Type -> Set.Set ETypeVar
freeExistentialVariables TUnit   = Set.empty
freeExistentialVariables TBool   = Set.empty
freeExistentialVariables TInt    = Set.empty
freeExistentialVariables TFloat  = Set.empty
freeExistentialVariables TChar   = Set.empty
freeExistentialVariables TString = Set.empty
freeExistentialVariables (TArrow t1 t2)  = Set.union (freeExistentialVariables t1) (freeExistentialVariables t2)
freeExistentialVariables (TGADT _ ts)    = Set.unions $ map freeExistentialVariablesOfGADTParameter ts
freeExistentialVariables (TProduct ts _) = Set.unions $ map freeExistentialVariables ts
freeExistentialVariables (TUVar _) = Set.empty
freeExistentialVariables (TEVar x) = Set.singleton x
freeExistentialVariables (TUniversal _ _ t) = freeExistentialVariables t
freeExistentialVariables (TExistential x _ t) = Set.delete (ETypeVar $ uTypeVarName x) $ freeExistentialVariables t
freeExistentialVariables (TImp p t) = Set.union (freeExistentialVariablesOfProp p) (freeExistentialVariables t)
freeExistentialVariables (TAnd t p) = Set.union (freeExistentialVariables t) (freeExistentialVariablesOfProp p)
freeExistentialVariables (TVec n t) = Set.union (freeExistentialVariablesOfMonotype n) (freeExistentialVariables t)

freeExistentialVariablesOfProp :: Proposition -> Set.Set ETypeVar
freeExistentialVariablesOfProp (m1, m2) = Set.union (freeExistentialVariablesOfMonotype m1) (freeExistentialVariablesOfMonotype m2)

freeExistentialVariablesOfMonotype :: Monotype -> Set.Set ETypeVar
freeExistentialVariablesOfMonotype MUnit   = Set.empty
freeExistentialVariablesOfMonotype MBool   = Set.empty
freeExistentialVariablesOfMonotype MInt    = Set.empty
freeExistentialVariablesOfMonotype MFloat  = Set.empty
freeExistentialVariablesOfMonotype MChar   = Set.empty
freeExistentialVariablesOfMonotype MString = Set.empty
freeExistentialVariablesOfMonotype MZero   = Set.empty
freeExistentialVariablesOfMonotype (MSucc n) = freeExistentialVariablesOfMonotype n
freeExistentialVariablesOfMonotype (MArrow m1 m2)  = Set.union  (freeExistentialVariablesOfMonotype m1) (freeExistentialVariablesOfMonotype m2)
freeExistentialVariablesOfMonotype (MGADT _ ms)    = Set.unions $ map freeExistentialVariablesOfMonotype ms
freeExistentialVariablesOfMonotype (MProduct ms _) = Set.unions $ map freeExistentialVariablesOfMonotype ms
freeExistentialVariablesOfMonotype (MUVar _) = Set.empty
freeExistentialVariablesOfMonotype (MEVar x) = Set.singleton x

freeVariablesOfMonotype :: Monotype -> Set.Set Var
freeVariablesOfMonotype MUnit   = Set.empty
freeVariablesOfMonotype MBool   = Set.empty
freeVariablesOfMonotype MInt    = Set.empty
freeVariablesOfMonotype MFloat  = Set.empty
freeVariablesOfMonotype MChar   = Set.empty
freeVariablesOfMonotype MString = Set.empty
freeVariablesOfMonotype MZero   = Set.empty
freeVariablesOfMonotype (MSucc n) = freeVariablesOfMonotype n
freeVariablesOfMonotype (MArrow m1 m2)  = Set.union  (freeVariablesOfMonotype m1) (freeVariablesOfMonotype m2)
freeVariablesOfMonotype (MGADT _ ms)    = Set.unions $ map freeVariablesOfMonotype ms
freeVariablesOfMonotype (MProduct ms _) = Set.unions $ map freeVariablesOfMonotype ms
freeVariablesOfMonotype (MUVar x) = Set.singleton $ uTypeVarName x
freeVariablesOfMonotype (MEVar x) = Set.singleton $ eTypeVarName x

--Context utils-----------------------------------------------------------------

varContextLookup :: Context -> Var -> p -> Either (Error p) ContextEntry
varContextLookup  (entry @ (CVar y _ _): c) x p
  | x == y = return entry
  | otherwise = varContextLookup c x p
varContextLookup (_ : c) x p = varContextLookup c x p
varContextLookup [] x p = Left $ UndeclaredVariableError p x

uTypeVarEqContextLookup :: Context -> UTypeVar -> Maybe ContextEntry
uTypeVarEqContextLookup (entry @ (CUTypeVarEq b _) : c) a
  | a == b = return entry
  | otherwise = uTypeVarEqContextLookup c a
uTypeVarEqContextLookup (CTypeVar (U b) _ : c) a
  | a == b = Nothing
  | otherwise = uTypeVarEqContextLookup c a
uTypeVarEqContextLookup (CTypeVar (E b) _ : c) a
  | uTypeVarName a == eTypeVarName b = Nothing
  | otherwise = uTypeVarEqContextLookup c a
uTypeVarEqContextLookup (_ : c) a = uTypeVarEqContextLookup c a
uTypeVarEqContextLookup [] _ = Nothing

typeVarContextLookup :: Context -> Var -> Maybe ContextEntry
typeVarContextLookup (entry @ (CETypeVar e _ _) : c) a
  | a == eTypeVarName e = return entry
  | otherwise = typeVarContextLookup c a
typeVarContextLookup (entry @ (CTypeVar (E e) _) : c) a
  | a == eTypeVarName e = return entry
  | otherwise = typeVarContextLookup c a
typeVarContextLookup (entry @ (CTypeVar (U u) _) : c) a
  | a == uTypeVarName u = return entry
  | otherwise = typeVarContextLookup c a
typeVarContextLookup (_ : c) a = typeVarContextLookup c a
typeVarContextLookup [] _ = Nothing

eTypeVarContextReplace :: Context -> ETypeVar -> Kind -> Monotype -> [ContextEntry] -> p -> Either (Error p) Context
eTypeVarContextReplace c @ (entry @ (CETypeVar b k2 tau) : ct) a k1 sigma extraEntries p
  | a == b && k1 == k2 && tau == sigma = return c
  | a == b && k1 /= k2 = Left $ ETypeVarKindMismatchError p a k2 k1
  | a == b && tau /= sigma = Left $ ETypeVarTypeMismatchError p a tau sigma
  | otherwise = (:) entry <$> eTypeVarContextReplace ct a k1 sigma extraEntries p
eTypeVarContextReplace (entry @  (CTypeVar (E b) k2) : ct) a k1 sigma extraEntries p
  | a == b && k1 == k2 = return $ CETypeVar a k1 sigma : extraEntries ++ ct
  | a == b && k1 /= k2 = Left $ ETypeVarKindMismatchError p a k2 k1
  | otherwise = (:) entry <$> eTypeVarContextReplace ct a k1 sigma extraEntries p
eTypeVarContextReplace (entry @  (CTypeVar (U (UTypeVar b)) _) : ct) (ETypeVar a) k sigma extraEntries p
  | a == b = Left $ UndeclaredETypeVarError p (ETypeVar a)
  | otherwise = (:) entry <$> eTypeVarContextReplace ct (ETypeVar a) k sigma extraEntries p
eTypeVarContextReplace (entry : ct) a k sigma extraEntries p = (:) entry <$> eTypeVarContextReplace ct a k sigma extraEntries p
eTypeVarContextReplace [] a _ _ _ p = Left $ UndeclaredETypeVarError p a

dropContextToMarker :: Context -> Context
dropContextToMarker [] = []
dropContextToMarker (CMarker : c) = c
dropContextToMarker (_ : c) = dropContextToMarker c

dropContextToETypeVar :: ETypeVar -> Context -> p -> Either (Error p) Context
dropContextToETypeVar x [] p = Left $ UndeclaredETypeVarError p x
dropContextToETypeVar x (CETypeVar y _ _  : c) p
  | x == y = return c
  | otherwise = dropContextToETypeVar x c p
dropContextToETypeVar x (CTypeVar (E y) _  : c) p
  | x == y = return c
  | otherwise = dropContextToETypeVar x c p
dropContextToETypeVar x (CTypeVar (U y) _  : c) p
  | eTypeVarName x == uTypeVarName y = Left $ UndeclaredETypeVarError p x
  | otherwise = dropContextToETypeVar x c p
dropContextToETypeVar x (_ : c) p = dropContextToETypeVar x c p

takeContextToETypeVar :: ETypeVar -> Context -> p -> Either (Error p) Context
takeContextToETypeVar x c p =
  tc c []
  where
    tc [] _ = Left $ UndeclaredETypeVarError p x
    tc (entry @ (CETypeVar y _ _) : cx) a
      | x == y = return $ reverse a
      | otherwise = tc cx (entry : a)
    tc (entry @ (CTypeVar (E y) _) : cx) a
      | x == y = return $ reverse a
      | otherwise = tc cx (entry : a)
    tc (entry @ (CTypeVar (U y) _) : cx) a
      | eTypeVarName x == uTypeVarName y = Left $ UndeclaredETypeVarError p x
      | otherwise = tc cx (entry : a)
    tc (entry : cx) a = tc cx (entry : a)

takeContextToUTypeVar :: UTypeVar -> Context -> p -> Either (Error p) Context
takeContextToUTypeVar x c p =
  tc c []
  where
    tc [] _ = Left $ UndeclaredUTypeVarError p x
    tc (entry @ (CTypeVar (U y) _) : cx) a
      | x == y = return $ reverse a
      | otherwise = tc cx (entry : a)
    tc (entry @ (CETypeVar y _ _) : cx) a
      | uTypeVarName x == eTypeVarName y = Left $ UndeclaredUTypeVarError p x
      | otherwise = tc cx (entry : a)
    tc (entry @ (CTypeVar (E y) _) : cx) a
      | uTypeVarName x == eTypeVarName y = Left $ UndeclaredUTypeVarError p x
      | otherwise = tc cx (entry : a)
    tc (entry : cx) a = tc cx (entry : a)

--Substitute universal type var for type var in type----------------------------

substituteUVarInGADTParameter ::  UTypeVar -> TypeVar -> GADTParameter -> GADTParameter
substituteUVarInGADTParameter u x (ParameterType t)     = ParameterType     $ substituteUVarInType u x t
substituteUVarInGADTParameter u x (ParameterMonotype m) = ParameterMonotype $ substituteUVarInMonotype u x m

substituteUVarInType :: UTypeVar -> TypeVar -> Type -> Type
substituteUVarInType _ _ TUnit   = TUnit
substituteUVarInType _ _ TBool   = TBool
substituteUVarInType _ _ TInt    = TInt
substituteUVarInType _ _ TFloat  = TFloat
substituteUVarInType _ _ TChar   = TChar
substituteUVarInType _ _ TString = TString
substituteUVarInType u x (TArrow t1 t2)  = TArrow   (substituteUVarInType u x t1) (substituteUVarInType u x t2)
substituteUVarInType u x (TGADT n ts)    = TGADT n  (map (substituteUVarInGADTParameter u x) ts)
substituteUVarInType u x (TProduct ts n) = TProduct (map (substituteUVarInType u x) ts) n
substituteUVarInType u x (TUVar a)
  | u == a =  case x of
    E e -> TEVar e
    U u' -> TUVar u'
  | otherwise = TUVar a
substituteUVarInType _ _ (TEVar a) = TEVar a
substituteUVarInType u x t @ (TUniversal a k t1)
  | u /= a = TUniversal a k $ substituteUVarInType u x t1
  | otherwise = t
substituteUVarInType u x t @ (TExistential a k t1)
  | u /= a = TExistential a k $ substituteUVarInType u x t1
  | otherwise = t
substituteUVarInType u x (TImp p t) = TImp (substituteUVarInProp u x p) (substituteUVarInType u x t)
substituteUVarInType u x (TAnd t p) = TAnd (substituteUVarInType u x t) (substituteUVarInProp u x p)
substituteUVarInType u x (TVec n t) = TVec (substituteUVarInMonotype u x n) (substituteUVarInType u x t)

substituteUVarInProp :: UTypeVar -> TypeVar -> Proposition -> Proposition
substituteUVarInProp u x (m1, m2) = (substituteUVarInMonotype u x m1, substituteUVarInMonotype u x m2)

substituteUVarInMonotype :: UTypeVar -> TypeVar -> Monotype -> Monotype
substituteUVarInMonotype _ _ MUnit   = MUnit
substituteUVarInMonotype _ _ MBool   = MBool
substituteUVarInMonotype _ _ MInt    = MInt
substituteUVarInMonotype _ _ MFloat  = MFloat
substituteUVarInMonotype _ _ MChar   = MChar
substituteUVarInMonotype _ _ MString = MString
substituteUVarInMonotype _ _ MZero   = MZero
substituteUVarInMonotype u x (MSucc n) = MSucc $ substituteUVarInMonotype u x n
substituteUVarInMonotype u x (MArrow m1 m2)  = MArrow   (substituteUVarInMonotype u x m1) (substituteUVarInMonotype u x m2)
substituteUVarInMonotype u x (MGADT n ms)    = MGADT n  (map (substituteUVarInMonotype u x) ms)
substituteUVarInMonotype u x (MProduct ms n) = MProduct (map (substituteUVarInMonotype u x) ms) n
substituteUVarInMonotype u x (MUVar a)
  | u == a = case x of
    E e -> MEVar e
    U u' -> MUVar u'
  | otherwise = MUVar a
substituteUVarInMonotype _ _ (MEVar a) = MEVar a

--Monotype to type and type to monotype-----------------------------------------

monotypeToType :: p -> Monotype -> Either (Error p) Type
monotypeToType _ MUnit   = return TUnit
monotypeToType _ MBool   = return TBool
monotypeToType _ MInt    = return TInt
monotypeToType _ MFloat  = return TFloat
monotypeToType _ MChar   = return TChar
monotypeToType _ MString = return TString
monotypeToType p (MArrow m1 m2)  = TArrow <$> monotypeToType p m1 <*> monotypeToType p m2
monotypeToType _ (MGADT n ms)    = return $ TGADT n $ map ParameterMonotype ms
monotypeToType p (MProduct ms n) = TProduct <$> mapM (monotypeToType p) ms <*> return n
monotypeToType _ (MEVar x) = return $ TEVar x
monotypeToType _ (MUVar x) = return $ TUVar x
monotypeToType p n = Left $ MonotypeIsNotTypeError p n

gADTParameterToMonotype :: p -> GADTParameter -> Either (Error p) Monotype
gADTParameterToMonotype p (ParameterType t)     = typeToMonotype p t
gADTParameterToMonotype _ (ParameterMonotype m) = return m

typeToMonotype :: p -> Type -> Either (Error p) Monotype
typeToMonotype _ TUnit   = return MUnit
typeToMonotype _ TBool   = return MBool
typeToMonotype _ TInt    = return MInt
typeToMonotype _ TFloat  = return MFloat
typeToMonotype _ TChar   = return MChar
typeToMonotype _ TString = return MString
typeToMonotype _ (TUVar a) = return $ MUVar a
typeToMonotype _ (TEVar a) = return $ MEVar a
typeToMonotype p (TArrow t1 t2)  = MArrow   <$> typeToMonotype p t1 <*> typeToMonotype p t2
typeToMonotype p (TGADT n ts)    = MGADT n  <$> mapM (gADTParameterToMonotype p) ts
typeToMonotype p (TProduct ts n) = MProduct <$> mapM (typeToMonotype p) ts <*> return n
typeToMonotype p t = Left $ TypeIsNotMonotypeError p t

--Context application-----------------------------------------------------------

applyContextToGADTParameter :: p -> Context -> GADTParameter -> Either (Error p) GADTParameter
applyContextToGADTParameter p c (ParameterType t)     = ParameterType <$> applyContextToType p c t
applyContextToGADTParameter p c (ParameterMonotype m) = ParameterMonotype <$> applyContextToMonotype p c m

applyContextToType ::  p -> Context -> Type -> Either (Error p) Type
applyContextToType p c (TUVar u) =
  case uTypeVarEqContextLookup c u of
    Just (CUTypeVarEq _ tau) -> applyContextToMonotype p c tau >>= monotypeToType p
    _ -> return $ TUVar u
applyContextToType p c (TImp pr t) = TImp <$> applyContextToProposition p c pr <*> applyContextToType p c t
applyContextToType p c (TAnd t pr) = TAnd <$> applyContextToType p c t <*> applyContextToProposition p c pr
applyContextToType p c (TArrow t1 t2)  = TArrow   <$> applyContextToType p c t1 <*> applyContextToType p c t2
applyContextToType p c (TGADT n ts)    = TGADT n  <$> mapM (applyContextToGADTParameter p c) ts
applyContextToType p c (TProduct ts n) = TProduct <$> mapM (applyContextToType p c) ts <*> return n
applyContextToType p c (TVec n t) = TVec <$> applyContextToMonotype p c n <*> applyContextToType p c t
applyContextToType p c (TEVar e) =
  case typeVarContextLookup c $ eTypeVarName e of
    Just (CETypeVar _ KStar tau) -> applyContextToMonotype p c tau >>= monotypeToType p
    Just (CTypeVar (E _) KStar) -> return $ TEVar e
    Just (CETypeVar _ KNat _) -> Left $ TypeHasWrongKindError p (TEVar e) KStar KNat
    Just (CTypeVar (E _) KNat) -> Left $ TypeHasWrongKindError p (TEVar e) KStar KNat
    _ -> Left $ UndeclaredETypeVarError p e
applyContextToType p c (TUniversal a k t) = TUniversal a k <$> applyContextToType p c t --TODO przemyśleć / zapytać
applyContextToType p c (TExistential a k t) = TExistential a k <$> applyContextToType p c t
applyContextToType _ _ TUnit   = return TUnit
applyContextToType _ _ TBool   = return TBool
applyContextToType _ _ TInt    = return TInt
applyContextToType _ _ TFloat  = return TFloat
applyContextToType _ _ TChar   = return TChar
applyContextToType _ _ TString = return TString

applyContextToMonotype :: p -> Context -> Monotype -> Either (Error p) Monotype
applyContextToMonotype p c (MUVar u) =
  case uTypeVarEqContextLookup c u of
    Just (CUTypeVarEq _ tau) -> applyContextToMonotype p c tau
    _ -> return $ MUVar u
applyContextToMonotype p c (MArrow m1 m2)  = MArrow   <$> applyContextToMonotype p c m1 <*> applyContextToMonotype p c m2
applyContextToMonotype p c (MGADT n ms)    = MGADT n  <$> mapM (applyContextToMonotype p c) ms
applyContextToMonotype p c (MProduct ms n) = MProduct <$> mapM (applyContextToMonotype p c) ms <*> return n
applyContextToMonotype p c (MEVar e) =
  case typeVarContextLookup c $ eTypeVarName e of
    Just (CETypeVar _ _ tau) -> applyContextToMonotype p c tau
    Just (CTypeVar (E _) _) -> return $ MEVar e
    _ -> Left $ UndeclaredETypeVarError p e
applyContextToMonotype _ _ MUnit   = return MUnit
applyContextToMonotype _ _ MBool   = return MBool
applyContextToMonotype _ _ MInt    = return MInt
applyContextToMonotype _ _ MFloat  = return MFloat
applyContextToMonotype _ _ MChar   = return MChar
applyContextToMonotype _ _ MString = return MString
applyContextToMonotype _ _ MZero   = return MZero
applyContextToMonotype p c (MSucc n) = MSucc <$> applyContextToMonotype p c n

applyContextToProposition :: p -> Context -> Proposition -> Either (Error p) Proposition
applyContextToProposition p c (m1, m2) = do
  m1' <- applyContextToMonotype p c m1
  m2' <- applyContextToMonotype p c m2
  return (m1', m2')

expandUnitPatterns :: [Branch p] -> StateT TypecheckerState (Either (Error p)) [Branch p]
expandUnitPatterns [] = return []
expandUnitPatterns (([], _, p) : _) = lift . Left $ TooShortPatternError p
expandUnitPatterns ((PUnit _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandUnitPatterns bs
expandUnitPatterns ((PWild _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandUnitPatterns bs
expandUnitPatterns ((PVar _ _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandUnitPatterns bs
expandUnitPatterns ((ptrn : _, _, _) : _) =  lift . Left $ PatternTypeError "Unit" ptrn

expandBoolPatterns :: [Branch p] -> StateT TypecheckerState (Either (Error p)) [Branch p]
expandBoolPatterns [] = return []
expandBoolPatterns (([], _, p) : _) = lift . Left $ TooShortPatternError p
expandBoolPatterns ((PBool _ _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandBoolPatterns bs
expandBoolPatterns ((PWild _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandBoolPatterns bs
expandBoolPatterns ((PVar _ _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandBoolPatterns bs
expandBoolPatterns ((ptrn : _, _, _) : _) =  lift . Left $ PatternTypeError "Bool" ptrn

expandIntPatterns :: [Branch p] -> StateT TypecheckerState (Either (Error p)) [Branch p]
expandIntPatterns [] = return []
expandIntPatterns (([], _, p) : _) = lift . Left $ TooShortPatternError p
expandIntPatterns ((PInt _ _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandIntPatterns bs
expandIntPatterns ((PWild _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandIntPatterns bs
expandIntPatterns ((PVar _ _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandIntPatterns bs
expandIntPatterns ((ptrn : _, _, _) : _) =  lift . Left $ PatternTypeError "Int" ptrn

expandFloatPatterns :: [Branch p] -> StateT TypecheckerState (Either (Error p)) [Branch p]
expandFloatPatterns [] = return []
expandFloatPatterns (([], _, p) : _) = lift . Left $ TooShortPatternError p
expandFloatPatterns ((PFloat _ _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandFloatPatterns bs
expandFloatPatterns ((PWild _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandFloatPatterns bs
expandFloatPatterns ((PVar _ _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandFloatPatterns bs
expandFloatPatterns ((ptrn : _, _, _) : _) =  lift . Left $ PatternTypeError "Float" ptrn

expandCharPatterns :: [Branch p] -> StateT TypecheckerState (Either (Error p)) [Branch p]
expandCharPatterns [] = return []
expandCharPatterns (([], _, p) : _) = lift . Left $ TooShortPatternError p
expandCharPatterns ((PChar _ _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandCharPatterns bs
expandCharPatterns ((PWild _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandCharPatterns bs
expandCharPatterns ((PVar _ _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandCharPatterns bs
expandCharPatterns ((ptrn : _, _, _) : _) =  lift . Left $ PatternTypeError "Char" ptrn

expandStringPatterns :: [Branch p] -> StateT TypecheckerState (Either (Error p)) [Branch p]
expandStringPatterns [] = return []
expandStringPatterns (([], _, p) : _) = lift . Left $ TooShortPatternError p
expandStringPatterns ((PString _ _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandStringPatterns bs
expandStringPatterns ((PWild _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandStringPatterns bs
expandStringPatterns ((PVar _ _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandStringPatterns bs
expandStringPatterns ((ptrn : _, _, _) : _) =  lift . Left $ PatternTypeError "String" ptrn

expandVarPatterns :: [Branch p] -> StateT TypecheckerState (Either (Error p)) [Branch p]
expandVarPatterns [] = return []
expandVarPatterns (([], _, p) : _) = lift . Left $ TooShortPatternError p
expandVarPatterns ((PWild _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandVarPatterns bs
expandVarPatterns ((PVar _ _ : ptrns, e, p2) : bs) = ((ptrns, e, p2) :) <$> expandVarPatterns bs
expandVarPatterns ((ptrn : _, _, _) : _) =  lift . Left $ PatternTypeError "Var" ptrn

expandTuplePatterns :: Int -> [Branch p] -> StateT TypecheckerState (Either (Error p)) [Branch p]
expandTuplePatterns _ [] = return []
expandTuplePatterns _ (([], _, p) : _) = lift . Left $ TooShortPatternError p
expandTuplePatterns n ((PTuple p1 args m : ptrns, e, p2) : bs)
  | n == m = ((args ++ ptrns, e, p2) :) <$> expandTuplePatterns n bs
  | otherwise = lift . Left $ PatternTypeError ("Tuple" ++ show n) $ PTuple p1 args m
expandTuplePatterns n ((PWild p1 : ptrns, e, p2) : bs) =
  ((map (const (PWild p1)) [1..n] ++ ptrns, e, p2) :) <$> expandTuplePatterns n bs
expandTuplePatterns n ((PVar p1 _ : ptrns, e, p2) : bs) =
  ((map (const (PWild p1)) [1..n] ++ ptrns, e, p2) :) <$> expandTuplePatterns n bs
expandTuplePatterns n ((ptrn : _, _, _) : _) =  lift . Left $ PatternTypeError ("Tuple" ++ show n) ptrn

expandVecPatterns :: [Branch p] -> StateT TypecheckerState (Either (Error p)) ([Branch p], [Branch p])
expandVecPatterns [] = return ([], [])
expandVecPatterns (([], _, p) : _) = lift . Left $ TooShortPatternError p
expandVecPatterns ((PNil _ : ptrns, e, p) : bs) = cross ((ptrns, e, p) :) id <$> expandVecPatterns bs
expandVecPatterns ((PCons _ x xs : ptrns, e, p) : bs) = cross id ((x : xs : ptrns, e, p) :) <$> expandVecPatterns bs
expandVecPatterns ((PWild p1 : ptrns, e, p2) : bs) =
  cross ((ptrns, e, p2) :) ((PWild p1 : PWild p1 : ptrns, e, p2) :) <$> expandVecPatterns bs
expandVecPatterns ((PVar p1 _ : ptrns, e, p2) : bs) =
  cross ((ptrns, e, p2) :) ((PWild p1 : PWild p1 : ptrns, e, p2) :) <$> expandVecPatterns bs
expandVecPatterns ((ptrn : _, _, _) : _) =  lift . Left $ PatternTypeError "Vec" ptrn

expandGADTVarPatterns ::
  String -> p -> [Pattern p] -> Expr p -> p -> [Branch p]
  -> StateT TypecheckerState (Either (Error p)) (Map.Map String [Branch p])
expandGADTVarPatterns typeName p1 ptrns e p2 bs = do
  cs <- view constrContext <$> get
  bs' <- expandGADTPatterns typeName bs
  return $ Map.mapWithKey (produceWilds cs) bs'
  where
    produceWilds cs k b =
      (map (const (PWild p1)) (maybe [] constrArgsTemplates (Map.lookup k cs)) ++ ptrns, e, p2) : b

expandGADTPatterns :: String -> [Branch p] -> StateT TypecheckerState (Either (Error p)) (Map.Map String [Branch p])
expandGADTPatterns typeName [] = do
  cs <- view constrContext <$> get
  return . Map.fromList . map (pair (constrTypeName . snd, const [])) . Map.toList . Map.filter ((typeName ==) . constrTypeName) $ cs
expandGADTPatterns _ (([], _, p) : _) = lift . Left $ TooShortPatternError p
expandGADTPatterns typeName ((PConstr p1 constrName args : ptrns, e, p2) : bs) = do
  bs' <- expandGADTPatterns typeName bs
  if Map.member constrName bs' then
    return $ Map.adjust ((args ++ ptrns, e, p2) :) constrName bs'
  else
    lift . Left $ NotConstructorOfError (PConstr p1 constrName args) typeName
expandGADTPatterns typeName ((PWild p1 : ptrns, e, p2) : bs) =
  expandGADTVarPatterns typeName p1 ptrns e p2 bs
expandGADTPatterns typeName ((PVar p1 _ : ptrns, e, p2) : bs) =
  expandGADTVarPatterns typeName p1 ptrns e p2 bs
expandGADTPatterns _ ((ptrn : _, _, _) : _) =  lift . Left $ PatternTypeError "GADT" ptrn

vecPatternGuarded :: [Branch p] -> StateT TypecheckerState (Either (Error p)) Bool
vecPatternGuarded [] = return False
vecPatternGuarded ((PNil _ : _, _, _) : _) = return True
vecPatternGuarded ((PCons {} : _, _, _) : _) = return True
vecPatternGuarded ((PWild _ : _, _, _) : bs) = vecPatternGuarded bs
vecPatternGuarded ((PVar {} : _, _, _) : bs) = vecPatternGuarded bs
vecPatternGuarded (([], _, p) : _) = lift . Left $ TooShortPatternError p
vecPatternGuarded ((ptrn : _, _, _) : _) = lift . Left $ PatternTypeError "Vec" ptrn

gadtPatternGuarded :: String -> [Branch p] -> StateT TypecheckerState (Either (Error p)) Bool
gadtPatternGuarded _ [] = return False
gadtPatternGuarded typeName ((PConstr p constrName args : _, _, _) : _) = do
  lookupRes <- Map.lookup constrName . view constrContext <$> get
  case lookupRes of
    Nothing -> lift . Left $ UndeclaredConstructorInPatternError $ PConstr p constrName args
    Just constr
      | constrTypeName constr /= typeName ->
        lift . Left $ MismatchedConstructorInPatternError (PConstr p constrName args) (constrTypeName constr) typeName
      | length (constrArgsTemplates constr) /= length args ->
        lift . Left $ MismatchedConstructorArityInPatternError
        (PConstr p constrName args)
        (length $ constrArgsTemplates constr) (length args)
      | otherwise -> return True
gadtPatternGuarded typeName ((PWild _ : _, _, _) : bs) = gadtPatternGuarded typeName bs
gadtPatternGuarded typeName ((PVar {} : _, _, _) : bs) = gadtPatternGuarded typeName bs
gadtPatternGuarded _ (([], _, p) : _) = lift . Left $ TooShortPatternError p
gadtPatternGuarded _ ((ptrn : _, _, _) : _) = lift . Left $ PatternTypeError "Vec" ptrn
