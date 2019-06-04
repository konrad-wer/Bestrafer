{-# LANGUAGE TemplateHaskell #-}

module TypecheckerUtils where

import AST
import qualified Data.Set as Set
import Control.Lens hiding (Context)

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
  deriving (Show)

data TypecheckerState = TypecheckerState {_freshVarNum :: Integer, _constrContext :: ConstructorsContext, _gadtArities :: GADTArities}

makeLenses ''TypecheckerState

--simple utils------------------------------------------------------------------

generateSubETypeVars :: ETypeVar -> (ETypeVar, ETypeVar)
generateSubETypeVars a = (ETypeVar $ eTypeVarName a ++ "-1", ETypeVar $ eTypeVarName a ++ "-2")

generateSubETypeVarsList :: ETypeVar -> Int -> [ETypeVar]
generateSubETypeVarsList a n = [ETypeVar $ eTypeVarName a ++ "-" ++ show k | k <- [1..n]]

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
    ParameterMonotype m -> monotypeToType m p

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
    ParameterType t -> typeToMonotype t p
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

monotypeToType :: Monotype -> p -> Either (Error p) Type
monotypeToType MUnit _   = return TUnit
monotypeToType MBool _   = return TBool
monotypeToType MInt _    = return TInt
monotypeToType MFloat _  = return TFloat
monotypeToType MChar _   = return TChar
monotypeToType MString _ = return TString
monotypeToType (MArrow m1 m2) p  = TArrow   <$> monotypeToType m1 p <*> monotypeToType m2 p
monotypeToType (MGADT n ms) _    = return $ TGADT n $ map ParameterMonotype ms
monotypeToType (MProduct ms n) p = TProduct <$> mapM (`monotypeToType` p) ms <*> return n
monotypeToType (MEVar x) _ = return $ TEVar x
monotypeToType (MUVar x) _ = return $ TUVar x
monotypeToType n p = Left $ MonotypeIsNotTypeError p n

gADTParameterToMonotype :: GADTParameter -> p -> Either (Error p) Monotype
gADTParameterToMonotype (ParameterType t) p     = typeToMonotype t p
gADTParameterToMonotype (ParameterMonotype m) _ = return m

typeToMonotype :: Type -> p -> Either (Error p) Monotype
typeToMonotype TUnit _   = return MUnit
typeToMonotype TBool _   = return MBool
typeToMonotype TInt _    = return MInt
typeToMonotype TFloat _  = return MFloat
typeToMonotype TChar _   = return MChar
typeToMonotype TString _ = return MString
typeToMonotype (TUVar a) _ = return $ MUVar a
typeToMonotype (TEVar a) _ = return $ MEVar a
typeToMonotype (TArrow t1 t2)  p = MArrow   <$> typeToMonotype t1 p <*> typeToMonotype t2 p
typeToMonotype (TGADT n ts)    p = MGADT n  <$> mapM (`gADTParameterToMonotype` p) ts
typeToMonotype (TProduct ts n) p = MProduct <$> mapM (`typeToMonotype` p) ts <*> return n
typeToMonotype t p = Left $ TypeIsNotMonotypeError p t

--Context application-----------------------------------------------------------

applyContextToGADTParameter :: Context -> GADTParameter -> p -> Either (Error p) GADTParameter
applyContextToGADTParameter c (ParameterType t)     p = ParameterType <$> applyContextToType c t p
applyContextToGADTParameter c (ParameterMonotype m) p = ParameterMonotype <$> applyContextToMonotype c m p

applyContextToType :: Context -> Type -> p -> Either (Error p) Type
applyContextToType c (TUVar u) p =
  case uTypeVarEqContextLookup c u of
    Just (CUTypeVarEq _ tau) -> applyContextToMonotype c tau p >>= flip monotypeToType p
    _ -> return $ TUVar u
applyContextToType c (TImp pr t) p = TImp <$> applyContextToProposition c pr p <*> applyContextToType c t p
applyContextToType c (TAnd t pr) p = TAnd <$> applyContextToType c t p <*> applyContextToProposition c pr p
applyContextToType c (TArrow t1 t2)  p = TArrow   <$> applyContextToType c t1 p <*> applyContextToType c t2 p
applyContextToType c (TGADT n ts)    p = TGADT n  <$> mapM (flip (applyContextToGADTParameter c) p) ts
applyContextToType c (TProduct ts n) p = TProduct <$> mapM (flip (applyContextToType c) p) ts <*> return n
applyContextToType c (TVec n t) p = TVec <$> applyContextToMonotype c n p <*> applyContextToType c t p
applyContextToType c (TEVar e) p =
  case typeVarContextLookup c $ eTypeVarName e of
    Just (CETypeVar _ KStar tau) -> applyContextToMonotype c tau p >>= flip monotypeToType p
    Just (CTypeVar (E _) KStar) -> return $ TEVar e
    Just (CETypeVar _ KNat _) -> Left $ TypeHasWrongKindError p (TEVar e) KStar KNat
    Just (CTypeVar (E _) KNat) -> Left $ TypeHasWrongKindError p (TEVar e) KStar KNat
    _ -> Left $ UndeclaredETypeVarError p e
applyContextToType c (TUniversal a k t) p = TUniversal a k <$> applyContextToType c t p --TODO przemyśleć / zapytać
applyContextToType c (TExistential a k t) p = TExistential a k <$> applyContextToType c t p
applyContextToType _ TUnit _   = return TUnit
applyContextToType _ TBool _   = return TBool
applyContextToType _ TInt _    = return TInt
applyContextToType _ TFloat _  = return TFloat
applyContextToType _ TChar _   = return TChar
applyContextToType _ TString _ = return TString

applyContextToMonotype :: Context -> Monotype -> p -> Either (Error p) Monotype
applyContextToMonotype c (MUVar u) p =
  case uTypeVarEqContextLookup c u of
    Just (CUTypeVarEq _ tau) -> applyContextToMonotype c tau p
    _ -> return $ MUVar u
applyContextToMonotype c (MArrow m1 m2)  p = MArrow   <$> applyContextToMonotype c m1 p <*> applyContextToMonotype c m2 p
applyContextToMonotype c (MGADT n ms)    p = MGADT n  <$> mapM (flip (applyContextToMonotype c) p) ms
applyContextToMonotype c (MProduct ms n) p = MProduct <$> mapM (flip (applyContextToMonotype c) p) ms  <*> return n
applyContextToMonotype c (MEVar e) p =
  case typeVarContextLookup c $ eTypeVarName e of
    Just (CETypeVar _ _ tau) -> applyContextToMonotype c tau p
    Just (CTypeVar (E _) _) -> return $ MEVar e
    _ -> Left $ UndeclaredETypeVarError p e
applyContextToMonotype _ MUnit _   = return MUnit
applyContextToMonotype _ MBool _   = return MBool
applyContextToMonotype _ MInt _    = return MInt
applyContextToMonotype _ MFloat _  = return MFloat
applyContextToMonotype _ MChar _   = return MChar
applyContextToMonotype _ MString _ = return MString
applyContextToMonotype _ MZero _   = return MZero
applyContextToMonotype c (MSucc n) p = MSucc <$> applyContextToMonotype c n p

applyContextToProposition :: Context -> Proposition -> p -> Either (Error p) Proposition
applyContextToProposition c (m1, m2) p = do
  m1' <- applyContextToMonotype c m1 p
  m2' <- applyContextToMonotype c m2 p
  return (m1', m2')
