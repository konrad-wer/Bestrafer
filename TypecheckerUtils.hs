module TypecheckerUtils where

import AST
import qualified Data.Set as Set

data Error p
  = UndeclaredVariableError p Var
  | InternalCompilerError p String
  | ETypeVarMismatchError p Monotype Monotype
  | UndeclaredETypeVarError p ETypeVar
  | UndeclaredUTypeVarError p UTypeVar
  | TypeHasWrongKindError p Type Kind Kind
  | MonotypeHasWrongKindError p Monotype Kind Kind
  | MonotypeIsNotTypeError p Monotype
  | TypeFormednessPrcFEVError p [ETypeVar]
  deriving (Show, Eq)

--polarity utils------------------------------------------

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

join :: Polarity -> Polarity -> Polarity
join Positive _ = Positive
join Negative _ = Negative
join Neutral Positive = Positive
join Neutral Negative = Negative
join Neutral Neutral = Negative

headedByUniversal :: Type -> Bool
headedByUniversal TUniversal {} = True
headedByUniversal _ = False

headedByExistential :: Type -> Bool
headedByExistential TExistential {} = True
headedByExistential _ = False

--Free existential variables-----------------------------------

freeExistentialVariables :: Type -> Set.Set ETypeVar
freeExistentialVariables TUnit = Set.empty
freeExistentialVariables (TArrow t1 t2) = Set.union (freeExistentialVariables t1) (freeExistentialVariables t2)
freeExistentialVariables (TCoproduct t1 t2) = Set.union (freeExistentialVariables t1) (freeExistentialVariables t2)
freeExistentialVariables (TProduct t1 t2) = Set.union (freeExistentialVariables t1) (freeExistentialVariables t2)
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
freeExistentialVariablesOfMonotype MUnit = Set.empty
freeExistentialVariablesOfMonotype MZero = Set.empty
freeExistentialVariablesOfMonotype (MSucc n) = freeExistentialVariablesOfMonotype n
freeExistentialVariablesOfMonotype (MArrow m1 m2) = Set.union (freeExistentialVariablesOfMonotype m1) (freeExistentialVariablesOfMonotype m2)
freeExistentialVariablesOfMonotype (MCoproduct m1 m2) = Set.union (freeExistentialVariablesOfMonotype m1) (freeExistentialVariablesOfMonotype m2)
freeExistentialVariablesOfMonotype (MProduct m1 m2) = Set.union (freeExistentialVariablesOfMonotype m1) (freeExistentialVariablesOfMonotype m2)
freeExistentialVariablesOfMonotype (MUVar _) = Set.empty
freeExistentialVariablesOfMonotype (MEVar x) = Set.singleton x

--Context utils----------------------------------------------

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

eTypeVarContextReplace :: Context -> ETypeVar -> Monotype -> [ContextEntry] -> p -> Either (Error p) Context
eTypeVarContextReplace c @ (entry @ (CETypeVar b _ tau) : ct) a sigma extraEntries p
  | a == b && tau == sigma = return c
  | a == b && tau /= sigma = Left $ ETypeVarMismatchError p tau sigma
  | otherwise = (:) entry <$> eTypeVarContextReplace ct a sigma extraEntries p
eTypeVarContextReplace (entry @  (CTypeVar (E b) k) : ct) a sigma extraEntries p
  | a == b = return $ CETypeVar a k sigma : extraEntries ++ ct
  | otherwise = (:) entry <$> eTypeVarContextReplace ct a sigma extraEntries p
eTypeVarContextReplace (entry @  (CTypeVar (U (UTypeVar b)) _) : ct) (ETypeVar a) sigma extraEntries p
  | a == b = Left $ UndeclaredETypeVarError p (ETypeVar a)
  | otherwise = (:) entry <$> eTypeVarContextReplace ct (ETypeVar a) sigma extraEntries p
eTypeVarContextReplace (entry : ct) a sigma extraEntries p = (:) entry <$> eTypeVarContextReplace ct a sigma extraEntries p
eTypeVarContextReplace [] a _ _ p = Left $ UndeclaredETypeVarError p a

dropContextToMarker :: Context -> Context
dropContextToMarker [] = []
dropContextToMarker (CMarker : c) = c
dropContextToMarker (_ : c) = dropContextToMarker c

--Substitute universal type var for type var in type-----------

substituteUVarInType :: UTypeVar -> TypeVar -> Type -> Type
substituteUVarInType _ _ TUnit = TUnit
substituteUVarInType u x (TArrow t1 t2) = TArrow (substituteUVarInType u x t1) (substituteUVarInType u x t2)
substituteUVarInType u x (TCoproduct t1 t2) = TCoproduct (substituteUVarInType u x t1) (substituteUVarInType u x t2)
substituteUVarInType u x (TProduct t1 t2) = TProduct (substituteUVarInType u x t1) (substituteUVarInType u x t2)
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
substituteUVarInMonotype _ _ MUnit = MUnit
substituteUVarInMonotype _ _ MZero = MZero
substituteUVarInMonotype u x (MSucc n) = MSucc $ substituteUVarInMonotype u x n
substituteUVarInMonotype u x (MArrow m1 m2) = MArrow (substituteUVarInMonotype u x m1) (substituteUVarInMonotype u x m2)
substituteUVarInMonotype u x (MCoproduct m1 m2) = MCoproduct (substituteUVarInMonotype u x m1) (substituteUVarInMonotype u x m2)
substituteUVarInMonotype u x (MProduct m1 m2) = MProduct (substituteUVarInMonotype u x m1) (substituteUVarInMonotype u x m2)
substituteUVarInMonotype u x (MUVar a)
  | u == a = case x of
    E e -> MEVar e
    U u' -> MUVar u'
  | otherwise = MUVar a
substituteUVarInMonotype _ _ (MEVar a) = MEVar a

--Monotype to type------------------------------------------------

monotypeToType :: Monotype -> p -> Either (Error p) Type
monotypeToType MUnit _ = return TUnit
monotypeToType (MArrow m1 m2) p = TArrow <$> monotypeToType m1 p <*> monotypeToType m2 p
monotypeToType (MCoproduct m1 m2) p = TCoproduct <$> monotypeToType m1 p <*> monotypeToType m2 p
monotypeToType (MProduct m1 m2) p = TProduct <$> monotypeToType m1 p <*> monotypeToType m2 p
monotypeToType (MEVar x) _ = return $ TEVar x
monotypeToType (MUVar x) _ = return $ TUVar x
monotypeToType n p = Left $ MonotypeIsNotTypeError p n

--Context application----------------------------------------------

applyContextToType :: Context -> Type -> p-> Either (Error p) Type
applyContextToType c (TUVar u) p =
  case uTypeVarEqContextLookup c u of
    Just (CUTypeVarEq _ tau) -> applyContextToMonotype c tau p >>= flip monotypeToType p
    _ -> return $ TUVar u
applyContextToType c (TImp pr t) p = TImp <$> applyContextToProposition c pr p <*> applyContextToType c t p
applyContextToType c (TAnd t pr) p = TAnd <$> applyContextToType c t p <*> applyContextToProposition c pr p
applyContextToType c (TArrow t1 t2) p = TArrow <$> applyContextToType c t1 p <*> applyContextToType c t2 p
applyContextToType c (TCoproduct t1 t2) p = TCoproduct <$> applyContextToType c t1 p <*> applyContextToType c t2 p
applyContextToType c (TProduct t1 t2) p = TProduct <$> applyContextToType c t1 p <*> applyContextToType c t2 p
applyContextToType c (TVec n t) p = TVec <$> applyContextToMonotype c n p <*> applyContextToType c t p
applyContextToType c (TEVar e) p =
  case typeVarContextLookup c $ eTypeVarName e of
    Just (CETypeVar _ KStar tau) -> applyContextToMonotype c tau p >>= flip monotypeToType p
    Just (CTypeVar (E _) KStar) -> return $ TEVar e
    Just (CETypeVar _ KNat _) -> Left $ TypeHasWrongKindError p (TEVar e) KStar KNat
    Just (CTypeVar (E _) KNat) -> Left $ TypeHasWrongKindError p (TEVar e) KStar KNat
    _ -> Left $ UndeclaredETypeVarError p e
applyContextToType c (TUniversal a k t) p = TUniversal a k <$> applyContextToType (CTypeVar (U a) k : c) t p --TODO przemyśleć / zapytać
applyContextToType c (TExistential a k t) p = TExistential a k <$> applyContextToType (CTypeVar (U a) k : c) t p
applyContextToType _ TUnit _ = return TUnit

applyContextToMonotype :: Context -> Monotype -> p -> Either (Error p) Monotype
applyContextToMonotype c (MUVar u) p =
  case uTypeVarEqContextLookup c u of
    Just (CUTypeVarEq _ tau) -> applyContextToMonotype c tau p
    _ -> return $ MUVar u
applyContextToMonotype c (MArrow m1 m2) p = MArrow <$> applyContextToMonotype c m1 p <*> applyContextToMonotype c m2 p
applyContextToMonotype c (MCoproduct m1 m2) p = MCoproduct <$> applyContextToMonotype c m1 p <*> applyContextToMonotype c m2 p
applyContextToMonotype c (MProduct m1 m2) p = MProduct <$> applyContextToMonotype c m1 p <*> applyContextToMonotype c m2 p
applyContextToMonotype c (MEVar e) p =
  case typeVarContextLookup c $ eTypeVarName e of
    Just (CETypeVar _ _ tau) -> applyContextToMonotype c tau p
    Just (CTypeVar (E _) _) -> return $ MEVar e
    _ -> Left $ UndeclaredETypeVarError p e
applyContextToMonotype _ MUnit _ = return MUnit
applyContextToMonotype _ MZero _ = return MZero
applyContextToMonotype c (MSucc n) p = MSucc <$> applyContextToMonotype c n p

applyContextToProposition :: Context -> Proposition -> p -> Either (Error p) Proposition
applyContextToProposition c (m1, m2) p = do
  m1' <- applyContextToMonotype c m1 p
  m2' <- applyContextToMonotype c m2 p
  return (m1', m2')
