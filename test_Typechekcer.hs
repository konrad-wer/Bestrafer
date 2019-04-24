import AST
import Typechecker
import qualified Data.Set as Set

type Test = () -> Bool
type TestName = String

context1 :: Context
context1 = [CVar "x" TUnit Principal, CTypeVar (U $ UTypeVar "y") KStar, CUTypeVarEq (UTypeVar "n") (MSucc (MSucc (MSucc MZero))),
            CETypeVar (ETypeVar "z") KStar $ MProduct MUnit MUnit, CUTypeVarEq (UTypeVar "k") MUnit,
            CVar "r" (TEVar $ ETypeVar "z") NotPrincipal, CTypeVar (E $ ETypeVar "a") KStar, CETypeVar (ETypeVar "b") KNat (MSucc MZero)]

context2 :: Context
context2 = [CTypeVar (E $ ETypeVar "a") KNat, CTypeVar (E $ ETypeVar "b") KStar, CTypeVar (E $ ETypeVar "c") KStar]

context3 :: Context
context3 = [CVar "x" TUnit Principal, CTypeVar (U $ UTypeVar "y") KStar, CUTypeVarEq (UTypeVar "n") (MSucc (MSucc (MSucc MZero))),
            CETypeVar (ETypeVar "z") KStar $ MProduct MUnit MUnit, CUTypeVarEq (UTypeVar "k") MUnit,
            CVar "r" (TEVar $ ETypeVar "z") NotPrincipal, CETypeVar (ETypeVar "a") KStar MUnit, CETypeVar (ETypeVar "b") KNat (MSucc MZero)]

context4 :: Context
context4 = [CVar "zz" (TEVar $ ETypeVar "r")  NotPrincipal, CVar "x" TUnit NotPrincipal, CTypeVar (U $ UTypeVar "x") KStar, CUTypeVarEq (UTypeVar "x") MZero,
            CETypeVar (ETypeVar "x") KNat MZero, CUTypeVarEq (UTypeVar "x") MUnit, CVar "x" TUnit Principal, CTypeVar (E $ ETypeVar "x") KStar,
            CETypeVar (ETypeVar "x") KStar $ MProduct MUnit MUnit, CTypeVar (U $ UTypeVar "x") KNat, CTypeVar (E $ ETypeVar "x") KStar]

context5 :: Context
context5 = [CUTypeVarEq (UTypeVar "x") MZero, CETypeVar (ETypeVar "x") KNat (MSucc MZero), CUTypeVarEq (UTypeVar "x") MUnit,
            CVar "x" (TUVar $ UTypeVar "x") Principal, CTypeVar (E $ ETypeVar "x") KStar, CETypeVar (ETypeVar "x") KStar $ MProduct MUnit MUnit,
            CTypeVar (U $ UTypeVar "x") KNat, CTypeVar (E $ ETypeVar "x") KStar, CTypeVar (U $ UTypeVar "x") KStar]

--freeExistentialVariablesOfMonotype :: Monotype -> Set.Set ETypeVar
freeExistentialVariablesOfMonotype_test1 :: Test
freeExistentialVariablesOfMonotype_test1 () =
  case Set.toList . freeExistentialVariablesOfMonotype $ MProduct (MArrow (MUVar $ UTypeVar "x") MUnit) (MCoproduct MUnit MUnit) of
    [] -> True
    _ -> False

freeExistentialVariablesOfMonotype_test2 :: Test
freeExistentialVariablesOfMonotype_test2 () =
  case Set.toList . freeExistentialVariablesOfMonotype $ MProduct (MArrow (MUVar $ UTypeVar "x")
       (MEVar $ ETypeVar "a")) (MCoproduct (MEVar $ ETypeVar "b") (MEVar $ ETypeVar "c")) of
    [ETypeVar "a", ETypeVar "b", ETypeVar "c"] -> True
    _ -> False

freeExistentialVariablesOfMonotype_test3 :: Test
freeExistentialVariablesOfMonotype_test3 () =
  case Set.toList . freeExistentialVariablesOfMonotype $ MSucc (MSucc MZero) of
    [] -> True
    _ -> False

freeExistentialVariablesOfMonotype_test4 :: Test
freeExistentialVariablesOfMonotype_test4 () =
  case Set.toList . freeExistentialVariablesOfMonotype $ MSucc (MSucc (MUVar $ UTypeVar "x")) of
    [] -> True
    _ -> False

freeExistentialVariablesOfMonotype_test5 :: Test
freeExistentialVariablesOfMonotype_test5 () =
  case Set.toList . freeExistentialVariablesOfMonotype $ MSucc (MSucc (MEVar $ ETypeVar "x")) of
    [ETypeVar "x"] -> True
    _ -> False

--freeExistentialVariablesOfProp :: Proposition -> Set.Set ETypeVar
freeExistentialVariablesOfProp_test1 :: Test
freeExistentialVariablesOfProp_test1 () =
  case Set.toList . freeExistentialVariablesOfProp $ (MSucc MZero, MArrow (MUVar $ UTypeVar "x") MUnit) of
    [] -> True
    _ -> False

freeExistentialVariablesOfProp_test2 :: Test
freeExistentialVariablesOfProp_test2 () =
  case Set.toList . freeExistentialVariablesOfProp $ (MSucc (MEVar $ ETypeVar "x") , MArrow (MUVar $ UTypeVar "x") MUnit) of
    [ETypeVar "x"] -> True
    _ -> False

freeExistentialVariablesOfProp_test3 :: Test
freeExistentialVariablesOfProp_test3 () =
  case Set.toList . freeExistentialVariablesOfProp $ (MSucc (MUVar $ UTypeVar "x") , MArrow (MEVar $ ETypeVar "a") (MEVar $ ETypeVar "b")) of
    [ETypeVar "a", ETypeVar "b"] -> True
    _ -> False

freeExistentialVariablesOfProp_test4 :: Test
freeExistentialVariablesOfProp_test4 () =
  case Set.toList . freeExistentialVariablesOfProp $ (MSucc (MEVar $ ETypeVar "U") , MArrow (MEVar $ ETypeVar "W") (MEVar $ ETypeVar "r")) of
    [ETypeVar "U", ETypeVar "W",  ETypeVar "r"] -> True
    _ -> False

--freeExistentialVariables :: Type -> Set.Set ETypeVar
freeExistentialVariables_test1 :: Test
freeExistentialVariables_test1 () =
  case Set.toList . freeExistentialVariables $ TProduct (TArrow (TUVar $ UTypeVar "x") TUnit) (TCoproduct TUnit TUnit) of
    [] -> True
    _ -> False

freeExistentialVariables_test2 :: Test
freeExistentialVariables_test2 () =
  case Set.toList . freeExistentialVariables $ TProduct (TArrow (TUVar $ UTypeVar "x") (TEVar $ ETypeVar "g"))
       (TCoproduct (TEVar $ ETypeVar "h") (TEVar $ ETypeVar "c")) of
    [ETypeVar "c", ETypeVar "g", ETypeVar "h"] -> True
    _ -> False

freeExistentialVariables_test3 :: Test
freeExistentialVariables_test3 () =
  case Set.toList . freeExistentialVariables $ TExistential "x" KStar $ TProduct (TArrow (TEVar $ ETypeVar "x") TUnit) (TCoproduct TUnit TUnit) of
    [] -> True
    _ -> False

freeExistentialVariables_test4 :: Test
freeExistentialVariables_test4 () =
  case Set.toList . freeExistentialVariables $ TUniversal "x" KStar $ TProduct (TArrow (TEVar $ ETypeVar "x") TUnit) (TCoproduct TUnit TUnit) of
    [ETypeVar "x"] -> True
    _ -> False

freeExistentialVariables_test5 :: Test
freeExistentialVariables_test5 () =
  case Set.toList . freeExistentialVariables $ TUniversal "U" KNat $ TExistential "x" KStar $
       TImp (MSucc (MEVar $ ETypeVar "U") , MArrow (MEVar $ ETypeVar "W") (MEVar $ ETypeVar "r"))
       (TProduct (TArrow (TEVar $ ETypeVar "x") TUnit) (TCoproduct (TEVar $ ETypeVar "y") TUnit)) of
    [ETypeVar "U", ETypeVar "W", ETypeVar "r", ETypeVar "y"] -> True
    _ -> False

freeExistentialVariables_test6 :: Test
freeExistentialVariables_test6 () =
  case Set.toList . freeExistentialVariables $ TUniversal "U" KNat $ TExistential "x" KStar $
       TAnd (TVec (MSucc (MEVar $ ETypeVar "a")) (TProduct (TArrow (TEVar $ ETypeVar "x") TUnit) (TCoproduct (TEVar $ ETypeVar "y") TUnit)))
       (MSucc (MEVar $ ETypeVar "U") , MArrow (MEVar $ ETypeVar "W") (MEVar $ ETypeVar "r")) of
    [ETypeVar "U", ETypeVar "W",  ETypeVar "a", ETypeVar "r", ETypeVar "y"] -> True
    _ -> False

freeExistentialVariables_test7 :: Test
freeExistentialVariables_test7 () =
  case Set.toList . freeExistentialVariables $ TExistential "h" KNat $  TExistential "c" KStar $ TExistential "g" KStar $
       TProduct (TArrow (TUVar $ UTypeVar "x") (TEVar $ ETypeVar "g")) (TCoproduct (TEVar $ ETypeVar "h") (TEVar $ ETypeVar "c")) of
    [] -> True
    _ -> False

--varContextLookup :: Context -> Expr p -> Either (Error p) ContextEntry
varContextLookup_test1 :: Test
varContextLookup_test1 () =
  case varContextLookup context1 "x" "1 , 3" of
    Right (CVar "x" TUnit Principal) -> True
    _ -> False

varContextLookup_test2 :: Test
varContextLookup_test2 () =
  case varContextLookup []  "x"  "1 , 3"of
    Left (UndeclaredVariableError _ "x") -> True
    _ -> False

varContextLookup_test3 :: Test
varContextLookup_test3 () =
  case varContextLookup context1 "y" "1 , 3" of
    Left (UndeclaredVariableError _ "y") -> True
    _ -> False

varContextLookup_test4 :: Test
varContextLookup_test4 () =
  case varContextLookup context1  "z" "1 , 3" of
    Left (UndeclaredVariableError _ "z") -> True
    _ -> False

varContextLookup_test5 :: Test
varContextLookup_test5 () =
  case varContextLookup context1 "k" "1 , 3" of
    Left (UndeclaredVariableError _ "k") -> True
    _ -> False

varContextLookup_test6 :: Test
varContextLookup_test6 () =
  case varContextLookup context1 "Konrad" "1 , 3" of
    Left (UndeclaredVariableError _ "Konrad")  -> True
    _ -> False

varContextLookup_test7 :: Test
varContextLookup_test7 () =
  case varContextLookup context4 "x" "1 , 3" of
    Right (CVar "x" TUnit NotPrincipal) -> True
    _ -> False

varContextLookup_test8 :: Test
varContextLookup_test8 () =
  case varContextLookup context5 "x" "1 , 3" of
    Right (CVar "x" (TUVar (UTypeVar "x")) Principal) -> True
    _ -> False

varContextLookup_test9 :: Test
varContextLookup_test9 () =
  case varContextLookup context1 "r" "1 , 3" of
    Right (CVar "r" (TEVar (ETypeVar "z")) NotPrincipal) -> True
    _ -> False

--uTypeVarEqContextLookup :: Context -> UTypeVar -> Maybe ContextEntry
uTypeVarEqContextLookup_test1 :: Test
uTypeVarEqContextLookup_test1 () =
  case uTypeVarEqContextLookup [] $ UTypeVar "x" of
    Nothing -> True
    _ -> False

uTypeVarEqContextLookup_test2 :: Test
uTypeVarEqContextLookup_test2 () =
  case uTypeVarEqContextLookup context1 $ UTypeVar "x" of
    Nothing -> True
    _ -> False

uTypeVarEqContextLookup_test3 :: Test
uTypeVarEqContextLookup_test3 () =
  case uTypeVarEqContextLookup context1 $ UTypeVar "n" of
    Just (CUTypeVarEq (UTypeVar "n") (MSucc (MSucc (MSucc MZero)))) -> True
    _ -> False

uTypeVarEqContextLookup_test4 :: Test
uTypeVarEqContextLookup_test4 () =
  case uTypeVarEqContextLookup context1 $ UTypeVar "k" of
    Just (CUTypeVarEq (UTypeVar "k") MUnit) -> True
    _ -> False

uTypeVarEqContextLookup_test5 :: Test
uTypeVarEqContextLookup_test5 () =
  case uTypeVarEqContextLookup context1 $ UTypeVar "Konrad" of
    Nothing -> True
    _ -> False

uTypeVarEqContextLookup_test6 :: Test
uTypeVarEqContextLookup_test6 () =
  case uTypeVarEqContextLookup context4 $ UTypeVar "x" of
    Nothing -> True
    _ -> False

uTypeVarEqContextLookup_test7 :: Test
uTypeVarEqContextLookup_test7 () =
  case uTypeVarEqContextLookup context5 $ UTypeVar "x" of
    Just (CUTypeVarEq (UTypeVar "x") MZero) -> True
    _ -> False

--eTypeVarContextLookup :: Context -> ETypeVar -> Maybe ContextEntry
eTypeVarContextLookup_test1 :: Test
eTypeVarContextLookup_test1 () =
  case eTypeVarContextLookup [] $ ETypeVar "x" of
    Nothing -> True
    _ -> False

eTypeVarContextLookup_test2 :: Test
eTypeVarContextLookup_test2 () =
  case eTypeVarContextLookup context1 $ ETypeVar "x" of
    Nothing -> True
    _ -> False

eTypeVarContextLookup_test3 :: Test
eTypeVarContextLookup_test3 () =
  case eTypeVarContextLookup context1 $ ETypeVar "z" of
    Just (CETypeVar (ETypeVar "z") KStar (MProduct MUnit MUnit)) -> True
    _ -> False

eTypeVarContextLookup_test4 :: Test
eTypeVarContextLookup_test4 () =
 case eTypeVarContextLookup context1 $ ETypeVar "b" of
   Just (CETypeVar (ETypeVar "b") KNat (MSucc MZero)) -> True
   _ -> False

eTypeVarContextLookup_test5 :: Test
eTypeVarContextLookup_test5 () =
 case eTypeVarContextLookup context1 $ ETypeVar "Konrad" of
   Nothing -> True
   _ -> False

eTypeVarContextLookup_test6 :: Test
eTypeVarContextLookup_test6 () =
  case eTypeVarContextLookup context1 $ ETypeVar "a" of
    Just (CTypeVar (E (ETypeVar "a")) KStar) -> True
    _ -> False

eTypeVarContextLookup_test7 :: Test
eTypeVarContextLookup_test7 () =
 case eTypeVarContextLookup context1 $ ETypeVar "Konrad" of
   Nothing -> True
   _ -> False

eTypeVarContextLookup_test8 :: Test
eTypeVarContextLookup_test8 () =
 case eTypeVarContextLookup context4 $ ETypeVar "x" of
   Just (CETypeVar (ETypeVar "x") KNat MZero) -> True
   _ -> False

eTypeVarContextLookup_test9 :: Test
eTypeVarContextLookup_test9 () =
 case eTypeVarContextLookup [CTypeVar (E $ ETypeVar "a") KStar, CETypeVar (ETypeVar "a") KNat MZero] $ ETypeVar "a" of
   Just (CTypeVar (E (ETypeVar "a")) KStar) -> True
   _ -> False

--eTypeVarContextReplace :: Context -> ETypeVar -> Monotype -> p -> Either (Error p) Context
eTypeVarContextReplace_test1 :: Test
eTypeVarContextReplace_test1 () =
  case eTypeVarContextReplace [] (ETypeVar "x") MUnit [] "1, 3" of
    Left (UndeclaredETypeVarError "1, 3" (ETypeVar "x")) -> True
    _ -> False

eTypeVarContextReplace_test2 :: Test
eTypeVarContextReplace_test2 () =
  case eTypeVarContextReplace context2 (ETypeVar "b") MUnit [] "1, 3" of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CETypeVar (ETypeVar "b") KStar MUnit, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

eTypeVarContextReplace_test3 :: Test
eTypeVarContextReplace_test3 () =
  case eTypeVarContextReplace context2 (ETypeVar "c") (MProduct MUnit MUnit) [] "1, 3" of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CTypeVar (E (ETypeVar "b")) KStar, CETypeVar (ETypeVar "c") KStar (MProduct MUnit MUnit)] -> True
    _ -> False

eTypeVarContextReplace_test4 :: Test
eTypeVarContextReplace_test4 () =
  case eTypeVarContextReplace context1 (ETypeVar "b") (MSucc MZero) [] "1, 3" of
    Right c -> c == context1
    _ -> False

eTypeVarContextReplace_test5 :: Test
eTypeVarContextReplace_test5 () =
  case eTypeVarContextReplace context1 (ETypeVar "a") MUnit [] "1, 3" of
    Right c -> c == context3
    _ -> False

eTypeVarContextReplace_test6 :: Test
eTypeVarContextReplace_test6 () =
  case eTypeVarContextReplace context1 (ETypeVar "z") MUnit [] "1, 3" of
    Left (ETypeVarMismatchError "1, 3" (MProduct MUnit MUnit) MUnit) -> True
    _ -> False

eTypeVarContextReplace_test7 :: Test
eTypeVarContextReplace_test7 () =
  case eTypeVarContextReplace context1 (ETypeVar "Konrad") MUnit [] "1, 3" of
    Left (UndeclaredETypeVarError "1, 3" (ETypeVar "Konrad")) -> True
    _ -> False

eTypeVarContextReplace_test8 :: Test
eTypeVarContextReplace_test8 () =
  case eTypeVarContextReplace context4 (ETypeVar "x") MUnit [] "1, 3" of
    Left (ETypeVarMismatchError "1, 3" MZero MUnit) -> True
    _ -> False

eTypeVarContextReplace_test9 :: Test
eTypeVarContextReplace_test9 () =
  case eTypeVarContextReplace [CTypeVar (E $ ETypeVar "a") KStar, CETypeVar (ETypeVar "a") KNat MZero]
       (ETypeVar "a") (MProduct MUnit MUnit) [] () of
    Right [CETypeVar (ETypeVar "a") KStar (MProduct MUnit MUnit), CETypeVar (ETypeVar "a") KNat MZero] -> True
    _ -> False

eTypeVarContextReplace_test10 :: Test
eTypeVarContextReplace_test10 () =
  case eTypeVarContextReplace [CTypeVar (E $ ETypeVar "a") KStar, CETypeVar (ETypeVar "a") KNat MZero]
       (ETypeVar "a") (MProduct MUnit MUnit) [CTypeVar (E (ETypeVar "b")) KStar] () of
    Right [CETypeVar (ETypeVar "a") KStar (MProduct MUnit MUnit), CTypeVar (E (ETypeVar "b")) KStar, CETypeVar (ETypeVar "a") KNat MZero] -> True
    _ -> False

eTypeVarContextReplace_test11 :: Test
eTypeVarContextReplace_test11 () =
  case eTypeVarContextReplace context2 (ETypeVar "b") (MProduct MUnit MUnit)
        [CTypeVar (E (ETypeVar "t")) KStar, CUTypeVarEq (UTypeVar "r") MZero, CETypeVar (ETypeVar "c") KStar MUnit] () of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CETypeVar (ETypeVar "b") KStar (MProduct MUnit MUnit), CTypeVar (E (ETypeVar "t")) KStar,
           CUTypeVarEq (UTypeVar "r") MZero, CETypeVar (ETypeVar "c") KStar MUnit, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

--unsolvedTypeVarContextLookup :: Context -> TypeVar -> Maybe ContextEntry
unsolvedTypeVarContextLookup_test1 :: Test
unsolvedTypeVarContextLookup_test1 () =
  case unsolvedTypeVarContextLookup [] $ U $ UTypeVar "x" of
    Nothing -> True
    _ -> False

unsolvedTypeVarContextLookup_test2 :: Test
unsolvedTypeVarContextLookup_test2 () =
  case unsolvedTypeVarContextLookup [] $ U $ UTypeVar "x" of
    Nothing -> True
    _ -> False

unsolvedTypeVarContextLookup_test3 :: Test
unsolvedTypeVarContextLookup_test3 () =
  case unsolvedTypeVarContextLookup context1 $ U $ UTypeVar "y" of
    Just (CTypeVar (U (UTypeVar "y")) KStar) -> True
    _ -> False

unsolvedTypeVarContextLookup_test4 :: Test
unsolvedTypeVarContextLookup_test4 () =
 case unsolvedTypeVarContextLookup context1 $ E $ ETypeVar "a" of
   Just (CTypeVar (E (ETypeVar "a")) KStar) -> True
   _ -> False

unsolvedTypeVarContextLookup_test5 :: Test
unsolvedTypeVarContextLookup_test5 () =
  case unsolvedTypeVarContextLookup context1 $ E $ ETypeVar "Konrad" of
    Nothing -> True
    _ -> False

unsolvedTypeVarContextLookup_test6 :: Test
unsolvedTypeVarContextLookup_test6 () =
  case unsolvedTypeVarContextLookup context4 $ E $ ETypeVar "x" of
    Just (CTypeVar (E (ETypeVar "x")) KStar) -> True
    _ -> False

unsolvedTypeVarContextLookup_test7 :: Test
unsolvedTypeVarContextLookup_test7 () =
  case unsolvedTypeVarContextLookup context5 $ U $ UTypeVar "x" of
    Just (CTypeVar (U (UTypeVar "x")) KNat) -> True
    _ -> False

--monotypeToType :: Monotype -> p -> Either (Error p) Type
monotypeToType_test1 :: Test
monotypeToType_test1 () =
  case monotypeToType (MArrow (MProduct MUnit MUnit) (MCoproduct (MUVar $ UTypeVar "x") (MEVar $ ETypeVar "y"))) () of
    Right (TArrow (TProduct TUnit TUnit) (TCoproduct (TUVar (UTypeVar "x")) (TEVar (ETypeVar "y")))) -> True
    _ -> False

monotypeToType_test2 :: Test
monotypeToType_test2 () =
  case monotypeToType (MSucc (MSucc (MSucc MZero))) () of
    Left (MonotypeIsNotTypeError () (MSucc (MSucc (MSucc MZero)))) -> True
    _ -> False

monotypeToType_test3 :: Test
monotypeToType_test3 () =
  case monotypeToType (MArrow (MProduct MUnit $ MSucc MZero) (MCoproduct (MUVar $ UTypeVar "x") (MEVar $ ETypeVar "y"))) () of
    Left (MonotypeIsNotTypeError () (MSucc MZero)) -> True
    _ -> False

--applyContextToMonotype :: Context -> Monotype -> Monotype
applyContextToMonotype_test1 :: Test
applyContextToMonotype_test1 () =
  case applyContextToMonotype [] (MArrow (MProduct MUnit MUnit) (MCoproduct (MUVar $ UTypeVar "x") (MEVar $ ETypeVar "y"))) () of
    Left (UndeclaredETypeVarError () (ETypeVar "y")) -> True
    _ -> False

applyContextToMonotype_test2 :: Test
applyContextToMonotype_test2 () =
  case applyContextToMonotype context5 (MArrow (MProduct MUnit MUnit) (MCoproduct (MUVar $ UTypeVar "x") (MEVar $ ETypeVar "x"))) () of
    Right (MArrow (MProduct MUnit MUnit) (MCoproduct MZero (MSucc MZero))) -> True
    _ -> False

applyContextToMonotype_test3 :: Test
applyContextToMonotype_test3 () =
  case applyContextToMonotype context5 (MArrow (MProduct MUnit MUnit) (MCoproduct (MUVar $ UTypeVar "y") (MEVar $ ETypeVar "x"))) () of
    Right (MArrow (MProduct MUnit MUnit) (MCoproduct (MUVar (UTypeVar "y")) (MSucc MZero))) -> True
    _ -> False

applyContextToMonotype_test4 :: Test
applyContextToMonotype_test4 () =
  case applyContextToMonotype context1 (MArrow (MProduct MUnit MUnit) (MCoproduct (MUVar $ UTypeVar "k") (MEVar $ ETypeVar "z"))) () of
    Right (MArrow (MProduct MUnit MUnit) (MCoproduct MUnit (MProduct MUnit MUnit))) -> True
    _ -> False

--applyContextToProposition :: Context -> Proposition -> Proposition
applyContextToProposition_test1 :: Test
applyContextToProposition_test1 () =
  case applyContextToProposition context5 (MUnit, MUnit) () of
    Right (MUnit, MUnit) -> True
    _ -> False

applyContextToProposition_test2 :: Test
applyContextToProposition_test2 () =
  case applyContextToProposition [] (MUVar (UTypeVar "x"), MEVar (ETypeVar "y")) () of
    Left (UndeclaredETypeVarError () (ETypeVar "y")) -> True
    _ -> False

applyContextToProposition_test3 :: Test
applyContextToProposition_test3 () =
  case applyContextToProposition context5 (MUVar (UTypeVar "x"), MEVar (ETypeVar "x")) () of
    Right (MZero, MSucc MZero) -> True
    _ -> False

--applyContextToType :: Context -> Type -> p-> Either (Error p) Type
applyContextToType_test1 :: Test
applyContextToType_test1 () =
  case applyContextToType [] (TArrow (TProduct TUnit TUnit) (TCoproduct (TUVar $ UTypeVar "x") (TEVar $ ETypeVar "y"))) () of
    Left (UndeclaredETypeVarError () (ETypeVar "y")) -> True
    _ -> False

applyContextToType_test2 :: Test
applyContextToType_test2 () =
  case applyContextToType context5 (TArrow (TProduct TUnit TUnit) (TCoproduct (TUVar $ UTypeVar "x") (TEVar $ ETypeVar "x"))) () of
    Left (MonotypeIsNotTypeError () MZero) -> True
    _ -> False

applyContextToType_test3 :: Test
applyContextToType_test3 () =
  case applyContextToType context5 (TArrow (TProduct TUnit TUnit) (TCoproduct (TUVar $ UTypeVar "y") (TEVar $ ETypeVar "x"))) () of
    Left (TypeHasWrongKindError () (TEVar (ETypeVar "x")) KStar KNat) -> True
    _ -> False

applyContextToType_test4 :: Test
applyContextToType_test4 () =
  case applyContextToType context1 (TArrow (TProduct TUnit TUnit) (TCoproduct (TUVar $ UTypeVar "k") (TEVar $ ETypeVar "z"))) () of
    Right (TArrow (TProduct TUnit TUnit) (TCoproduct TUnit (TProduct TUnit TUnit))) -> True
    _ -> False

applyContextToType_test5 :: Test
applyContextToType_test5 () =
  case applyContextToType context5 (TVec (MUVar $ UTypeVar "x") (TCoproduct TUnit TUnit)) () of
    Right (TVec MZero (TCoproduct TUnit TUnit)) -> True
    _ -> False

applyContextToType_test6 :: Test
applyContextToType_test6 () =
  case applyContextToType context5 (TImp (MUVar $ UTypeVar "x", MZero) (TCoproduct TUnit TUnit)) () of
    Right (TImp (MZero, MZero) (TCoproduct TUnit TUnit)) -> True
    _ -> False

applyContextToType_test7 :: Test
applyContextToType_test7 () =
  case applyContextToType [CUTypeVarEq (UTypeVar "x") (MSucc (MSucc MZero))] (TImp (MUVar $ UTypeVar "x", MZero)
       (TCoproduct (TUVar $ UTypeVar "x") TUnit)) () of
    Left (MonotypeIsNotTypeError () (MSucc (MSucc MZero))) -> True
    _ -> False

applyContextToType_test8 :: Test
applyContextToType_test8 () =
  case applyContextToType context1 (TAnd (TCoproduct TUnit TUnit) (MUVar $ UTypeVar "n", MEVar $ ETypeVar "b")) () of
    Right (TAnd (TCoproduct TUnit TUnit) (MSucc (MSucc (MSucc MZero)), MSucc MZero)) -> True
    _ -> False

applyContextToType_test9 :: Test
applyContextToType_test9 () =
  case applyContextToType context1 (TAnd (TUVar $ UTypeVar "n") (MUVar $ UTypeVar "n", MEVar $ ETypeVar "b")) () of
    Left (MonotypeIsNotTypeError () (MSucc (MSucc (MSucc MZero)))) -> True
    _ -> False

applyContextToType_test10 :: Test
applyContextToType_test10 () =
  case applyContextToType context5 (TUniversal "x" KNat (TVec (MUVar $ UTypeVar "x") (TCoproduct TUnit TUnit))) () of
    Right (TUniversal "x" KNat (TVec (MUVar (UTypeVar "x")) (TCoproduct TUnit TUnit))) -> True
    _ -> False

applyContextToType_test11 :: Test
applyContextToType_test11 () =
  case applyContextToType context1 (TUniversal "x" KStar (TVec (MUVar $ UTypeVar "n") (TCoproduct TUnit TUnit))) () of
    Right (TUniversal "x" KStar (TVec (MSucc (MSucc (MSucc MZero))) (TCoproduct TUnit TUnit))) -> True
    _ -> False

applyContextToType_test12 :: Test
applyContextToType_test12 () =
  case applyContextToType context1 (TUniversal "x" KStar (TVec (MUVar $ UTypeVar "n") (TCoproduct (TUVar $ UTypeVar "x") TUnit))) () of
    Right (TUniversal "x" KStar (TVec (MSucc (MSucc (MSucc MZero))) (TCoproduct (TUVar (UTypeVar "x")) TUnit))) -> True
    _ -> False

applyContextToType_test13 :: Test
applyContextToType_test13  () =
  case applyContextToType context1 (TExistential "b" KNat (TImp (MUVar (UTypeVar "n"), MEVar (ETypeVar "b")) (TVec (MEVar (ETypeVar "b")) TUnit))) () of
    Right (TExistential "b" KNat (TImp (MSucc (MSucc (MSucc MZero)), MEVar (ETypeVar "b")) (TVec (MEVar (ETypeVar "b")) TUnit))) -> True
    _ -> False

applyContextToType_test14 :: Test
applyContextToType_test14  () =
  case applyContextToType context5 (TExistential "x" KNat (TImp (MUVar (UTypeVar "x"), MEVar (ETypeVar "x")) (TVec (MUVar (UTypeVar "x")) TUnit))) () of
    Right (TExistential "x" KNat (TImp (MZero, MEVar (ETypeVar "x")) (TVec MZero TUnit))) -> True
    _ -> False

applyContextToType_test15 :: Test
applyContextToType_test15  () =
  case applyContextToType context5 (TExistential "x" KNat (TImp (MEVar (ETypeVar "x"), MEVar (ETypeVar "x")) (TVec MZero (TUVar (UTypeVar "x"))))) "1,3" of
    Left (MonotypeIsNotTypeError "1,3" MZero) -> True
    _ -> False

--inferMonotypeKind :: Context -> Monotype -> p -> Either (Error p) Kind
inferMonotypeKind_test1 :: Test
inferMonotypeKind_test1 () =
  case inferMonotypeKind [] (MSucc $ MSucc MZero) "1, 3" of
    Right KNat -> True
    _ -> False

inferMonotypeKind_test2 :: Test
inferMonotypeKind_test2 () =
  case inferMonotypeKind [] (MSucc $ MSucc MUnit) "1, 3" of
    Left (MonotypeHasWrongKindError "1, 3" MUnit KNat KStar) -> True
    _ -> False

inferMonotypeKind_test3 :: Test
inferMonotypeKind_test3 () =
  case inferMonotypeKind context1 (MCoproduct  (MUVar $ UTypeVar "y")  (MEVar $ ETypeVar "z")) "1, 3" of
    Right KStar -> True
    _ -> False

inferMonotypeKind_test4 :: Test
inferMonotypeKind_test4 () =
  case inferMonotypeKind context1 (MArrow  (MEVar $ ETypeVar "b")  (MEVar $ ETypeVar "z")) "1, 3" of
    Left (MonotypeHasWrongKindError "1, 3" (MEVar (ETypeVar "b")) KStar KNat) -> True
    _ -> False

inferMonotypeKind_test5 :: Test
inferMonotypeKind_test5 () =
  case inferMonotypeKind context1 (MUVar $ UTypeVar "n") "1, 3" of
    Left (UndeclaredUTypeVarError "1, 3" (UTypeVar "n")) -> True
    _ -> False

inferMonotypeKind_test6 :: Test
inferMonotypeKind_test6 () =
  case inferMonotypeKind context1 (MEVar $ ETypeVar "Konrad") (1 :: Integer, 3 :: Integer) of
    Left (UndeclaredETypeVarError (1, 3) (ETypeVar "Konrad")) -> True
    _ -> False

inferMonotypeKind_test7 :: Test
inferMonotypeKind_test7 () =
  case inferMonotypeKind context2 (MArrow (MProduct MUnit MUnit) (MEVar $ ETypeVar "c")) "1, 3" of
    Right KStar -> True
    _ -> False

inferMonotypeKind_test8 :: Test
inferMonotypeKind_test8 () =
  case inferMonotypeKind context2 (MCoproduct (MProduct MUnit MUnit) (MSucc $ MSucc MZero)) ("1", "3") of
    Left (MonotypeHasWrongKindError ("1", "3") (MSucc (MSucc MZero)) KStar KNat) -> True
    _ -> False

--checkMonotypeHasKind :: Context -> Monotype -> p -> Kind -> Either (Error p) ()
checkMonotypeHasKind_test1 :: Test
checkMonotypeHasKind_test1 () =
  case checkMonotypeHasKind [] (MArrow MUnit MUnit) "3.14" KStar of
    Right () -> True
    _ -> False

checkMonotypeHasKind_test2 :: Test
checkMonotypeHasKind_test2 () =
  case checkMonotypeHasKind context5 (MSucc $ MSucc (MEVar $ ETypeVar "x")) () KNat of
    Right () -> True
    _ -> False

checkMonotypeHasKind_test3 :: Test
checkMonotypeHasKind_test3 () =
  case checkMonotypeHasKind [CTypeVar (E $ ETypeVar "a") KStar, CETypeVar (ETypeVar "a") KNat MZero] (MSucc $ MSucc (MEVar $ ETypeVar "a")) () KNat of
    Left (MonotypeHasWrongKindError () (MEVar (ETypeVar "a")) KNat KStar) -> True
    _ -> False

checkMonotypeHasKind_test4 :: Test
checkMonotypeHasKind_test4 () =
  case checkMonotypeHasKind [CTypeVar (E $ ETypeVar "a") KStar, CETypeVar (ETypeVar "a") KNat MZero] (MArrow MUnit (MEVar $ ETypeVar "a")) () KStar of
    Right () -> True
    _ -> False

checkMonotypeHasKind_test5 :: Test
checkMonotypeHasKind_test5 () =
  case checkMonotypeHasKind context5 (MSucc $ MSucc (MUVar $ UTypeVar "x")) () KNat of
    Right () -> True
    _ -> False

checkMonotypeHasKind_test6 :: Test
checkMonotypeHasKind_test6 () =
  case checkMonotypeHasKind context5 (MSucc $ MSucc (MUVar $ UTypeVar "xx")) () KNat of
    Left (UndeclaredUTypeVarError () (UTypeVar "xx")) -> True
    _ -> False

checkMonotypeHasKind_test7 :: Test
checkMonotypeHasKind_test7 () =
  case checkMonotypeHasKind context5 (MSucc $ MSucc (MEVar $ ETypeVar "")) () KNat of
    Left (UndeclaredETypeVarError () (ETypeVar "")) -> True
    _ -> False

--checkPropWellFormedness :: Context -> Proposition -> p -> Either (Error p) ()
checkPropWellFormedness_test1 :: Test
checkPropWellFormedness_test1 () =
  case checkPropWellFormedness [] (MZero, MZero) (5 :: Integer) of
    Right () -> True
    _ -> False

checkPropWellFormedness_test2 :: Test
checkPropWellFormedness_test2 () =
  case checkPropWellFormedness [] (MZero, MSucc $ MSucc MZero) (5 :: Integer) of
    Right () -> True
    _ -> False

checkPropWellFormedness_test3 :: Test
checkPropWellFormedness_test3 () =
  case checkPropWellFormedness [] (MSucc $ MSucc MZero, MProduct MUnit MUnit) (5 :: Integer) of
    Left (MonotypeHasWrongKindError 5 (MProduct MUnit MUnit) KNat KStar) -> True
    _ -> False

checkPropWellFormedness_test4 :: Test
checkPropWellFormedness_test4 () =
  case checkPropWellFormedness [] (MSucc $ MSucc MZero, MProduct MUnit $ MSucc MZero) (5 :: Integer) of
    Left (MonotypeHasWrongKindError 5 (MSucc MZero) KStar KNat) -> True
    _ -> False

checkPropWellFormedness_test5 :: Test
checkPropWellFormedness_test5 () =
  case checkPropWellFormedness context1 (MSucc $ MSucc  (MEVar $ ETypeVar "b"), MProduct MUnit $ MSucc MZero) () of
    Left (MonotypeHasWrongKindError () (MSucc MZero) KStar KNat) -> True
    _ -> False

checkPropWellFormedness_test6 :: Test
checkPropWellFormedness_test6 () =
  case checkPropWellFormedness context5 (MSucc $ MSucc  (MUVar $ UTypeVar "x"), MEVar $ ETypeVar "x") () of
    Right () -> True
    _ -> False

checkPropWellFormedness_test7 :: Test
checkPropWellFormedness_test7 () =
  case checkPropWellFormedness context5 (MSucc $ MSucc  (MUVar $ UTypeVar "r"), MEVar $ ETypeVar "x") () of
    Left (UndeclaredUTypeVarError () (UTypeVar "r")) -> True
    _ -> False

--checkTypeWellFormedness :: Context -> Type -> p -> Either (Error p) ()
checkTypeWellFormedness_test1 :: Test
checkTypeWellFormedness_test1 () =
  case checkTypeWellFormedness context1 (TArrow TUnit $ TCoproduct TUnit (TProduct TUnit TUnit)) () of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test2 :: Test
checkTypeWellFormedness_test2 () =
  case checkTypeWellFormedness context1 (TCoproduct (TUVar $ UTypeVar "y") (TProduct (TEVar $ ETypeVar "z") (TEVar $ ETypeVar "a"))) () of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test3 :: Test
checkTypeWellFormedness_test3 () =
  case checkTypeWellFormedness context1 (TCoproduct (TUVar $ UTypeVar "y") (TProduct (TEVar $ ETypeVar "z") (TEVar $ ETypeVar "b"))) ((),()) of
    Left (TypeHasWrongKindError ((), ()) (TEVar (ETypeVar "b")) KStar KNat) -> True
    _ -> False

checkTypeWellFormedness_test4 :: Test
checkTypeWellFormedness_test4 () =
  case checkTypeWellFormedness [] (TCoproduct (TUVar $ UTypeVar "y") (TProduct (TEVar $ ETypeVar "z") (TEVar $ ETypeVar "b"))) ((),()) of
    Left (UndeclaredUTypeVarError ((), ()) (UTypeVar "y")) -> True
    _ -> False

checkTypeWellFormedness_test5 :: Test
checkTypeWellFormedness_test5 () =
  case checkTypeWellFormedness [] (TProduct (TEVar $ ETypeVar "z") (TEVar $ ETypeVar "b")) ((),()) of
    Left (UndeclaredETypeVarError ((), ()) (ETypeVar "z")) -> True
    _ -> False

checkTypeWellFormedness_test6 :: Test
checkTypeWellFormedness_test6 () =
  case checkTypeWellFormedness context5 (TUVar $ UTypeVar "x") (5 :: Integer) of
    Left (TypeHasWrongKindError 5 (TUVar (UTypeVar "x")) KStar KNat) -> True
    _ -> False

checkTypeWellFormedness_test7 :: Test
checkTypeWellFormedness_test7 () =
  case checkTypeWellFormedness context5 (TUniversal "x" KStar (TArrow (TUVar $ UTypeVar "x") TUnit)) () of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test8 :: Test
checkTypeWellFormedness_test8 () =
  case checkTypeWellFormedness context5 (TUniversal "Konrad" KStar (TArrow (TUVar $ UTypeVar "Konrad") TUnit)) () of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test9 :: Test
checkTypeWellFormedness_test9 () =
  case checkTypeWellFormedness [] (TUniversal "Konrad" KStar (TArrow (TUVar $ UTypeVar "Konrad") TUnit)) () of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test10 :: Test
checkTypeWellFormedness_test10 () =
  case checkTypeWellFormedness context1 (TExistential "b" KStar (TArrow (TEVar $ ETypeVar "b") TUnit)) () of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test11 :: Test
checkTypeWellFormedness_test11 () =
  case checkTypeWellFormedness context1 (TExistential "Konrad" KStar (TArrow (TEVar $ ETypeVar "Konrad") TUnit)) () of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test12 :: Test
checkTypeWellFormedness_test12 () =
  case checkTypeWellFormedness [] (TExistential "Konrad" KStar (TArrow (TEVar $ ETypeVar "Konrad") TUnit)) () of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test13 :: Test
checkTypeWellFormedness_test13 () =
  case checkTypeWellFormedness [] (TUniversal "x" KStar (TArrow (TUVar $ UTypeVar "y") TUnit)) () of
    Left (UndeclaredUTypeVarError () (UTypeVar "y")) -> True
    _ -> False

checkTypeWellFormedness_test14 :: Test
checkTypeWellFormedness_test14 () =
  case checkTypeWellFormedness [] (TExistential "x" KStar (TArrow (TEVar $ ETypeVar "y") TUnit)) () of
    Left (UndeclaredETypeVarError () (ETypeVar "y")) -> True
    _ -> False

checkTypeWellFormedness_test15 :: Test
checkTypeWellFormedness_test15 () =
  case checkTypeWellFormedness context1 (TImp (MZero, MSucc MZero) (TArrow (TEVar $ ETypeVar "z") TUnit)) () of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test16 :: Test
checkTypeWellFormedness_test16 () =
  case checkTypeWellFormedness [] (TImp (MZero, MZero) (TArrow (TEVar $ ETypeVar "y") TUnit)) () of
    Left (UndeclaredETypeVarError () (ETypeVar "y")) -> True
    _ -> False

checkTypeWellFormedness_test17 :: Test
checkTypeWellFormedness_test17 () =
  case checkTypeWellFormedness [] (TExistential "x" KStar (TImp (MZero, MSucc MZero) (TArrow (TEVar $ ETypeVar "x") TUnit))) () of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test18 :: Test
checkTypeWellFormedness_test18 () =
  case checkTypeWellFormedness [] (TExistential "x" KStar (TImp (MZero, MSucc (MEVar $ ETypeVar "x")) (TArrow (TEVar $ ETypeVar "z") TUnit))) () of
    Left (MonotypeHasWrongKindError () (MEVar (ETypeVar "x")) KNat KStar) -> True
    _ -> False

checkTypeWellFormedness_test19 :: Test
checkTypeWellFormedness_test19 () =
  case checkTypeWellFormedness context1 (TAnd (TArrow (TEVar $ ETypeVar "z") TUnit) (MEVar $ ETypeVar "b", MSucc MZero)) () of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test20 :: Test
checkTypeWellFormedness_test20 () =
  case checkTypeWellFormedness context1 (TAnd (TArrow (TUVar $ UTypeVar "Haskell") TUnit) (MEVar $ ETypeVar "Konrad", MSucc MZero)) () of
    Left (UndeclaredUTypeVarError () (UTypeVar "Haskell")) -> True
    _ -> False

checkTypeWellFormedness_test21 :: Test
checkTypeWellFormedness_test21 () =
  case checkTypeWellFormedness [] (TUniversal "x" KStar (TAnd (TArrow (TUVar $ UTypeVar "x") TUnit)  (MUVar $ UTypeVar "x", MUnit))) () of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test22 :: Test
checkTypeWellFormedness_test22 () =
  case checkTypeWellFormedness [] (TUniversal "x" KStar (TAnd (TArrow (TUVar $ UTypeVar "x") TUnit)  (MEVar $ ETypeVar "x", MUnit))) () of
    Left (UndeclaredETypeVarError () (ETypeVar "x")) -> True
    _ -> False

checkTypeWellFormedness_test23 :: Test
checkTypeWellFormedness_test23 () =
  case checkTypeWellFormedness context1 (TVec (MSucc $ MSucc (MEVar $ ETypeVar "b")) (TProduct TUnit TUnit)) () of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test24 :: Test
checkTypeWellFormedness_test24 () =
  case checkTypeWellFormedness [] (TUniversal "n" KNat $ TVec (MSucc $ MSucc (MUVar $ UTypeVar "n")) (TProduct TUnit (TUVar $ UTypeVar "n"))) () of
    Left (TypeHasWrongKindError () (TUVar (UTypeVar "n")) KStar KNat) -> True
    _ -> False

checkTypeWellFormedness_test25 :: Test
checkTypeWellFormedness_test25 () =
  case checkTypeWellFormedness [] (TExistential "x" KStar $ TVec (MSucc $ MSucc (MEVar $ ETypeVar "x")) (TProduct TUnit TUnit)) () of
    Left (MonotypeHasWrongKindError () (MEVar (ETypeVar "x")) KNat KStar) -> True
    _ -> False

checkTypeWellFormedness_test26 :: Test
checkTypeWellFormedness_test26 () =
  case checkTypeWellFormedness context1 (TUniversal "n" KNat $ TVec (MSucc $ MSucc (MUVar $ UTypeVar "n"))
       (TImp (MEVar $ ETypeVar "b", MUVar $ UTypeVar "n") (TProduct TUnit TUnit))) () of
    Right () -> True
    _ -> False

--checkTypeWellFormednessWithPrnc :: Context -> Type -> Principality -> p -> Either (Error p) ()
checkTypeWellFormednessWithPrnc_test1 :: Test
checkTypeWellFormednessWithPrnc_test1 () =
  case checkTypeWellFormednessWithPrnc context1 (TArrow TUnit $ TCoproduct TUnit (TProduct TUnit TUnit)) Principal () of
    Right () -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test2 :: Test
checkTypeWellFormednessWithPrnc_test2 () =
  case checkTypeWellFormednessWithPrnc context1 (TCoproduct (TUVar $ UTypeVar "y") (TProduct (TEVar $ ETypeVar "z") (TEVar $ ETypeVar "a"))) Principal () of
    Left (TypeFormednessPrcFEVError () [ETypeVar "a", ETypeVar "z"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test3 :: Test
checkTypeWellFormednessWithPrnc_test3 () =
  case checkTypeWellFormednessWithPrnc context1 (TCoproduct (TUVar $ UTypeVar "y") (TProduct (TEVar $ ETypeVar "z") (TEVar $ ETypeVar "b"))) Principal ((),()) of
    Left (TypeFormednessPrcFEVError ((),()) [ETypeVar "b", ETypeVar "z"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test4 :: Test
checkTypeWellFormednessWithPrnc_test4 () =
  case checkTypeWellFormednessWithPrnc [] (TCoproduct (TUVar $ UTypeVar "y") (TProduct (TEVar $ ETypeVar "z") (TEVar $ ETypeVar "b"))) Principal ((),()) of
    Left (TypeFormednessPrcFEVError ((),()) [ETypeVar "b", ETypeVar "z"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test5 :: Test
checkTypeWellFormednessWithPrnc_test5 () =
  case checkTypeWellFormednessWithPrnc [] (TProduct (TEVar $ ETypeVar "z") (TEVar $ ETypeVar "b")) Principal ((),()) of
    Left (TypeFormednessPrcFEVError ((),()) [ETypeVar "b", ETypeVar "z"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test6 :: Test
checkTypeWellFormednessWithPrnc_test6 () =
  case checkTypeWellFormednessWithPrnc context5 (TUVar $ UTypeVar "x") Principal (5 :: Integer) of
    Left (TypeHasWrongKindError 5 (TUVar (UTypeVar "x")) KStar KNat) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test7 :: Test
checkTypeWellFormednessWithPrnc_test7 () =
  case checkTypeWellFormednessWithPrnc context5 (TUniversal "x" KStar (TArrow (TUVar $ UTypeVar "x") TUnit)) Principal () of
    Right () -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test8 :: Test
checkTypeWellFormednessWithPrnc_test8 () =
  case checkTypeWellFormednessWithPrnc context5 (TUniversal "Konrad" KStar (TArrow (TUVar $ UTypeVar "Konrad") TUnit)) Principal () of
    Right () -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test9 :: Test
checkTypeWellFormednessWithPrnc_test9 () =
  case checkTypeWellFormednessWithPrnc [] (TUniversal "Konrad" KStar (TArrow (TUVar $ UTypeVar "Konrad") TUnit)) Principal () of
    Right () -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test10 :: Test
checkTypeWellFormednessWithPrnc_test10 () =
  case checkTypeWellFormednessWithPrnc context1 (TExistential "b" KStar (TArrow (TEVar $ ETypeVar "b") TUnit)) Principal () of
    Right () -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test11 :: Test
checkTypeWellFormednessWithPrnc_test11 () =
  case checkTypeWellFormednessWithPrnc context1 (TExistential "Konrad" KStar (TArrow (TEVar $ ETypeVar "Konrad") TUnit)) Principal () of
    Right () -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test12 :: Test
checkTypeWellFormednessWithPrnc_test12 () =
  case checkTypeWellFormednessWithPrnc [] (TExistential "Konrad" KStar (TArrow (TEVar $ ETypeVar "Konrad") TUnit)) Principal () of
    Right () -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test13 :: Test
checkTypeWellFormednessWithPrnc_test13 () =
  case checkTypeWellFormednessWithPrnc [] (TUniversal "x" KStar (TArrow (TUVar $ UTypeVar "y") TUnit)) Principal () of
    Left (UndeclaredUTypeVarError () (UTypeVar "y")) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test14 :: Test
checkTypeWellFormednessWithPrnc_test14 () =
  case checkTypeWellFormednessWithPrnc [] (TExistential "x" KStar (TArrow (TEVar $ ETypeVar "y") TUnit)) Principal () of
    Left (TypeFormednessPrcFEVError () [ETypeVar "y"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test15 :: Test
checkTypeWellFormednessWithPrnc_test15 () =
  case checkTypeWellFormednessWithPrnc context1 (TImp (MZero, MSucc MZero) (TArrow (TEVar $ ETypeVar "z") TUnit)) Principal () of
    Left (TypeFormednessPrcFEVError () [ETypeVar "z"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test16 :: Test
checkTypeWellFormednessWithPrnc_test16 () =
  case checkTypeWellFormednessWithPrnc [] (TImp (MZero, MZero) (TArrow (TEVar $ ETypeVar "y") TUnit)) Principal () of
    Left (TypeFormednessPrcFEVError () [ETypeVar "y"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test17 :: Test
checkTypeWellFormednessWithPrnc_test17 () =
  case checkTypeWellFormednessWithPrnc [] (TExistential "x" KStar (TImp (MZero, MSucc MZero) (TArrow (TEVar $ ETypeVar "x") TUnit))) Principal () of
    Right () -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test18 :: Test
checkTypeWellFormednessWithPrnc_test18 () =
  case checkTypeWellFormednessWithPrnc [] (TExistential "x" KStar (TImp (MZero, MSucc (MEVar $ ETypeVar "x"))
       (TArrow (TEVar $ ETypeVar "z") TUnit))) Principal () of
    Left (TypeFormednessPrcFEVError () [ETypeVar "z"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test19 :: Test
checkTypeWellFormednessWithPrnc_test19 () =
  case checkTypeWellFormednessWithPrnc context1 (TAnd (TArrow (TEVar $ ETypeVar "z") TUnit) (MEVar $ ETypeVar "b", MSucc MZero)) Principal () of
    Left (TypeFormednessPrcFEVError () [ETypeVar "b", ETypeVar "z"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test20 :: Test
checkTypeWellFormednessWithPrnc_test20 () =
  case checkTypeWellFormednessWithPrnc context1 (TAnd (TArrow (TUVar $ UTypeVar "Haskell") TUnit) (MEVar $ ETypeVar "Konrad", MSucc MZero)) Principal () of
    Left (TypeFormednessPrcFEVError () [ETypeVar "Konrad"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test21 :: Test
checkTypeWellFormednessWithPrnc_test21 () =
  case checkTypeWellFormednessWithPrnc [] (TUniversal "x" KStar (TAnd (TArrow (TUVar $ UTypeVar "x") TUnit)  (MUVar $ UTypeVar "x", MUnit))) Principal () of
    Right () -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test22 :: Test
checkTypeWellFormednessWithPrnc_test22 () =
  case checkTypeWellFormednessWithPrnc [] (TUniversal "x" KStar (TAnd (TArrow (TUVar $ UTypeVar "x") TUnit)  (MEVar $ ETypeVar "x", MUnit))) Principal () of
    Left (TypeFormednessPrcFEVError () [ETypeVar "x"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test23 :: Test
checkTypeWellFormednessWithPrnc_test23 () =
  case checkTypeWellFormednessWithPrnc context1 (TVec (MSucc $ MSucc (MEVar $ ETypeVar "b")) (TProduct TUnit TUnit)) Principal () of
    Left (TypeFormednessPrcFEVError () [ETypeVar "b"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test24 :: Test
checkTypeWellFormednessWithPrnc_test24 () =
  case checkTypeWellFormednessWithPrnc [] (TUniversal "n" KNat $ TVec (MSucc $ MSucc (MUVar $ UTypeVar "n"))
       (TProduct TUnit (TUVar $ UTypeVar "n"))) Principal () of
    Left (TypeHasWrongKindError () (TUVar (UTypeVar "n")) KStar KNat) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test25 :: Test
checkTypeWellFormednessWithPrnc_test25 () =
  case checkTypeWellFormednessWithPrnc [] (TExistential "x" KStar $ TVec (MSucc $ MSucc (MEVar $ ETypeVar "x")) (TProduct TUnit TUnit)) Principal () of
    Left (MonotypeHasWrongKindError () (MEVar (ETypeVar "x")) KNat KStar) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test26 :: Test
checkTypeWellFormednessWithPrnc_test26 () =
  case checkTypeWellFormednessWithPrnc context1 (TUniversal "n" KNat $ TVec (MSucc $ MSucc (MUVar $ UTypeVar "n"))
       (TImp (MEVar $ ETypeVar "b", MUVar $ UTypeVar "n") (TProduct TUnit TUnit))) Principal () of
    Left (TypeFormednessPrcFEVError () [ETypeVar "b"]) -> True
    _ -> False

--checkExpr :: Context -> Expr p -> Type -> Principality -> Either (Error p) Context
checkExpr_EUnit_test1 :: Test
checkExpr_EUnit_test1 () =
  case checkExpr context1 (EUnit ()) TUnit Principal of
    Right c -> c == context1
    _ -> False

checkExpr_EUnit_test2 :: Test
checkExpr_EUnit_test2 () =
  case checkExpr [] (EUnit ()) TUnit NotPrincipal of
    Right [] -> True
    _ -> False

checkExpr_EUnit_test3 :: Test
checkExpr_EUnit_test3 () =
  case checkExpr context1 (EUnit ()) (TEVar $ ETypeVar "a") Principal of
    Right c -> c == context3
    _ -> False

checkExpr_EUnit_test4 :: Test
checkExpr_EUnit_test4 () =
  case checkExpr context1 (EUnit ()) (TEVar $ ETypeVar "z") Principal of
    Left (ETypeVarMismatchError () (MProduct MUnit MUnit) MUnit) -> True
    _ -> False

checkExpr_EUnit_test5 :: Test
checkExpr_EUnit_test5 () =
  case checkExpr context3 (EUnit ()) (TEVar $ ETypeVar "a") Principal of
    Right c -> c == context3
    _ -> False

checkExpr_EUnit_test6 :: Test
checkExpr_EUnit_test6 () =
  case checkExpr context3 (EUnit ()) (TEVar $ ETypeVar "Konrad") Principal of
    Left (UndeclaredETypeVarError () (ETypeVar "Konrad")) -> True
    _ -> False

checkExpr_EUnit_test7 :: Test
checkExpr_EUnit_test7 () =
  case checkExpr context3 (EUnit ()) (TEVar $ ETypeVar "a") Principal of
    Right c -> c == context3
    _ -> False

checkExpr_EPair_test1 :: Test
checkExpr_EPair_test1 () =
  case checkExpr context1 (EPair () (EUnit ()) (EUnit ())) (TProduct TUnit TUnit) Principal of
    Right c -> c == context1
    _ -> False

checkExpr_EPair_test2 :: Test
checkExpr_EPair_test2 () =
  case checkExpr context5 (EPair () (EPair () (EUnit ()) (EUnit ())) (EUnit ())) (TProduct (TProduct TUnit TUnit) TUnit) NotPrincipal of
    Right c -> c == context5
    _ -> False

checkExpr_EPair_test3 :: Test
checkExpr_EPair_test3 () =
  case checkExpr [CTypeVar (E $ ETypeVar "x") KStar] (EPair () (EPair () (EUnit ()) (EUnit ())) (EUnit ())) (TEVar $ ETypeVar "x") Principal of
    Right c -> c == [CETypeVar (ETypeVar "x") KStar (MProduct (MEVar (ETypeVar "x-1")) (MEVar (ETypeVar "x-2"))),
                     CETypeVar (ETypeVar "x-1") KStar (MProduct (MEVar (ETypeVar "x-1-1")) (MEVar (ETypeVar "x-1-2"))),
                     CETypeVar (ETypeVar "x-1-1") KStar MUnit, CETypeVar (ETypeVar "x-1-2") KStar MUnit, CETypeVar (ETypeVar "x-2") KStar MUnit]
    _ -> False

checkExpr_EPair_test4 :: Test
checkExpr_EPair_test4 () =
  case checkExpr context1 (EPair () (EUnit ()) (EUnit ())) (TEVar $ ETypeVar "z") Principal of
    Left (ETypeVarMismatchError ()  (MProduct MUnit MUnit) (MProduct (MEVar (ETypeVar "z-1")) (MEVar (ETypeVar "z-2")))) -> True
    _ -> False

checkExpr_EPair_test5 :: Test
checkExpr_EPair_test5 () =
  case checkExpr [CETypeVar (ETypeVar "x") KStar (MProduct (MEVar (ETypeVar "x-1")) (MEVar (ETypeVar "x-2"))),
                  CETypeVar (ETypeVar "x-1") KStar MUnit, CETypeVar (ETypeVar "x-2") KStar MUnit]
                  (EPair () (EUnit ()) (EUnit ())) (TEVar $ ETypeVar "x") Principal of
    Right c -> c == [CETypeVar (ETypeVar "x") KStar (MProduct (MEVar (ETypeVar "x-1")) (MEVar (ETypeVar "x-2"))),
                     CETypeVar (ETypeVar "x-1") KStar MUnit, CETypeVar (ETypeVar "x-2") KStar MUnit]
    _ -> False

checkExpr_EPair_test6 :: Test
checkExpr_EPair_test6 () =
  case checkExpr context1 (EPair () (EUnit ()) (EUnit ())) (TEVar $ ETypeVar "zz") Principal of
    Left (UndeclaredETypeVarError () (ETypeVar "zz")) -> True
    _ -> False

checkExpr_EPair_test7 :: Test
checkExpr_EPair_test7 () =
  case checkExpr [CTypeVar (E $ ETypeVar "x") KStar] (EPair () (EPair () (EPair () (EUnit ()) (EUnit ())) (EUnit ()))
                 (EPair () (EUnit ()) (EUnit ()))) (TProduct (TEVar $ ETypeVar "x") (TEVar $ ETypeVar "x")) Principal of
    Left (ETypeVarMismatchError () (MProduct (MEVar (ETypeVar "x-1-1")) (MEVar(ETypeVar "x-1-2"))) MUnit) -> True
    _ -> False

checkExpr_EPair_test8 :: Test
checkExpr_EPair_test8 () =
  case checkExpr [CTypeVar (E $ ETypeVar "x") KStar] (EPair () (EPair () (EUnit ()) (EUnit ()))
                 (EPair () (EUnit ()) (EUnit ()))) (TProduct (TEVar $ ETypeVar "x") (TEVar $ ETypeVar "x")) Principal of
    Right c -> c == [CETypeVar (ETypeVar "x") KStar (MProduct (MEVar (ETypeVar "x-1")) (MEVar (ETypeVar "x-2"))),
                     CETypeVar (ETypeVar "x-1") KStar MUnit, CETypeVar (ETypeVar "x-2") KStar MUnit]
    _ -> False

--inferExpr :: Context -> Expr p -> Either (Error p) (Type, Principality, Context)
inferExpr_EVar_test1 :: Test
inferExpr_EVar_test1 () =
  case inferExpr context1 (EVar () "r") of
    Right (TProduct TUnit TUnit, NotPrincipal, c) -> c == context1
    _ -> False

inferExpr_EVar_test2 :: Test
inferExpr_EVar_test2 () =
  case inferExpr context1 (EVar () "x") of
    Right (TUnit, Principal, c) -> c == context1
    _ -> False

inferExpr_EVar_test3 :: Test
inferExpr_EVar_test3 () =
  case inferExpr context5 (EVar () "x") of
    Left (MonotypeIsNotTypeError () MZero) -> True
    _ -> False

inferExpr_EVar_test4 :: Test
inferExpr_EVar_test4 () =
  case inferExpr context5 (EVar () "y") of
    Left (UndeclaredVariableError () "y") -> True
    _ -> False

inferExpr_EVar_test5 :: Test
inferExpr_EVar_test5 () =
  case inferExpr context4 (EVar () "zz") of
    Left (UndeclaredETypeVarError () (ETypeVar "r")) -> True
    _ -> False

inferExpr_EVar_test6 :: Test
inferExpr_EVar_test6 () =
  case inferExpr [CVar "zz" (TUVar $ UTypeVar "v") Principal] (EVar () "zz") of
    Right (TUVar (UTypeVar "v"), Principal, c)  -> c == [CVar "zz" (TUVar $ UTypeVar "v") Principal]
    _ -> False

inferExpr_EVar_test7 :: Test
inferExpr_EVar_test7 () =
  case inferExpr [CVar "zz" (TUVar $ UTypeVar "v") Principal, CUTypeVarEq (UTypeVar "v") (MCoproduct MUnit MUnit)] (EVar () "zz") of
    Right (TCoproduct TUnit TUnit, Principal, c)  -> c == [CVar "zz" (TUVar $ UTypeVar "v") Principal, CUTypeVarEq (UTypeVar "v") (MCoproduct MUnit MUnit)]
    _ -> False

inferExpr_EVar_test8 :: Test
inferExpr_EVar_test8 () =
  case inferExpr [] (EVar () "zz") of
    Left (UndeclaredVariableError () "zz") -> True
    _ -> False

tests :: [(TestName, Test)]
tests = [("freeExistentialVariablesOfMonotype_test1", freeExistentialVariablesOfMonotype_test1),
         ("freeExistentialVariablesOfMonotype_test2", freeExistentialVariablesOfMonotype_test2),
         ("freeExistentialVariablesOfMonotype_test3", freeExistentialVariablesOfMonotype_test3),
         ("freeExistentialVariablesOfMonotype_test4", freeExistentialVariablesOfMonotype_test4),
         ("freeExistentialVariablesOfMonotype_test5", freeExistentialVariablesOfMonotype_test5),
         ("freeExistentialVariablesOfProp_test1", freeExistentialVariablesOfProp_test1),
         ("freeExistentialVariablesOfProp_test2", freeExistentialVariablesOfProp_test2),
         ("freeExistentialVariablesOfProp_test3", freeExistentialVariablesOfProp_test3),
         ("freeExistentialVariablesOfProp_test4", freeExistentialVariablesOfProp_test4),
         ("freeExistentialVariables_test1", freeExistentialVariables_test1),
         ("freeExistentialVariables_test2", freeExistentialVariables_test2),
         ("freeExistentialVariables_test3", freeExistentialVariables_test3),
         ("freeExistentialVariables_test4", freeExistentialVariables_test4),
         ("freeExistentialVariables_test5", freeExistentialVariables_test5),
         ("freeExistentialVariables_test6", freeExistentialVariables_test6),
         ("freeExistentialVariables_test7", freeExistentialVariables_test7),
         ("varContextLookup_test1", varContextLookup_test1),
         ("varContextLookup_test2", varContextLookup_test2),
         ("varContextLookup_test3", varContextLookup_test3),
         ("varContextLookup_test4", varContextLookup_test4),
         ("varContextLookup_test5", varContextLookup_test5),
         ("varContextLookup_test6", varContextLookup_test6),
         ("varContextLookup_test7", varContextLookup_test7),
         ("varContextLookup_test8", varContextLookup_test8),
         ("varContextLookup_test9", varContextLookup_test9),
         ("uTypeVarEqContextLookup_test1", uTypeVarEqContextLookup_test1),
         ("uTypeVarEqContextLookup_test2", uTypeVarEqContextLookup_test2),
         ("uTypeVarEqContextLookup_test3", uTypeVarEqContextLookup_test3),
         ("uTypeVarEqContextLookup_test4", uTypeVarEqContextLookup_test4),
         ("uTypeVarEqContextLookup_test5", uTypeVarEqContextLookup_test5),
         ("uTypeVarEqContextLookup_test6", uTypeVarEqContextLookup_test6),
         ("uTypeVarEqContextLookup_test7", uTypeVarEqContextLookup_test7),
         ("eTypeVarContextLookup_test1", eTypeVarContextLookup_test1),
         ("eTypeVarContextLookup_test2", eTypeVarContextLookup_test2),
         ("eTypeVarContextLookup_test3", eTypeVarContextLookup_test3),
         ("eTypeVarContextLookup_test4", eTypeVarContextLookup_test4),
         ("eTypeVarContextLookup_test5", eTypeVarContextLookup_test5),
         ("eTypeVarContextLookup_test6", eTypeVarContextLookup_test6),
         ("eTypeVarContextLookup_test7", eTypeVarContextLookup_test7),
         ("eTypeVarContextLookup_test8", eTypeVarContextLookup_test8),
         ("eTypeVarContextLookup_test9", eTypeVarContextLookup_test9),
         ("eTypeVarContextReplace_test1", eTypeVarContextReplace_test1),
         ("eTypeVarContextReplace_test2", eTypeVarContextReplace_test2),
         ("eTypeVarContextReplace_test3", eTypeVarContextReplace_test3),
         ("eTypeVarContextReplace_test4", eTypeVarContextReplace_test4),
         ("eTypeVarContextReplace_test5", eTypeVarContextReplace_test5),
         ("eTypeVarContextReplace_test6", eTypeVarContextReplace_test6),
         ("eTypeVarContextReplace_test7", eTypeVarContextReplace_test7),
         ("eTypeVarContextReplace_test8", eTypeVarContextReplace_test8),
         ("eTypeVarContextReplace_test9", eTypeVarContextReplace_test9),
         ("eTypeVarContextReplace_test10", eTypeVarContextReplace_test10),
         ("eTypeVarContextReplace_test11", eTypeVarContextReplace_test11),
         ("unsolvedTypeVarContextLookup_test1", unsolvedTypeVarContextLookup_test1),
         ("unsolvedTypeVarContextLookup_test2", unsolvedTypeVarContextLookup_test2),
         ("unsolvedTypeVarContextLookup_test3", unsolvedTypeVarContextLookup_test3),
         ("unsolvedTypeVarContextLookup_test4", unsolvedTypeVarContextLookup_test4),
         ("unsolvedTypeVarContextLookup_test5", unsolvedTypeVarContextLookup_test5),
         ("unsolvedTypeVarContextLookup_test6", unsolvedTypeVarContextLookup_test6),
         ("unsolvedTypeVarContextLookup_test7", unsolvedTypeVarContextLookup_test7),
         ("monotypeToType_test1", monotypeToType_test1),
         ("monotypeToType_test2", monotypeToType_test2),
         ("monotypeToType_test3", monotypeToType_test3),
         ("applyContextToMonotype_test1", applyContextToMonotype_test1),
         ("applyContextToMonotype_test2", applyContextToMonotype_test2),
         ("applyContextToMonotype_test3", applyContextToMonotype_test3),
         ("applyContextToMonotype_test4", applyContextToMonotype_test4),
         ("applyContextToProposition_test1", applyContextToProposition_test1),
         ("applyContextToProposition_test2", applyContextToProposition_test2),
         ("applyContextToProposition_test3", applyContextToProposition_test3),
         ("applyContextToType_test1", applyContextToType_test1),
         ("applyContextToType_test2", applyContextToType_test2),
         ("applyContextToType_test3", applyContextToType_test3),
         ("applyContextToType_test4", applyContextToType_test4),
         ("applyContextToType_test5", applyContextToType_test5),
         ("applyContextToType_test6", applyContextToType_test6),
         ("applyContextToType_test7", applyContextToType_test7),
         ("applyContextToType_test8", applyContextToType_test8),
         ("applyContextToType_test9", applyContextToType_test9),
         ("applyContextToType_test10", applyContextToType_test10),
         ("applyContextToType_test11", applyContextToType_test11),
         ("applyContextToType_test12", applyContextToType_test12),
         ("applyContextToType_test13", applyContextToType_test13),
         ("applyContextToType_test14", applyContextToType_test14),
         ("applyContextToType_test15", applyContextToType_test15),
         ("inferMonotypeKind_test1", inferMonotypeKind_test1),
         ("inferMonotypeKind_test2", inferMonotypeKind_test2),
         ("inferMonotypeKind_test3", inferMonotypeKind_test3),
         ("inferMonotypeKind_test4", inferMonotypeKind_test4),
         ("inferMonotypeKind_test5", inferMonotypeKind_test5),
         ("inferMonotypeKind_test6", inferMonotypeKind_test6),
         ("inferMonotypeKind_test7", inferMonotypeKind_test7),
         ("inferMonotypeKind_test8", inferMonotypeKind_test8),
         ("checkMonotypeHasKind_test1", checkMonotypeHasKind_test1),
         ("checkMonotypeHasKind_test2", checkMonotypeHasKind_test2),
         ("checkMonotypeHasKind_test3", checkMonotypeHasKind_test3),
         ("checkMonotypeHasKind_test4", checkMonotypeHasKind_test4),
         ("checkMonotypeHasKind_test5", checkMonotypeHasKind_test5),
         ("checkMonotypeHasKind_test6", checkMonotypeHasKind_test6),
         ("checkMonotypeHasKind_test7", checkMonotypeHasKind_test7),
         ("checkPropWellFormedness_test1", checkPropWellFormedness_test1),
         ("checkPropWellFormedness_test2", checkPropWellFormedness_test2),
         ("checkPropWellFormedness_test3", checkPropWellFormedness_test3),
         ("checkPropWellFormedness_test4", checkPropWellFormedness_test4),
         ("checkPropWellFormedness_test5", checkPropWellFormedness_test5),
         ("checkPropWellFormedness_test6", checkPropWellFormedness_test6),
         ("checkPropWellFormedness_test7", checkPropWellFormedness_test7),
         ("checkTypeWellFormedness_test1", checkTypeWellFormedness_test1),
         ("checkTypeWellFormedness_test2", checkTypeWellFormedness_test2),
         ("checkTypeWellFormedness_test3", checkTypeWellFormedness_test3),
         ("checkTypeWellFormedness_test4", checkTypeWellFormedness_test4),
         ("checkTypeWellFormedness_test5", checkTypeWellFormedness_test5),
         ("checkTypeWellFormedness_test6", checkTypeWellFormedness_test6),
         ("checkTypeWellFormedness_test7", checkTypeWellFormedness_test7),
         ("checkTypeWellFormedness_test8", checkTypeWellFormedness_test8),
         ("checkTypeWellFormedness_test9", checkTypeWellFormedness_test9),
         ("checkTypeWellFormedness_test10", checkTypeWellFormedness_test10),
         ("checkTypeWellFormedness_test11", checkTypeWellFormedness_test11),
         ("checkTypeWellFormedness_test12", checkTypeWellFormedness_test12),
         ("checkTypeWellFormedness_test13", checkTypeWellFormedness_test13),
         ("checkTypeWellFormedness_test14", checkTypeWellFormedness_test14),
         ("checkTypeWellFormedness_test15", checkTypeWellFormedness_test15),
         ("checkTypeWellFormedness_test16", checkTypeWellFormedness_test16),
         ("checkTypeWellFormedness_test17", checkTypeWellFormedness_test17),
         ("checkTypeWellFormedness_test18", checkTypeWellFormedness_test18),
         ("checkTypeWellFormedness_test19", checkTypeWellFormedness_test19),
         ("checkTypeWellFormedness_test20", checkTypeWellFormedness_test20),
         ("checkTypeWellFormedness_test21", checkTypeWellFormedness_test21),
         ("checkTypeWellFormedness_test22", checkTypeWellFormedness_test22),
         ("checkTypeWellFormedness_test23", checkTypeWellFormedness_test23),
         ("checkTypeWellFormedness_test24", checkTypeWellFormedness_test24),
         ("checkTypeWellFormedness_test25", checkTypeWellFormedness_test25),
         ("checkTypeWellFormedness_test26", checkTypeWellFormedness_test26),
         ("checkTypeWellFormednessWithPrnc_test1", checkTypeWellFormednessWithPrnc_test1),
         ("checkTypeWellFormednessWithPrnc_test2", checkTypeWellFormednessWithPrnc_test2),
         ("checkTypeWellFormednessWithPrnc_test3", checkTypeWellFormednessWithPrnc_test3),
         ("checkTypeWellFormednessWithPrnc_test4", checkTypeWellFormednessWithPrnc_test4),
         ("checkTypeWellFormednessWithPrnc_test5", checkTypeWellFormednessWithPrnc_test5),
         ("checkTypeWellFormednessWithPrnc_test6", checkTypeWellFormednessWithPrnc_test6),
         ("checkTypeWellFormednessWithPrnc_test7", checkTypeWellFormednessWithPrnc_test7),
         ("checkTypeWellFormednessWithPrnc_test8", checkTypeWellFormednessWithPrnc_test8),
         ("checkTypeWellFormednessWithPrnc_test9", checkTypeWellFormednessWithPrnc_test9),
         ("checkTypeWellFormednessWithPrnc_test10", checkTypeWellFormednessWithPrnc_test10),
         ("checkTypeWellFormednessWithPrnc_test11", checkTypeWellFormednessWithPrnc_test11),
         ("checkTypeWellFormednessWithPrnc_test12", checkTypeWellFormednessWithPrnc_test12),
         ("checkTypeWellFormednessWithPrnc_test13", checkTypeWellFormednessWithPrnc_test13),
         ("checkTypeWellFormednessWithPrnc_test14", checkTypeWellFormednessWithPrnc_test14),
         ("checkTypeWellFormednessWithPrnc_test15", checkTypeWellFormednessWithPrnc_test15),
         ("checkTypeWellFormednessWithPrnc_test16", checkTypeWellFormednessWithPrnc_test16),
         ("checkTypeWellFormednessWithPrnc_test17", checkTypeWellFormednessWithPrnc_test17),
         ("checkTypeWellFormednessWithPrnc_test18", checkTypeWellFormednessWithPrnc_test18),
         ("checkTypeWellFormednessWithPrnc_test19", checkTypeWellFormednessWithPrnc_test19),
         ("checkTypeWellFormednessWithPrnc_test20", checkTypeWellFormednessWithPrnc_test20),
         ("checkTypeWellFormednessWithPrnc_test21", checkTypeWellFormednessWithPrnc_test21),
         ("checkTypeWellFormednessWithPrnc_test22", checkTypeWellFormednessWithPrnc_test22),
         ("checkTypeWellFormednessWithPrnc_test23", checkTypeWellFormednessWithPrnc_test23),
         ("checkTypeWellFormednessWithPrnc_test24", checkTypeWellFormednessWithPrnc_test24),
         ("checkTypeWellFormednessWithPrnc_test25", checkTypeWellFormednessWithPrnc_test25),
         ("checkTypeWellFormednessWithPrnc_test26", checkTypeWellFormednessWithPrnc_test26),
         ("checkExpr_EUnit_test1", checkExpr_EUnit_test1),
         ("checkExpr_EUnit_test2", checkExpr_EUnit_test2),
         ("checkExpr_EUnit_test3", checkExpr_EUnit_test3),
         ("checkExpr_EUnit_test4", checkExpr_EUnit_test4),
         ("checkExpr_EUnit_test5", checkExpr_EUnit_test5),
         ("checkExpr_EUnit_test6", checkExpr_EUnit_test6),
         ("checkExpr_EUnit_test7", checkExpr_EUnit_test7),
         ("checkExpr_EPair_test1", checkExpr_EPair_test1),
         ("checkExpr_EPair_test2", checkExpr_EPair_test2),
         ("checkExpr_EPair_test3", checkExpr_EPair_test3),
         ("checkExpr_EPair_test4", checkExpr_EPair_test4),
         ("checkExpr_EPair_test5", checkExpr_EPair_test5),
         ("checkExpr_EPair_test6", checkExpr_EPair_test6),
         ("checkExpr_EPair_test7", checkExpr_EPair_test7),
         ("checkExpr_EPair_test8", checkExpr_EPair_test8),
         ("inferExpr_EVar_test1", inferExpr_EVar_test1),
         ("inferExpr_EVar_test2", inferExpr_EVar_test2),
         ("inferExpr_EVar_test3", inferExpr_EVar_test3),
         ("inferExpr_EVar_test4", inferExpr_EVar_test4),
         ("inferExpr_EVar_test5", inferExpr_EVar_test5),
         ("inferExpr_EVar_test6", inferExpr_EVar_test6),
         ("inferExpr_EVar_test7", inferExpr_EVar_test7),
         ("inferExpr_EVar_test8", inferExpr_EVar_test8)]

runTest :: (TestName, Test) -> String
runTest (name, t) =
  name ++ " - " ++  if t() then
    "Passed\n"
  else
    "Failed!\n"

runTests :: [(TestName, Test)] -> String
runTests = foldl (flip $ flip (++) . runTest) ""

checkAll :: [(TestName, Test)] -> Bool
checkAll = foldl (flip $ (&&) . flip ($) () . snd) True

main :: IO ()
main = do
  putStrLn $ runTests tests
  if checkAll tests then
    putStrLn "All tests have passed :)"
  else
    putStrLn "One or more tests have failed! :("
  return ()
