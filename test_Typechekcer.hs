import AST
import Typechecker

type Test = () -> Bool
type TestName = String

context1 :: Context
context1 = [CVar "x" TUnit Principal, CTypeVar (U $ UTypeVar "y") KStar, CUTypeVarEq (UTypeVar "n") MZero, CETypeVar (ETypeVar "z") KStar $ MProduct MUnit MUnit,
            CUTypeVarEq (UTypeVar "k") MUnit, CVar "r" TUnit NotPrincipal, CTypeVar (E $ ETypeVar "a") KStar, CETypeVar (ETypeVar "b") KNat MZero]

context2 :: Context
context2 = [CTypeVar (E $ ETypeVar "a") KNat, CTypeVar (E $ ETypeVar "b") KStar, CTypeVar (E $ ETypeVar "c") KStar]

context3 :: Context
context3 = [CVar "x" TUnit Principal, CTypeVar (U $ UTypeVar "y") KStar, CUTypeVarEq (UTypeVar "n") MZero, CETypeVar (ETypeVar "z") KStar $ MProduct MUnit MUnit,
            CUTypeVarEq (UTypeVar "k") MUnit, CVar "r" TUnit NotPrincipal, CETypeVar (ETypeVar "a") KStar MUnit, CETypeVar (ETypeVar "b") KNat MZero]

context4 :: Context
context4 = [CVar "zz" TUnit NotPrincipal, CVar "x" TUnit NotPrincipal, CTypeVar (U $ UTypeVar "x") KStar, CUTypeVarEq (UTypeVar "x") MZero,
            CETypeVar (ETypeVar "x") KNat MZero, CUTypeVarEq (UTypeVar "x") MUnit, CVar "x" TUnit Principal, CTypeVar (E $ ETypeVar "x") KStar,
            CETypeVar (ETypeVar "x") KStar $ MProduct MUnit MUnit, CTypeVar (U $ UTypeVar "x") KNat, CTypeVar (E $ ETypeVar "x") KStar]

context5 :: Context
context5 = [CUTypeVarEq (UTypeVar "x") MZero, CETypeVar (ETypeVar "x") KNat MZero, CUTypeVarEq (UTypeVar "x") MUnit,
            CVar "x" TUnit Principal, CTypeVar (E $ ETypeVar "x") KStar, CETypeVar (ETypeVar "x") KStar $ MProduct MUnit MUnit,
            CTypeVar (U $ UTypeVar "x") KNat, CTypeVar (E $ ETypeVar "x") KStar, CTypeVar (U $ UTypeVar "x") KStar]

--varContextLookup :: Context -> Expr p -> Either (Error p) ContextEntry
varContextLookup_test1 :: Test
varContextLookup_test1 () =
  case varContextLookup context1 "x" "1 , 3" of
    Right (CVar "x" TUnit Principal) -> True
    _ -> False

varContextLookup_test2 :: Test
varContextLookup_test2 () =
  case varContextLookup []  "x"  "1 , 3"of
    Left (UndeclaredVariable _ "x") -> True
    _ -> False

varContextLookup_test3 :: Test
varContextLookup_test3 () =
  case varContextLookup context1 "y" "1 , 3" of
    Left (UndeclaredVariable _ "y") -> True
    _ -> False

varContextLookup_test4 :: Test
varContextLookup_test4 () =
  case varContextLookup context1  "z" "1 , 3" of
    Left (UndeclaredVariable _ "z") -> True
    _ -> False

varContextLookup_test5 :: Test
varContextLookup_test5 () =
  case varContextLookup context1 "k" "1 , 3" of
    Left (UndeclaredVariable _ "k") -> True
    _ -> False

varContextLookup_test6 :: Test
varContextLookup_test6 () =
  case varContextLookup context1 "Konrad" "1 , 3" of
    Left (UndeclaredVariable _ "Konrad")  -> True
    _ -> False

varContextLookup_test7 :: Test
varContextLookup_test7 () =
  case varContextLookup context4 "x" "1 , 3" of
    Right (CVar "x" TUnit NotPrincipal) -> True
    _ -> False

varContextLookup_test8 :: Test
varContextLookup_test8 () =
  case varContextLookup context5 "x" "1 , 3" of
    Right (CVar "x" TUnit Principal) -> True
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
    Just (CUTypeVarEq (UTypeVar "n") MZero) -> True
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
    Just (CUTypeVarEq (UTypeVar "x") MZero) -> True
    _ -> False

--solvedETypeVarContextLookup :: Context -> ETypeVar -> Maybe ContextEntry
solvedETypeVarContextLookup_test1 :: Test
solvedETypeVarContextLookup_test1 () =
  case solvedETypeVarContextLookup [] $ ETypeVar "x" of
    Nothing -> True
    _ -> False

solvedETypeVarContextLookup_test2 :: Test
solvedETypeVarContextLookup_test2 () =
  case solvedETypeVarContextLookup context1 $ ETypeVar "x" of
    Nothing -> True
    _ -> False

solvedETypeVarContextLookup_test3 :: Test
solvedETypeVarContextLookup_test3 () =
  case solvedETypeVarContextLookup context1 $ ETypeVar "z" of
    Just (CETypeVar (ETypeVar "z") KStar (MProduct MUnit MUnit)) -> True
    _ -> False

solvedETypeVarContextLookup_test4 :: Test
solvedETypeVarContextLookup_test4 () =
 case solvedETypeVarContextLookup context1 $ ETypeVar "b" of
   Just (CETypeVar (ETypeVar "b") KNat MZero) -> True
   _ -> False

solvedETypeVarContextLookup_test5 :: Test
solvedETypeVarContextLookup_test5 () =
 case solvedETypeVarContextLookup context1 $ ETypeVar "Konrad" of
   Nothing -> True
   _ -> False

solvedETypeVarContextLookup_test6 :: Test
solvedETypeVarContextLookup_test6 () =
  case solvedETypeVarContextLookup context4 $ ETypeVar "x" of
    Just (CETypeVar (ETypeVar "x") KNat MZero) -> True
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
   Just (CETypeVar (ETypeVar "b") KNat MZero) -> True
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
  case eTypeVarContextReplace [] (ETypeVar "x") MUnit "1, 3" of
    Left (UndeclaredETypeVar "1, 3" "x") -> True
    _ -> False

eTypeVarContextReplace_test2 :: Test
eTypeVarContextReplace_test2 () =
  case eTypeVarContextReplace context2 (ETypeVar "b") MUnit "1, 3" of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CETypeVar (ETypeVar "b") KStar MUnit, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

eTypeVarContextReplace_test3 :: Test
eTypeVarContextReplace_test3 () =
  case eTypeVarContextReplace context2 (ETypeVar "c") (MProduct MUnit MUnit) "1, 3" of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CTypeVar (E (ETypeVar "b")) KStar, CETypeVar (ETypeVar "c") KStar (MProduct MUnit MUnit)] -> True
    _ -> False

eTypeVarContextReplace_test4 :: Test
eTypeVarContextReplace_test4 () =
  case eTypeVarContextReplace context1 (ETypeVar "b") MZero "1, 3" of
    Right c -> c == context1
    _ -> False

eTypeVarContextReplace_test5 :: Test
eTypeVarContextReplace_test5 () =
  case eTypeVarContextReplace context1 (ETypeVar "a") MUnit "1, 3" of
    Right c -> c == context3
    _ -> False

eTypeVarContextReplace_test6 :: Test
eTypeVarContextReplace_test6 () =
  case eTypeVarContextReplace context1 (ETypeVar "z") MUnit "1, 3" of
    Left (ETypeVarMismatchError "1, 3" (MProduct MUnit MUnit) MUnit) -> True
    _ -> False

eTypeVarContextReplace_test7 :: Test
eTypeVarContextReplace_test7 () =
  case eTypeVarContextReplace context1 (ETypeVar "Konrad") MUnit "1, 3" of
    Left (UndeclaredETypeVar "1, 3" "Konrad") -> True
    _ -> False

eTypeVarContextReplace_test8 :: Test
eTypeVarContextReplace_test8 () =
  case eTypeVarContextReplace context4 (ETypeVar "x") MUnit "1, 3" of
    Left (ETypeVarMismatchError "1, 3" MZero MUnit) -> True
    _ -> False

eTypeVarContextReplace_test9 :: Test
eTypeVarContextReplace_test9 () =
  case eTypeVarContextReplace [CTypeVar (E $ ETypeVar "a") KStar, CETypeVar (ETypeVar "a") KNat MZero] (ETypeVar "a") (MProduct MUnit MUnit) () of
    Right [CETypeVar (ETypeVar "a") KStar (MProduct MUnit MUnit), CETypeVar (ETypeVar "a") KNat MZero] -> True
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
  case applyContextToMonotype [] (MArrow (MProduct MUnit MUnit) (MCoproduct (MUVar $ UTypeVar "x") (MEVar $ ETypeVar "y"))) of
    (MArrow (MProduct MUnit MUnit) (MCoproduct (MUVar (UTypeVar "x")) (MEVar (ETypeVar "y")))) -> True
    _ -> False

applyContextToMonotype_test2 :: Test
applyContextToMonotype_test2 () =
  case applyContextToMonotype context5 (MArrow (MProduct MUnit MUnit) (MCoproduct (MUVar $ UTypeVar "x") (MEVar $ ETypeVar "x"))) of
    (MArrow (MProduct MUnit MUnit) (MCoproduct MZero MZero)) -> True
    _ -> False

applyContextToMonotype_test3 :: Test
applyContextToMonotype_test3 () =
  case applyContextToMonotype context5 (MArrow (MProduct MUnit MUnit) (MCoproduct (MUVar $ UTypeVar "y") (MEVar $ ETypeVar "x"))) of
    (MArrow (MProduct MUnit MUnit) (MCoproduct (MUVar (UTypeVar "y")) MZero)) -> True
    _ -> False

applyContextToMonotype_test4 :: Test
applyContextToMonotype_test4 () =
  case applyContextToMonotype context1 (MArrow (MProduct MUnit MUnit) (MCoproduct (MUVar $ UTypeVar "k") (MEVar $ ETypeVar "z"))) of
    (MArrow (MProduct MUnit MUnit) (MCoproduct MUnit (MProduct MUnit MUnit))) -> True
    _ -> False

--applyContextToProposition :: Context -> Proposition -> Proposition
applyContextToProposition_test1 :: Test
applyContextToProposition_test1 () =
  case applyContextToProposition context5 (MUnit, MUnit) of
    (MUnit, MUnit) -> True
    _ -> False

applyContextToProposition_test2 :: Test
applyContextToProposition_test2 () =
  case applyContextToProposition [] (MUVar (UTypeVar "x"), MEVar (ETypeVar "y")) of
    (MUVar (UTypeVar "x"), MEVar (ETypeVar "y")) -> True
    _ -> False

applyContextToProposition_test3 :: Test
applyContextToProposition_test3 () =
  case applyContextToProposition context5 (MUVar (UTypeVar "x"), MEVar (ETypeVar "x")) of
    (MZero, MZero) -> True
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
    Left (CheckKindHasWrongKindError "1, 3" KNat KStar) -> True
    _ -> False

inferMonotypeKind_test3 :: Test
inferMonotypeKind_test3 () =
  case inferMonotypeKind context1 (MCoproduct  (MUVar $ UTypeVar "y")  (MEVar $ ETypeVar "z")) "1, 3" of
    Right KStar -> True
    _ -> False

inferMonotypeKind_test4 :: Test
inferMonotypeKind_test4 () =
  case inferMonotypeKind context1 (MArrow  (MEVar $ ETypeVar "b")  (MEVar $ ETypeVar "z")) "1, 3" of
    Left (CheckKindHasWrongKindError "1, 3" KStar KNat) -> True
    _ -> False

inferMonotypeKind_test5 :: Test
inferMonotypeKind_test5 () =
  case inferMonotypeKind context1 (MUVar $ UTypeVar "n") "1, 3" of
    Left (CheckKindUVarNotDeclaredError "1, 3" "n") -> True
    _ -> False

inferMonotypeKind_test6 :: Test
inferMonotypeKind_test6 () =
  case inferMonotypeKind context1 (MEVar $ ETypeVar "Konrad") (1 :: Integer, 3 :: Integer) of
    Left (CheckKindEVarNotDeclaredError (1, 3) "Konrad") -> True
    _ -> False

inferMonotypeKind_test7 :: Test
inferMonotypeKind_test7 () =
  case inferMonotypeKind context2 (MArrow (MProduct MUnit MUnit) (MEVar $ ETypeVar "c")) "1, 3" of
    Right KStar -> True
    _ -> False

inferMonotypeKind_test8 :: Test
inferMonotypeKind_test8 () =
  case inferMonotypeKind context2 (MCoproduct (MProduct MUnit MUnit) (MSucc $ MSucc MZero)) ("1", "3") of
    Left (CheckKindHasWrongKindError ("1", "3") KStar KNat) -> True
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
    Left (CheckKindHasWrongKindError () KNat KStar) -> True
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
    Left (CheckKindUVarNotDeclaredError () "xx") -> True
    _ -> False

checkMonotypeHasKind_test7 :: Test
checkMonotypeHasKind_test7 () =
  case checkMonotypeHasKind context5 (MSucc $ MSucc (MEVar $ ETypeVar "")) () KNat of
    Left (CheckKindEVarNotDeclaredError () "") -> True
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
    Left (CheckKindHasWrongKindError 5 KNat KStar) -> True
    _ -> False

checkPropWellFormedness_test4 :: Test
checkPropWellFormedness_test4 () =
  case checkPropWellFormedness [] (MSucc $ MSucc MZero, MProduct MUnit $ MSucc MZero) (5 :: Integer) of
    Left (CheckKindHasWrongKindError 5 KStar KNat) -> True
    _ -> False

checkPropWellFormedness_test5 :: Test
checkPropWellFormedness_test5 () =
  case checkPropWellFormedness context1 (MSucc $ MSucc  (MEVar $ ETypeVar "b"), MProduct MUnit $ MSucc MZero) () of
    Left (CheckKindHasWrongKindError () KStar KNat) -> True
    _ -> False

checkPropWellFormedness_test6 :: Test
checkPropWellFormedness_test6 () =
  case checkPropWellFormedness context5 (MSucc $ MSucc  (MUVar $ UTypeVar "x"), MEVar $ ETypeVar "x") () of
    Right () -> True
    _ -> False

checkPropWellFormedness_test7 :: Test
checkPropWellFormedness_test7 () =
  case checkPropWellFormedness context5 (MSucc $ MSucc  (MUVar $ UTypeVar "r"), MEVar $ ETypeVar "x") () of
    Left (CheckKindUVarNotDeclaredError () "r") -> True
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
    Left (TypeFormednessInvalidKindError ((), ()) "b") -> True
    _ -> False

checkTypeWellFormedness_test4 :: Test
checkTypeWellFormedness_test4 () =
  case checkTypeWellFormedness [] (TCoproduct (TUVar $ UTypeVar "y") (TProduct (TEVar $ ETypeVar "z") (TEVar $ ETypeVar "b"))) ((),()) of
    Left (TypeFormednessUVarNotDeclaredError ((), ()) "y") -> True
    _ -> False

checkTypeWellFormedness_test5 :: Test
checkTypeWellFormedness_test5 () =
  case checkTypeWellFormedness [] (TProduct (TEVar $ ETypeVar "z") (TEVar $ ETypeVar "b")) ((),()) of
    Left (TypeFormednessEVarNotDeclaredError ((), ()) "z") -> True
    _ -> False

checkTypeWellFormedness_test6 :: Test
checkTypeWellFormedness_test6 () =
  case checkTypeWellFormedness context5 (TUVar $ UTypeVar "x")  (5 :: Integer) of
    Left (TypeFormednessInvalidKindError 5 "x") -> True
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
    Left (TypeFormednessUVarNotDeclaredError () "y") -> True
    _ -> False

checkTypeWellFormedness_test14 :: Test
checkTypeWellFormedness_test14 () =
  case checkTypeWellFormedness [] (TExistential "x" KStar (TArrow (TEVar $ ETypeVar "y") TUnit)) () of
    Left (TypeFormednessEVarNotDeclaredError () "y") -> True
    _ -> False

checkTypeWellFormedness_test15 :: Test
checkTypeWellFormedness_test15 () =
  case checkTypeWellFormedness context1 (TImp (MZero, MSucc MZero) (TArrow (TEVar $ ETypeVar "z") TUnit)) () of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test16 :: Test
checkTypeWellFormedness_test16 () =
  case checkTypeWellFormedness [] (TImp (MZero, MZero) (TArrow (TEVar $ ETypeVar "y") TUnit)) () of
    Left (TypeFormednessEVarNotDeclaredError () "y") -> True
    _ -> False

checkTypeWellFormedness_test17 :: Test
checkTypeWellFormedness_test17 () =
  case checkTypeWellFormedness [] (TExistential "x" KStar (TImp (MZero, MSucc MZero) (TArrow (TEVar $ ETypeVar "x") TUnit))) () of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test18 :: Test
checkTypeWellFormedness_test18 () =
  case checkTypeWellFormedness [] (TExistential "x" KStar (TImp (MZero, MSucc (MEVar $ ETypeVar "x")) (TArrow (TEVar $ ETypeVar "z") TUnit))) () of
    Left (CheckKindHasWrongKindError () KNat KStar) -> True
    _ -> False

checkTypeWellFormedness_test19 :: Test
checkTypeWellFormedness_test19 () =
  case checkTypeWellFormedness context1 (TAnd (TArrow (TEVar $ ETypeVar "z") TUnit) (MEVar $ ETypeVar "b", MSucc MZero)) () of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test20 :: Test
checkTypeWellFormedness_test20 () =
  case checkTypeWellFormedness context1 (TAnd (TArrow (TUVar $ UTypeVar "Haskell") TUnit) (MEVar $ ETypeVar "Konrad", MSucc MZero)) () of
    Left (TypeFormednessUVarNotDeclaredError () "Haskell") -> True
    _ -> False

checkTypeWellFormedness_test21 :: Test
checkTypeWellFormedness_test21 () =
  case checkTypeWellFormedness [] (TUniversal "x" KStar (TAnd (TArrow (TUVar $ UTypeVar "x") TUnit)  (MUVar $ UTypeVar "x", MUnit))) () of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test22 :: Test
checkTypeWellFormedness_test22 () =
  case checkTypeWellFormedness [] (TUniversal "x" KStar (TAnd (TArrow (TUVar $ UTypeVar "x") TUnit)  (MEVar $ ETypeVar "x", MUnit))) () of
    Left (CheckKindEVarNotDeclaredError () "x") -> True
    _ -> False

checkTypeWellFormedness_test23 :: Test
checkTypeWellFormedness_test23 () =
  case checkTypeWellFormedness context1 (TVec (MSucc $ MSucc (MEVar $ ETypeVar "b")) (TProduct TUnit TUnit)) () of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test24 :: Test
checkTypeWellFormedness_test24 () =
  case checkTypeWellFormedness [] (TUniversal "n" KNat $ TVec (MSucc $ MSucc (MUVar $ UTypeVar "n")) (TProduct TUnit (TUVar $ UTypeVar "n"))) () of
    Left (TypeFormednessInvalidKindError () "n") -> True
    _ -> False

checkTypeWellFormedness_test25 :: Test
checkTypeWellFormedness_test25 () =
  case checkTypeWellFormedness [] (TExistential "x" KStar $ TVec (MSucc $ MSucc (MEVar $ ETypeVar "x")) (TProduct TUnit TUnit)) () of
    Left (CheckKindHasWrongKindError () KNat KStar) -> True
    _ -> False

checkTypeWellFormedness_test26 :: Test
checkTypeWellFormedness_test26 () =
  case checkTypeWellFormedness context1 (TUniversal "n" KNat $ TVec (MSucc $ MSucc (MUVar $ UTypeVar "n")) (TImp (MEVar $ ETypeVar "b", MUVar $ UTypeVar "n") (TProduct TUnit TUnit))) () of
    Right () -> True
    _ -> False

tests :: [(TestName, Test)]
tests = [("varContextLookup_test1", varContextLookup_test1),
         ("varContextLookup_test2", varContextLookup_test2),
         ("varContextLookup_test3", varContextLookup_test3),
         ("varContextLookup_test4", varContextLookup_test4),
         ("varContextLookup_test5", varContextLookup_test5),
         ("varContextLookup_test6", varContextLookup_test6),
         ("varContextLookup_test7", varContextLookup_test7),
         ("varContextLookup_test8", varContextLookup_test8),
         ("uTypeVarEqContextLookup_test1", uTypeVarEqContextLookup_test1),
         ("uTypeVarEqContextLookup_test2", uTypeVarEqContextLookup_test2),
         ("uTypeVarEqContextLookup_test3", uTypeVarEqContextLookup_test3),
         ("uTypeVarEqContextLookup_test4", uTypeVarEqContextLookup_test4),
         ("uTypeVarEqContextLookup_test5", uTypeVarEqContextLookup_test5),
         ("uTypeVarEqContextLookup_test6", uTypeVarEqContextLookup_test6),
         ("solvedETypeVarContextLookup_test1", solvedETypeVarContextLookup_test1),
         ("solvedETypeVarContextLookup_test2", solvedETypeVarContextLookup_test2),
         ("solvedETypeVarContextLookup_test3", solvedETypeVarContextLookup_test3),
         ("solvedETypeVarContextLookup_test4", solvedETypeVarContextLookup_test4),
         ("solvedETypeVarContextLookup_test5", solvedETypeVarContextLookup_test5),
         ("solvedETypeVarContextLookup_test6", solvedETypeVarContextLookup_test6),
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
         ("checkTypeWellFormedness_test26", checkTypeWellFormedness_test26)]

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
