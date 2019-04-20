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
         ("checkMonotypeHasKind_test5", checkMonotypeHasKind_test5)]

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
