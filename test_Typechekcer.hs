import AST
import Typechecker

type Test = () -> Bool
type TestName = String

context1 :: Context
context1 = [CVar "x" TUnit Principal, CTypeVar (U $ UTypeVar "y") KStar, CUTypeVar (UTypeVar "n") MZero, CETypeVar (ETypeVar "z") KStar $ MProduct MUnit MUnit,
            CUTypeVar (UTypeVar "k") MUnit, CVar "r" TUnit NotPrincipal, CTypeVar (E $ ETypeVar "a") KStar, CETypeVar (ETypeVar "b") KNat MZero]

context2 :: Context
context2 = [CTypeVar (E $ ETypeVar "a") KNat, CTypeVar (E $ ETypeVar "b") KStar, CTypeVar (E $ ETypeVar "c") KStar]

context3 :: Context
context3 = [CVar "x" TUnit Principal, CTypeVar (U $ UTypeVar "y") KStar, CUTypeVar (UTypeVar "n") MZero, CETypeVar (ETypeVar "z") KStar $ MProduct MUnit MUnit,
            CUTypeVar (UTypeVar "k") MUnit, CVar "r" TUnit NotPrincipal, CETypeVar (ETypeVar "a") KStar MUnit, CETypeVar (ETypeVar "b") KNat MZero]

context4 :: Context
context4 = [CVar "zz" TUnit NotPrincipal, CVar "x" TUnit NotPrincipal, CTypeVar (U $ UTypeVar "x") KStar, CUTypeVar (UTypeVar "x") MZero,
            CETypeVar (ETypeVar "x") KNat MZero, CUTypeVar (UTypeVar "x") MUnit, CVar "x" TUnit Principal, CTypeVar (E $ ETypeVar "x") KStar,
            CETypeVar (ETypeVar "x") KStar $ MProduct MUnit MUnit, CTypeVar (U $ UTypeVar "x") KNat, CTypeVar (E $ ETypeVar "x") KStar]

context5 :: Context
context5 = [CUTypeVar (UTypeVar "x") MZero, CETypeVar (ETypeVar "x") KNat MZero, CUTypeVar (UTypeVar "x") MUnit,
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

--uTypeVarContextLookup :: Context -> UTypeVar -> Maybe ContextEntry
uTypeVarContextLookup_test1 :: Test
uTypeVarContextLookup_test1 () =
  case uTypeVarContextLookup [] $ UTypeVar "x" of
    Nothing -> True
    _ -> False

uTypeVarContextLookup_test2 :: Test
uTypeVarContextLookup_test2 () =
  case uTypeVarContextLookup context1 $ UTypeVar "x" of
    Nothing -> True
    _ -> False

uTypeVarContextLookup_test3 :: Test
uTypeVarContextLookup_test3 () =
  case uTypeVarContextLookup context1 $ UTypeVar "n" of
    Just (CUTypeVar (UTypeVar "n") MZero) -> True
    _ -> False

uTypeVarContextLookup_test4 :: Test
uTypeVarContextLookup_test4 () =
  case uTypeVarContextLookup context1 $ UTypeVar "k" of
    Just (CUTypeVar (UTypeVar "k") MUnit) -> True
    _ -> False

uTypeVarContextLookup_test5 :: Test
uTypeVarContextLookup_test5 () =
  case uTypeVarContextLookup context1 $ UTypeVar "Konrad" of
    Nothing -> True
    _ -> False

uTypeVarContextLookup_test6 :: Test
uTypeVarContextLookup_test6 () =
  case uTypeVarContextLookup context4 $ UTypeVar "x" of
    Just (CUTypeVar (UTypeVar "x") MZero) -> True
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
  case eTypeVarContextLookup context4 $ ETypeVar "x" of
    Just (CETypeVar (ETypeVar "x") KNat MZero) -> True
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

--typeVarContextLookup :: Context -> TypeVar -> Maybe ContextEntry
typeVarContextLookup_test1 :: Test
typeVarContextLookup_test1 () =
  case typeVarContextLookup [] $ U $ UTypeVar "x" of
    Nothing -> True
    _ -> False

typeVarContextLookup_test2 :: Test
typeVarContextLookup_test2 () =
  case typeVarContextLookup [] $ U $ UTypeVar "x" of
    Nothing -> True
    _ -> False

typeVarContextLookup_test3 :: Test
typeVarContextLookup_test3 () =
  case typeVarContextLookup context1 $ U $ UTypeVar "y" of
    Just (CTypeVar (U (UTypeVar "y")) KStar) -> True
    _ -> False

typeVarContextLookup_test4 :: Test
typeVarContextLookup_test4 () =
 case typeVarContextLookup context1 $ E $ ETypeVar "a" of
   Just (CTypeVar (E (ETypeVar "a")) KStar) -> True
   _ -> False

typeVarContextLookup_test5 :: Test
typeVarContextLookup_test5 () =
  case typeVarContextLookup context1 $ E $ ETypeVar "Konrad" of
    Nothing -> True
    _ -> False

typeVarContextLookup_test6 :: Test
typeVarContextLookup_test6 () =
  case typeVarContextLookup context4 $ E $ ETypeVar "x" of
    Just (CTypeVar (E (ETypeVar "x")) KStar) -> True
    _ -> False

typeVarContextLookup_test7 :: Test
typeVarContextLookup_test7 () =
  case typeVarContextLookup context5 $ U $ UTypeVar "x" of
    Just (CTypeVar (U (UTypeVar "x")) KNat) -> True
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
         ("uTypeVarContextLookup_test1", uTypeVarContextLookup_test1),
         ("uTypeVarContextLookup_test2", uTypeVarContextLookup_test2),
         ("uTypeVarContextLookup_test3", uTypeVarContextLookup_test3),
         ("uTypeVarContextLookup_test4", uTypeVarContextLookup_test4),
         ("uTypeVarContextLookup_test5", uTypeVarContextLookup_test5),
         ("uTypeVarContextLookup_test6", uTypeVarContextLookup_test6),
         ("eTypeVarContextLookup_test1", eTypeVarContextLookup_test1),
         ("eTypeVarContextLookup_test2", eTypeVarContextLookup_test2),
         ("eTypeVarContextLookup_test3", eTypeVarContextLookup_test3),
         ("eTypeVarContextLookup_test4", eTypeVarContextLookup_test4),
         ("eTypeVarContextLookup_test5", eTypeVarContextLookup_test5),
         ("eTypeVarContextLookup_test6", eTypeVarContextLookup_test6),
         ("eTypeVarContextReplace_test1", eTypeVarContextReplace_test1),
         ("eTypeVarContextReplace_test2", eTypeVarContextReplace_test2),
         ("eTypeVarContextReplace_test3", eTypeVarContextReplace_test3),
         ("eTypeVarContextReplace_test4", eTypeVarContextReplace_test4),
         ("eTypeVarContextReplace_test5", eTypeVarContextReplace_test5),
         ("eTypeVarContextReplace_test6", eTypeVarContextReplace_test6),
         ("eTypeVarContextReplace_test7", eTypeVarContextReplace_test7),
         ("eTypeVarContextReplace_test8", eTypeVarContextReplace_test8),
         ("typeVarContextLookup_test1", typeVarContextLookup_test1),
         ("typeVarContextLookup_test2", typeVarContextLookup_test2),
         ("typeVarContextLookup_test3", typeVarContextLookup_test3),
         ("typeVarContextLookup_test4", typeVarContextLookup_test4),
         ("typeVarContextLookup_test5", typeVarContextLookup_test5),
         ("typeVarContextLookup_test6", typeVarContextLookup_test6),
         ("typeVarContextLookup_test7", typeVarContextLookup_test7)]

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
