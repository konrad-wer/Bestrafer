import AST
import Typechecker
import TypecheckerUtils
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Monad.State
import Control.Monad.Trans.Maybe

type Test = Bool
type TestName = String

--TODO tests that not typecheck

startState :: TypecheckerState
startState = TypecheckerState {_freshVarNum = 0,
  _gadtArities = Map.fromList [("Terminator", 2), ("Lion", 1), ("List", 1), ("Vec", 2)],
  _constrContext = Map.fromList
  [("T800", Constructor "Terminator"
    [(UTypeVar "a", KNat)]
    [(MTInt, MTParam 1), (MTSucc (MTUVar (UTypeVar "a")), MTParam 0)]
    [TTInt, TTVec (MTUVar (UTypeVar "a")) (TTParam 1), TTBool]),
   ("T1000", Constructor "Terminator" [] [] [TTString, TTParam 0, TTParam 1]),
   ("TX", Constructor "Terminator" [] [] []),
   ("Simba", Constructor "Lion" [] [] [TTInt, TTBool]),
   ("Mufasa", Constructor "Lion" [] [(MTParam 0, MTInt)] [TTInt, TTBool]),
   ("LNil", Constructor "List" [] [] []),
   ("LCons", Constructor "List" [] [] [TTParam 0, TTGADT "List" [ParameterTypeT $ TTParam 0]]),
   ("Nil", Constructor "Vec" [] [(MTParam 0, MTZero)] []),
   ("Cons", Constructor "Vec" [(UTypeVar "a", KNat)] [(MTParam 0, MTSucc . MTUVar $ UTypeVar "a")]
    [TTParam 1, TTGADT "Vec" [ParameterMonotypeT . MTUVar $ UTypeVar "a", ParameterTypeT $ TTParam 1]])
  ]}

context1 :: Context
context1 = [CVar "x" TUnit Principal, CTypeVar (U $ UTypeVar "y") KStar, CUTypeVarEq (UTypeVar "n") (MSucc (MSucc (MSucc MZero))),
            CETypeVar (ETypeVar "z") KStar $ MProduct [MUnit, MUnit] 2, CMarker, CUTypeVarEq (UTypeVar "k") MUnit, CMarker,
            CVar "r" (TEVar $ ETypeVar "z") NotPrincipal, CTypeVar (E $ ETypeVar "a") KStar, CETypeVar (ETypeVar "b") KNat (MSucc MZero)]

context2 :: Context
context2 = [CTypeVar (E (ETypeVar "a")) KNat, CMarker, CTypeVar (E (ETypeVar "b")) KStar, CTypeVar (E (ETypeVar "c")) KStar]

context3 :: Context
context3 = [CVar "x" TUnit Principal, CTypeVar (U $ UTypeVar "y") KStar, CUTypeVarEq (UTypeVar "n") (MSucc (MSucc (MSucc MZero))),
            CETypeVar (ETypeVar "z") KStar $ MProduct [MUnit, MUnit] 2, CMarker, CUTypeVarEq (UTypeVar "k") MUnit, CMarker,
            CVar "r" (TEVar $ ETypeVar "z") NotPrincipal, CETypeVar (ETypeVar "a") KStar MUnit, CETypeVar (ETypeVar "b") KNat (MSucc MZero)]

context4 :: Context
context4 = [CVar "zz" (TEVar $ ETypeVar "r")  NotPrincipal, CVar "x" TUnit NotPrincipal, CTypeVar (U $ UTypeVar "x") KStar, CUTypeVarEq (UTypeVar "x") MZero,
            CETypeVar (ETypeVar "x") KNat MZero, CUTypeVarEq (UTypeVar "x") MUnit, CVar "x" TUnit Principal, CTypeVar (E $ ETypeVar "x") KStar,
            CETypeVar (ETypeVar "x") KStar $ MProduct [MUnit, MUnit] 2, CTypeVar (U $ UTypeVar "x") KNat, CTypeVar (E $ ETypeVar "x") KStar]

context5 :: Context
context5 = [CUTypeVarEq (UTypeVar "x") MZero, CETypeVar (ETypeVar "x") KNat (MSucc MZero), CUTypeVarEq (UTypeVar "x") MUnit,
            CVar "x" (TUVar $ UTypeVar "x") Principal, CTypeVar (E $ ETypeVar "x") KStar, CETypeVar (ETypeVar "x") KStar $ MProduct [MUnit, MUnit] 2,
            CTypeVar (U $ UTypeVar "x") KNat, CTypeVar (E $ ETypeVar "x") KStar, CTypeVar (U $ UTypeVar "x") KStar]


--typeFromTemplate :: [GADTParameter] -> p -> TypeTemplate -> Either (Error p) Type

typeFromTemplate_test1 :: Test
typeFromTemplate_test1 =
  case typeFromTemplate [ParameterType TUnit, ParameterMonotype $ MArrow MBool MInt] ()
                        (TTArrow (TTProduct [TTUnit, TTBool, TTInt, TTFloat, TTChar, TTString] 6)
                        (TTGADT "T" [ParameterTypeT (TTParam 0), ParameterTypeT (TTParam 1)])) of
    Right (TArrow (TProduct [TUnit, TBool, TInt, TFloat, TChar, TString] 6) (TGADT "T" [ParameterType TUnit, ParameterType (TArrow TBool TInt)])) -> True
    _ -> False

typeFromTemplate_test2 :: Test
typeFromTemplate_test2 =
  case typeFromTemplate [ParameterType TUnit, ParameterMonotype $ MSucc MZero] ()
                        (TTArrow (TTProduct [TTUnit, TTBool, TTInt, TTFloat, TTChar, TTString] 6)
                        (TTGADT "F" [ParameterTypeT (TTParam 0), ParameterTypeT (TTParam 1)])) of
    Left (MonotypeIsNotTypeError () (MSucc MZero)) -> True
    _ -> False

typeFromTemplate_test3 :: Test
typeFromTemplate_test3 =
  case typeFromTemplate [ParameterMonotype $ MSucc MZero] () (TTVec (MTParam 0) TTUnit) of
    Right (TVec (MSucc MZero) TUnit) -> True
    _ -> False

typeFromTemplate_test4 :: Test
typeFromTemplate_test4 =
  case typeFromTemplate [ParameterType $ TImp (MEVar (ETypeVar"A"), MZero) TUnit] () (TTVec (MTParam 0) TTUnit) of
    Left (TypeIsNotMonotypeError () (TImp (MEVar (ETypeVar"A"), MZero) TUnit)) -> True
    _ -> False

typeFromTemplate_test5 :: Test
typeFromTemplate_test5 =
  case typeFromTemplate [ParameterType TFloat] ()
       (TTUniversal (UTypeVar "x") KStar (TTImp (MTUVar (UTypeVar "x"), MTProduct [MTInt, MTGADT "T" [MTUnit, MTBool], MTFloat] 3) (TTParam 0))) of
    Right (TUniversal (UTypeVar "x") KStar (TImp (MUVar (UTypeVar "x"),  MProduct [MInt, MGADT "T" [MUnit, MBool], MFloat] 3) TFloat)) -> True
    _ -> False

typeFromTemplate_test6 :: Test
typeFromTemplate_test6 =
  case typeFromTemplate [ParameterMonotype (MSucc (MSucc (MSucc MZero)))] ()
       (TTExistential (UTypeVar "x") KNat (TTAnd (TTVec (MTParam 0) TTInt) (MTUVar (UTypeVar "x"), MTSucc MTZero))) of
    Right (TExistential (UTypeVar "x") KNat (TAnd (TVec (MSucc (MSucc (MSucc MZero))) TInt) (MUVar (UTypeVar "x"), MSucc MZero))) -> True
    _ -> False

--freeExistentialVariablesOfMonotype :: Monotype -> Set.Set ETypeVar
freeExistentialVariablesOfMonotype_test1 :: Test
freeExistentialVariablesOfMonotype_test1 =
  case Set.toList . freeExistentialVariablesOfMonotype $ MProduct [MArrow (MUVar $ UTypeVar "x") MUnit, MGADT "B" [MUnit, MUnit], MUnit] 3 of
    [] -> True
    _ -> False

freeExistentialVariablesOfMonotype_test2 :: Test
freeExistentialVariablesOfMonotype_test2 =
  case Set.toList . freeExistentialVariablesOfMonotype $ MProduct [MArrow (MUVar $ UTypeVar "x") (MEVar $ ETypeVar "a"),
                                                                   MGADT "B" [MEVar $ ETypeVar "b", MEVar $ ETypeVar "c"],
                                                                   MArrow (MUVar $ UTypeVar "x") (MEVar $ ETypeVar "a"),
                                                                   MGADT "B" [MEVar $ ETypeVar "b", MEVar $ ETypeVar "c"]] 4 of
    [ETypeVar "a", ETypeVar "b", ETypeVar "c"] -> True
    _ -> False

freeExistentialVariablesOfMonotype_test3 :: Test
freeExistentialVariablesOfMonotype_test3 =
  case Set.toList . freeExistentialVariablesOfMonotype $ MSucc (MSucc MZero) of
    [] -> True
    _ -> False

freeExistentialVariablesOfMonotype_test4 :: Test
freeExistentialVariablesOfMonotype_test4 =
  case Set.toList . freeExistentialVariablesOfMonotype $ MSucc (MSucc (MUVar $ UTypeVar "x")) of
    [] -> True
    _ -> False

freeExistentialVariablesOfMonotype_test5 :: Test
freeExistentialVariablesOfMonotype_test5 =
  case Set.toList . freeExistentialVariablesOfMonotype $ MSucc (MSucc (MEVar $ ETypeVar "x")) of
    [ETypeVar "x"] -> True
    _ -> False

--freeExistentialVariablesOfProp :: Proposition -> Set.Set ETypeVar
freeExistentialVariablesOfProp_test1 :: Test
freeExistentialVariablesOfProp_test1 =
  case Set.toList . freeExistentialVariablesOfProp $ (MSucc MZero, MArrow (MUVar $ UTypeVar "x") MUnit) of
    [] -> True
    _ -> False

freeExistentialVariablesOfProp_test2 :: Test
freeExistentialVariablesOfProp_test2 =
  case Set.toList . freeExistentialVariablesOfProp $ (MSucc (MEVar $ ETypeVar "x") , MArrow (MUVar $ UTypeVar "x") MUnit) of
    [ETypeVar "x"] -> True
    _ -> False

freeExistentialVariablesOfProp_test3 :: Test
freeExistentialVariablesOfProp_test3 =
  case Set.toList . freeExistentialVariablesOfProp $ (MSucc (MUVar $ UTypeVar "x") , MArrow (MEVar $ ETypeVar "a") (MEVar $ ETypeVar "b")) of
    [ETypeVar "a", ETypeVar "b"] -> True
    _ -> False

freeExistentialVariablesOfProp_test4 :: Test
freeExistentialVariablesOfProp_test4 =
  case Set.toList . freeExistentialVariablesOfProp $ (MSucc (MEVar $ ETypeVar "U") , MArrow (MEVar $ ETypeVar "W") (MEVar $ ETypeVar "r")) of
    [ETypeVar "U", ETypeVar "W",  ETypeVar "r"] -> True
    _ -> False

--freeExistentialVariables :: Type -> Set.Set ETypeVar
freeExistentialVariables_test1 :: Test
freeExistentialVariables_test1 =
  case Set.toList . freeExistentialVariables $ TProduct [TArrow (TUVar $ UTypeVar "x") TUnit, TGADT "F" [], TUnit, TUnit, TUnit] 5 of
    [] -> True
    _ -> False

freeExistentialVariables_test2 :: Test
freeExistentialVariables_test2 =
  case Set.toList . freeExistentialVariables $ TProduct [TArrow (TUVar $ UTypeVar "x") (TEVar $ ETypeVar "g"), TUnit,
                                                         TGADT "R" [ParameterType $ TEVar $ ETypeVar "h", ParameterType $ TEVar $ ETypeVar "c"],
                                                         TArrow (TUVar $ UTypeVar "x") (TEVar $ ETypeVar "g"),
                                                         TGADT "R" [ParameterType $ TEVar $ ETypeVar "h", ParameterType $ TEVar $ ETypeVar "c"], TUnit] 6  of
    [ETypeVar "c", ETypeVar "g", ETypeVar "h"] -> True
    _ -> False

freeExistentialVariables_test3 :: Test
freeExistentialVariables_test3 =
  case Set.toList . freeExistentialVariables $ TExistential (UTypeVar "x") KStar $
                    TProduct [TUnit, TArrow (TEVar $ ETypeVar "x") TUnit, TUnit, TGADT "T" [ParameterType TUnit], TUnit] 5 of
    [] -> True
    _ -> False

freeExistentialVariables_test4 :: Test
freeExistentialVariables_test4 =
  case Set.toList . freeExistentialVariables $ TUniversal (UTypeVar "x") KStar $ TProduct [TArrow (TEVar $ ETypeVar "x") TUnit, TGADT "F" []] 2 of
    [ETypeVar "x"] -> True
    _ -> False

freeExistentialVariables_test5 :: Test
freeExistentialVariables_test5 =
  case Set.toList . freeExistentialVariables $ TUniversal (UTypeVar "U") KNat $ TExistential (UTypeVar "x") KStar $
       TImp (MSucc (MEVar $ ETypeVar "U") , MArrow (MEVar $ ETypeVar "W") (MEVar $ ETypeVar "r"))
       (TProduct [TArrow (TEVar $ ETypeVar "x") TUnit, TGADT "p" [ParameterType $ TEVar $ ETypeVar "y", ParameterType TUnit]] 2) of
    [ETypeVar "U", ETypeVar "W", ETypeVar "r", ETypeVar "y"] -> True
    _ -> False

freeExistentialVariables_test6 :: Test
freeExistentialVariables_test6 =
  case Set.toList . freeExistentialVariables $ TUniversal (UTypeVar "U") KNat $ TExistential (UTypeVar "x") KStar $
       TAnd (TVec (MSucc (MEVar $ ETypeVar "a")) (TProduct [TArrow (TEVar $ ETypeVar "x") TUnit, TGADT "F" [ParameterType $ TEVar $ ETypeVar "y"]] 2))
       (MSucc (MEVar $ ETypeVar "U") , MArrow (MEVar $ ETypeVar "W") (MEVar $ ETypeVar "r")) of
    [ETypeVar "U", ETypeVar "W",  ETypeVar "a", ETypeVar "r", ETypeVar "y"] -> True
    _ -> False

freeExistentialVariables_test7 :: Test
freeExistentialVariables_test7 =
  case Set.toList . freeExistentialVariables $ TExistential (UTypeVar "h") KNat $  TExistential (UTypeVar "c") KStar $ TExistential (UTypeVar "g") KStar $
       TProduct [TArrow (TUVar $ UTypeVar "x") (TEVar $ ETypeVar "g"),
       TGADT "J" [ParameterType $ TEVar $ ETypeVar "h", ParameterType $ TEVar $ ETypeVar "c"]] 2 of
    [] -> True
    _ -> False

--freeVariablesOfMonotype :: Monotype -> Set.Set Var
freeVariablesOfMonotype_test1 :: Test
freeVariablesOfMonotype_test1 =
   case Set.toList . freeVariablesOfMonotype $ MArrow (MProduct [MUnit, MUnit] 2) (MGADT "J" [MUVar $ UTypeVar "x", MEVar $ ETypeVar "y"]) of
     ["x", "y"] -> True
     _ -> False

freeVariablesOfMonotype_test2 :: Test
freeVariablesOfMonotype_test2 =
  case Set.toList . freeVariablesOfMonotype $ MArrow (MProduct [MUnit, MUnit, MUnit, MUnit] 4) (MGADT "F" [MChar, MInt, MFloat, MBool]) of
    [] -> True
    _ -> False

freeVariablesOfMonotype_test3 :: Test
freeVariablesOfMonotype_test3 =
  case Set.toList . freeVariablesOfMonotype $ MSucc (MSucc MZero) of
    [] -> True
    _ -> False

freeVariablesOfMonotype_test4 :: Test
freeVariablesOfMonotype_test4 =
  case Set.toList . freeVariablesOfMonotype $ MSucc (MSucc $ MEVar $ ETypeVar "Konrad") of
    ["Konrad"] -> True
    _ -> False

freeVariablesOfMonotype_test5 :: Test
freeVariablesOfMonotype_test5 =
  case Set.toList . freeVariablesOfMonotype $ MSucc (MSucc $ MUVar $ UTypeVar "Jakub") of
    ["Jakub"] -> True
    _ -> False

--varContextLookup :: Context -> Expr p -> Either (Error p) ContextEntry
varContextLookup_test1 :: Test
varContextLookup_test1 =
  case varContextLookup context1 "x" "1 , 3" of
    Right (CVar "x" TUnit Principal) -> True
    _ -> False

varContextLookup_test2 :: Test
varContextLookup_test2 =
  case varContextLookup []  "x"  "1 , 3"of
    Left (UndeclaredVariableError _ "x") -> True
    _ -> False

varContextLookup_test3 :: Test
varContextLookup_test3 =
  case varContextLookup context1 "y" "1 , 3" of
    Left (UndeclaredVariableError _ "y") -> True
    _ -> False

varContextLookup_test4 :: Test
varContextLookup_test4 =
  case varContextLookup context1  "z" "1 , 3" of
    Left (UndeclaredVariableError _ "z") -> True
    _ -> False

varContextLookup_test5 :: Test
varContextLookup_test5 =
  case varContextLookup context1 "k" "1 , 3" of
    Left (UndeclaredVariableError _ "k") -> True
    _ -> False

varContextLookup_test6 :: Test
varContextLookup_test6 =
  case varContextLookup context1 "Konrad" "1 , 3" of
    Left (UndeclaredVariableError _ "Konrad")  -> True
    _ -> False

varContextLookup_test7 :: Test
varContextLookup_test7 =
  case varContextLookup context4 "x" "1 , 3" of
    Right (CVar "x" TUnit NotPrincipal) -> True
    _ -> False

varContextLookup_test8 :: Test
varContextLookup_test8 =
  case varContextLookup context5 "x" "1 , 3" of
    Right (CVar "x" (TUVar (UTypeVar "x")) Principal) -> True
    _ -> False

varContextLookup_test9 :: Test
varContextLookup_test9 =
  case varContextLookup context1 "r" "1 , 3" of
    Right (CVar "r" (TEVar (ETypeVar "z")) NotPrincipal) -> True
    _ -> False

--uTypeVarEqContextLookup :: Context -> UTypeVar -> Maybe ContextEntry
uTypeVarEqContextLookup_test1 :: Test
uTypeVarEqContextLookup_test1 =
  case uTypeVarEqContextLookup [] $ UTypeVar "x" of
    Nothing -> True
    _ -> False

uTypeVarEqContextLookup_test2 :: Test
uTypeVarEqContextLookup_test2 =
  case uTypeVarEqContextLookup context1 $ UTypeVar "x" of
    Nothing -> True
    _ -> False

uTypeVarEqContextLookup_test3 :: Test
uTypeVarEqContextLookup_test3 =
  case uTypeVarEqContextLookup context1 $ UTypeVar "n" of
    Just (CUTypeVarEq (UTypeVar "n") (MSucc (MSucc (MSucc MZero)))) -> True
    _ -> False

uTypeVarEqContextLookup_test4 :: Test
uTypeVarEqContextLookup_test4 =
  case uTypeVarEqContextLookup context1 $ UTypeVar "k" of
    Just (CUTypeVarEq (UTypeVar "k") MUnit) -> True
    _ -> False

uTypeVarEqContextLookup_test5 :: Test
uTypeVarEqContextLookup_test5 =
  case uTypeVarEqContextLookup context1 $ UTypeVar "Konrad" of
    Nothing -> True
    _ -> False

uTypeVarEqContextLookup_test6 :: Test
uTypeVarEqContextLookup_test6 =
  case uTypeVarEqContextLookup context4 $ UTypeVar "x" of
    Nothing -> True
    _ -> False

uTypeVarEqContextLookup_test7 :: Test
uTypeVarEqContextLookup_test7 =
  case uTypeVarEqContextLookup context5 $ UTypeVar "x" of
    Just (CUTypeVarEq (UTypeVar "x") MZero) -> True
    _ -> False

--typeVarContextLookup :: Context -> Var -> Maybe ContextEntry
typeVarContextLookup_test1 :: Test
typeVarContextLookup_test1 =
  case typeVarContextLookup [] "x" of
    Nothing -> True
    _ -> False

typeVarContextLookup_test2 :: Test
typeVarContextLookup_test2 =
  case typeVarContextLookup context1 "x" of
    Nothing -> True
    _ -> False

typeVarContextLookup_test3 :: Test
typeVarContextLookup_test3 =
  case typeVarContextLookup context1 "z" of
    Just (CETypeVar (ETypeVar "z") KStar (MProduct [MUnit, MUnit] 2)) -> True
    _ -> False

typeVarContextLookup_test4 :: Test
typeVarContextLookup_test4 =
 case typeVarContextLookup context1 "b" of
   Just (CETypeVar (ETypeVar "b") KNat (MSucc MZero)) -> True
   _ -> False

typeVarContextLookup_test5 :: Test
typeVarContextLookup_test5 =
 case typeVarContextLookup context1 "Konrad" of
   Nothing -> True
   _ -> False

typeVarContextLookup_test6 :: Test
typeVarContextLookup_test6 =
  case typeVarContextLookup context1 "a" of
    Just (CTypeVar (E (ETypeVar "a")) KStar) -> True
    _ -> False

typeVarContextLookup_test7 :: Test
typeVarContextLookup_test7 =
 case typeVarContextLookup context4 "x" of
   Just (CTypeVar (U (UTypeVar "x")) KStar) -> True
   _ -> False

typeVarContextLookup_test8 :: Test
typeVarContextLookup_test8 =
 case typeVarContextLookup [CTypeVar (E $ ETypeVar "a") KStar, CETypeVar (ETypeVar "a") KNat MZero] "a" of
   Just (CTypeVar (E (ETypeVar "a")) KStar) -> True
   _ -> False

typeVarContextLookup_test9 :: Test
typeVarContextLookup_test9 =
  case typeVarContextLookup [] "x" of
    Nothing -> True
    _ -> False

typeVarContextLookup_test10 :: Test
typeVarContextLookup_test10 =
  case typeVarContextLookup context1 "y" of
    Just (CTypeVar (U (UTypeVar "y")) KStar) -> True
    _ -> False

typeVarContextLookup_test11 :: Test
typeVarContextLookup_test11 =
  case typeVarContextLookup context1 "a" of
    Just (CTypeVar (E (ETypeVar "a")) KStar) -> True
    _ -> False

typeVarContextLookup_test12 :: Test
typeVarContextLookup_test12 =
  case typeVarContextLookup context1  "Konrad" of
    Nothing -> True
    _ -> False

typeVarContextLookup_test13 :: Test
typeVarContextLookup_test13 =
  case typeVarContextLookup context5 "x" of
    Just (CETypeVar (ETypeVar "x") KNat (MSucc MZero)) -> True
    _ -> False

--eTypeVarContextReplace :: Context -> ETypeVar -> Monotype -> p -> Either (Error p) Context
eTypeVarContextReplace_test1 :: Test
eTypeVarContextReplace_test1 =
  case eTypeVarContextReplace [] (ETypeVar "x") KStar MUnit [] "1, 3" of
    Left (UndeclaredETypeVarError "1, 3" (ETypeVar "x")) -> True
    _ -> False

eTypeVarContextReplace_test2 :: Test
eTypeVarContextReplace_test2 =
  case eTypeVarContextReplace context2 (ETypeVar "b") KStar MUnit [] "1, 3" of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CMarker, CETypeVar (ETypeVar "b") KStar MUnit, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

eTypeVarContextReplace_test3 :: Test
eTypeVarContextReplace_test3 =
  case eTypeVarContextReplace context2 (ETypeVar "c") KStar (MProduct [MUnit, MUnit, MUnit] 3) [] "1, 3" of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CMarker, CTypeVar (E (ETypeVar "b")) KStar,
           CETypeVar (ETypeVar "c") KStar (MProduct [MUnit, MUnit, MUnit] 3)] -> True
    _ -> False

eTypeVarContextReplace_test4 :: Test
eTypeVarContextReplace_test4 =
  case eTypeVarContextReplace context1 (ETypeVar "b") KNat (MSucc MZero) [] "1, 3" of
    Right c -> c == context1
    _ -> False

eTypeVarContextReplace_test5 :: Test
eTypeVarContextReplace_test5 =
  case eTypeVarContextReplace context1 (ETypeVar "a") KStar MUnit [] "1, 3" of
    Right c -> c == context3
    _ -> False

eTypeVarContextReplace_test6 :: Test
eTypeVarContextReplace_test6 =
  case eTypeVarContextReplace context1 (ETypeVar "z") KStar MUnit [] "1, 3" of
    Left (ETypeVarTypeMismatchError "1, 3" (ETypeVar "z") (MProduct [MUnit, MUnit] 2) MUnit) -> True
    _ -> False

eTypeVarContextReplace_test7 :: Test
eTypeVarContextReplace_test7 =
  case eTypeVarContextReplace context1 (ETypeVar "Konrad") KNat MUnit [] "1, 3" of
    Left (UndeclaredETypeVarError "1, 3" (ETypeVar "Konrad")) -> True
    _ -> False

eTypeVarContextReplace_test8 :: Test -- TO  ma jebnąć
eTypeVarContextReplace_test8 =
  case eTypeVarContextReplace context4 (ETypeVar "x") KStar MUnit [] "1, 3" of
    Left (UndeclaredETypeVarError "1, 3" (ETypeVar "x"))  -> True
    _ -> False

eTypeVarContextReplace_test9 :: Test
eTypeVarContextReplace_test9 =
  case eTypeVarContextReplace [CTypeVar (E $ ETypeVar "a") KStar, CETypeVar (ETypeVar "a") KNat MZero]
       (ETypeVar "a") KStar (MProduct [MUnit, MUnit] 2) [] () of
    Right [CETypeVar (ETypeVar "a") KStar (MProduct [MUnit, MUnit] 2), CETypeVar (ETypeVar "a") KNat MZero] -> True
    _ -> False

eTypeVarContextReplace_test10 :: Test
eTypeVarContextReplace_test10 =
  case eTypeVarContextReplace [CTypeVar (E $ ETypeVar "a") KStar, CETypeVar (ETypeVar "a") KNat MZero]
       (ETypeVar "a") KStar (MProduct [MUnit, MUnit] 2) [CTypeVar (E (ETypeVar "b")) KStar] () of
    Right [CETypeVar (ETypeVar "a") KStar (MProduct [MUnit, MUnit] 2), CTypeVar (E (ETypeVar "b")) KStar, CETypeVar (ETypeVar "a") KNat MZero] -> True
    _ -> False

eTypeVarContextReplace_test11 :: Test
eTypeVarContextReplace_test11 =
  case eTypeVarContextReplace context2 (ETypeVar "b") KStar (MProduct [MUnit, MUnit] 2)
        [CTypeVar (E (ETypeVar "t")) KStar, CUTypeVarEq (UTypeVar "r") MZero, CETypeVar (ETypeVar "c") KStar MUnit] () of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CMarker, CETypeVar (ETypeVar "b") KStar (MProduct [MUnit, MUnit] 2), CTypeVar (E (ETypeVar "t")) KStar,
           CUTypeVarEq (UTypeVar "r") MZero, CETypeVar (ETypeVar "c") KStar MUnit, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

eTypeVarContextReplace_test12 :: Test
eTypeVarContextReplace_test12 =
  case eTypeVarContextReplace context2 (ETypeVar "b") KNat MUnit [] "1, 3" of
    Left (ETypeVarKindMismatchError "1, 3" (ETypeVar "b") KStar KNat) -> True
    _ -> False

eTypeVarContextReplace_test13 :: Test
eTypeVarContextReplace_test13 =
  case eTypeVarContextReplace context2 (ETypeVar "a") KStar (MProduct [MUnit, MUnit] 2) [] "1, 3" of
    Left (ETypeVarKindMismatchError "1, 3" (ETypeVar "a") KNat KStar) -> True
    _ -> False

eTypeVarContextReplace_test14 :: Test
eTypeVarContextReplace_test14 =
  case eTypeVarContextReplace context1 (ETypeVar "b") KStar MZero [] "1, 3" of
    Left (ETypeVarKindMismatchError "1, 3" (ETypeVar "b") KNat KStar) -> True
    _ -> False

eTypeVarContextReplace_test15 :: Test
eTypeVarContextReplace_test15 =
  case eTypeVarContextReplace context1 (ETypeVar "z") KNat (MSucc MZero) [] "1, 3" of
    Left (ETypeVarKindMismatchError "1, 3" (ETypeVar "z") KStar KNat) -> True
    _ -> False

--dropContextToMarker :: Context -> Context
dropContextToMarker_test1 :: Test
dropContextToMarker_test1 =
  case dropContextToMarker context5 of
    [] -> True
    _ -> False

dropContextToMarker_test2 :: Test
dropContextToMarker_test2 =
  case dropContextToMarker context2 of
    [CTypeVar (E (ETypeVar "b")) KStar, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

dropContextToMarker_test3 :: Test
dropContextToMarker_test3 =
  case dropContextToMarker context1 of
    [CUTypeVarEq (UTypeVar "k") MUnit, CMarker, CVar "r" (TEVar (ETypeVar "z")) NotPrincipal,
     CTypeVar (E (ETypeVar "a")) KStar, CETypeVar (ETypeVar "b") KNat (MSucc MZero)] -> True
    _ -> False

dropContextToMarker_test4 :: Test
dropContextToMarker_test4 =
  case dropContextToMarker . dropContextToMarker $ context1 of
    [CVar "r" (TEVar (ETypeVar "z")) NotPrincipal, CTypeVar (E (ETypeVar "a")) KStar, CETypeVar (ETypeVar "b") KNat (MSucc MZero)] -> True
    _ -> False

dropContextToMarker_test5 :: Test
dropContextToMarker_test5 =
  case dropContextToMarker . dropContextToMarker . dropContextToMarker $ context1 of
    [] -> True
    _ -> False

--dropContextToETypeVar :: ETypeVar -> Context -> p -> Either (Error p) Context
dropContextToETypeVar_test1 :: Test
dropContextToETypeVar_test1 =
  case dropContextToETypeVar (ETypeVar "b") context1 () of
    Right [] -> True
    _ -> False

dropContextToETypeVar_test2 :: Test
dropContextToETypeVar_test2 =
  case dropContextToETypeVar (ETypeVar "Konrad") context1 () of
    Left (UndeclaredETypeVarError () (ETypeVar "Konrad")) -> True
    _ -> False

dropContextToETypeVar_test3 :: Test
dropContextToETypeVar_test3 =
  case dropContextToETypeVar (ETypeVar "b") context2 () of
    Right [CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

dropContextToETypeVar_test4 :: Test
dropContextToETypeVar_test4 =
  case dropContextToETypeVar (ETypeVar "a") context2 () of
    Right [CMarker, CTypeVar (E (ETypeVar "b")) KStar, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

dropContextToETypeVar_test5 :: Test
dropContextToETypeVar_test5 =
  case dropContextToETypeVar (ETypeVar "x") context5 () of
    Right [CUTypeVarEq (UTypeVar "x") MUnit, CVar "x" (TUVar (UTypeVar "x")) Principal,
           CTypeVar (E (ETypeVar "x")) KStar, CETypeVar (ETypeVar "x") KStar (MProduct [MUnit, MUnit] 2),
           CTypeVar (U (UTypeVar "x")) KNat, CTypeVar (E (ETypeVar "x")) KStar, CTypeVar (U (UTypeVar "x")) KStar] -> True
    _ -> False

dropContextToETypeVar_test6 :: Test
dropContextToETypeVar_test6 =
  case dropContextToETypeVar (ETypeVar "x") context4 () of
    Left (UndeclaredETypeVarError () (ETypeVar "x")) -> True
    _ -> False

--takeContextToETypeVar :: ETypeVar -> Context -> p -> Either (Error p) Context
takeContextToETypeVar_test1 :: Test
takeContextToETypeVar_test1 =
  case takeContextToETypeVar (ETypeVar "x") context4 () of
    Left (UndeclaredETypeVarError () (ETypeVar "x")) -> True
    _ -> False

takeContextToETypeVar_test2 :: Test
takeContextToETypeVar_test2 =
  case takeContextToETypeVar (ETypeVar "y") context5 () of
    Left (UndeclaredETypeVarError () (ETypeVar "y")) -> True
    _ -> False

takeContextToETypeVar_test3 :: Test
takeContextToETypeVar_test3 =
  case takeContextToETypeVar (ETypeVar "a") context2 () of
    Right [] -> True
    _ -> False

takeContextToETypeVar_test4 :: Test
takeContextToETypeVar_test4 =
  case takeContextToETypeVar (ETypeVar "x") context5 () of
    Right [CUTypeVarEq (UTypeVar "x") MZero] -> True
    _ -> False

takeContextToETypeVar_test5 :: Test
takeContextToETypeVar_test5 =
  case takeContextToETypeVar (ETypeVar "b") context1 () of
    Right [CVar "x" TUnit Principal, CTypeVar (U (UTypeVar "y")) KStar, CUTypeVarEq (UTypeVar "n") (MSucc (MSucc (MSucc MZero))),
           CETypeVar (ETypeVar "z") KStar (MProduct [MUnit, MUnit] 2), CMarker, CUTypeVarEq (UTypeVar "k") MUnit, CMarker,
           CVar "r" (TEVar (ETypeVar "z")) NotPrincipal, CTypeVar (E (ETypeVar "a")) KStar] -> True
    _ -> False

--takeContextToUTypeVar :: UTypeVar -> Context -> p -> Either (Error p) Context
takeContextToUTypeVar_test1 :: Test
takeContextToUTypeVar_test1 =
  case takeContextToUTypeVar (UTypeVar "y") context1 () of
    Right [CVar "x" TUnit Principal] -> True
    _ -> False

takeContextToUTypeVar_test2 :: Test
takeContextToUTypeVar_test2 =
  case takeContextToUTypeVar (UTypeVar "y") context2 () of
    Left (UndeclaredUTypeVarError () (UTypeVar "y")) -> True
    _ -> False

takeContextToUTypeVar_test3 :: Test
takeContextToUTypeVar_test3 =
  case takeContextToUTypeVar (UTypeVar "b") context2 () of
    Left (UndeclaredUTypeVarError () (UTypeVar "b")) -> True
    _ -> False

takeContextToUTypeVar_test4 :: Test
takeContextToUTypeVar_test4 =
  case takeContextToUTypeVar (UTypeVar "a") [CTypeVar (U (UTypeVar "a")) KStar] () of
    Right [] -> True
    _ -> False

takeContextToUTypeVar_test5 :: Test
takeContextToUTypeVar_test5 =
  case takeContextToUTypeVar (UTypeVar "x") context4 () of
    Right [CVar "zz" (TEVar (ETypeVar "r"))  NotPrincipal, CVar "x" TUnit NotPrincipal] -> True
    _ -> False

--substituteUVarInMonotype :: UTypeVar -> ETypeVar -> Monotype -> Monotype
substituteUVarInMonotype_test1 :: Test
substituteUVarInMonotype_test1 =
  case substituteUVarInMonotype (UTypeVar "x") (E $ ETypeVar "x") (MSucc (MSucc (MSucc MZero))) of
    MSucc (MSucc (MSucc MZero)) -> True
    _ -> False

substituteUVarInMonotype_test2 :: Test
substituteUVarInMonotype_test2 =
  case substituteUVarInMonotype (UTypeVar "x") (E $ ETypeVar "y") (MSucc (MSucc (MSucc (MUVar (UTypeVar "x"))))) of
    MSucc (MSucc (MSucc (MEVar (ETypeVar "y")))) -> True
    _ -> False

substituteUVarInMonotype_test3 :: Test
substituteUVarInMonotype_test3 =
  case substituteUVarInMonotype (UTypeVar "x") (E $ ETypeVar "y") (MSucc (MSucc (MSucc (MEVar (ETypeVar "x"))))) of
    MSucc (MSucc (MSucc (MEVar (ETypeVar "x")))) -> True
    _ -> False

substituteUVarInMonotype_test4 :: Test
substituteUVarInMonotype_test4 =
  case substituteUVarInMonotype (UTypeVar "x") (E $ ETypeVar "y")
                                (MArrow (MGADT "M" [MUnit, MProduct [MEVar (ETypeVar "x"), MUVar (UTypeVar "z")] 2]) MUnit) of
    MArrow (MGADT "M" [MUnit, MProduct [MEVar (ETypeVar "x"), MUVar (UTypeVar "z")] 2]) MUnit -> True
    _ -> False

substituteUVarInMonotype_test5 :: Test
substituteUVarInMonotype_test5 =
  case substituteUVarInMonotype (UTypeVar "x") (E $ ETypeVar "y") (MArrow (MGADT "A" [MUnit,
                                               MProduct [MEVar (ETypeVar "x"), MUVar (UTypeVar "x")] 2]) MUnit) of
    MArrow (MGADT "A" [MUnit, MProduct [MEVar (ETypeVar "x"), MEVar (ETypeVar "y")] 2]) MUnit -> True
    _ -> False

substituteUVarInMonotype_test6 :: Test
substituteUVarInMonotype_test6 =
  case substituteUVarInMonotype (UTypeVar "r") (E $ ETypeVar "y") (MArrow (MGADT "A" [MUnit,
                                MProduct [MUVar (UTypeVar "x"), MUVar (UTypeVar "z")] 2]) MUnit) of
    MArrow (MGADT "A" [MUnit, MProduct [MUVar (UTypeVar "x"), MUVar (UTypeVar "z")] 2]) MUnit -> True
    _ -> False

substituteUVarInMonotype_test7 :: Test
substituteUVarInMonotype_test7 =
  case substituteUVarInMonotype (UTypeVar "x") (U $ UTypeVar "x") (MSucc (MSucc (MSucc MZero))) of
    MSucc (MSucc (MSucc MZero)) -> True
    _ -> False

substituteUVarInMonotype_test8 :: Test
substituteUVarInMonotype_test8 =
  case substituteUVarInMonotype (UTypeVar "x") (U $ UTypeVar "y") (MSucc (MSucc (MSucc (MUVar (UTypeVar "x"))))) of
    MSucc (MSucc (MSucc (MUVar (UTypeVar "y")))) -> True
    _ -> False

substituteUVarInMonotype_test9 :: Test
substituteUVarInMonotype_test9 =
  case substituteUVarInMonotype (UTypeVar "x") (U $ UTypeVar "y") (MSucc (MSucc (MSucc (MEVar (ETypeVar "x"))))) of
    MSucc (MSucc (MSucc (MEVar (ETypeVar "x")))) -> True
    _ -> False

substituteUVarInMonotype_test10 :: Test
substituteUVarInMonotype_test10 =
  case substituteUVarInMonotype (UTypeVar "x") (U $ UTypeVar "y") (MArrow (MGADT "G" [MUnit,
                                MProduct [MEVar (ETypeVar "x"), MUVar (UTypeVar "z")] 2]) MUnit) of
    MArrow (MGADT "G" [MUnit, MProduct [MEVar (ETypeVar "x"), MUVar (UTypeVar "z")] 2]) MUnit -> True
    _ -> False

substituteUVarInMonotype_test11 :: Test
substituteUVarInMonotype_test11 =
  case substituteUVarInMonotype (UTypeVar "x") (U $ UTypeVar "y") (MArrow (MGADT "G" [MUnit,
                                MProduct [MEVar (ETypeVar "x"), MUVar (UTypeVar "x")] 2]) MUnit) of
    MArrow (MGADT "G" [MUnit, MProduct [MEVar (ETypeVar "x"), MUVar (UTypeVar "y")] 2]) MUnit -> True
    _ -> False

substituteUVarInMonotype_test12 :: Test
substituteUVarInMonotype_test12 =
  case substituteUVarInMonotype (UTypeVar "r") (U $ UTypeVar "y") (MArrow (MGADT "G" [MUnit,
                                MProduct [MUVar (UTypeVar "x"), MUVar (UTypeVar "z")] 2]) MUnit) of
    MArrow (MGADT "G" [MUnit, MProduct [MUVar (UTypeVar "x"), MUVar (UTypeVar "z")] 2]) MUnit -> True
    _ -> False

--substituteUVarInProp :: UTypeVar -> ETypeVar -> Proposition -> Proposition
substituteUVarInProp_test1 :: Test
substituteUVarInProp_test1 =
  case substituteUVarInProp (UTypeVar "x") (E $ ETypeVar "y") (MZero, MUnit) of
    (MZero, MUnit) -> True
    _ -> False

substituteUVarInProp_test2 :: Test
substituteUVarInProp_test2 =
  case substituteUVarInProp (UTypeVar "x") (E $ ETypeVar "y") (MZero, MUVar (UTypeVar "x")) of
    (MZero, MEVar (ETypeVar "y")) -> True
    _ -> False

substituteUVarInProp_test3 :: Test
substituteUVarInProp_test3 =
  case substituteUVarInProp (UTypeVar "x") (E $ ETypeVar "y") (MEVar (ETypeVar "z"), MUnit) of
    (MEVar (ETypeVar "z"), MUnit) -> True
    _ -> False

substituteUVarInProp_test4 :: Test
substituteUVarInProp_test4 =
  case substituteUVarInProp (UTypeVar "x") (E $ ETypeVar "y") (MUVar (UTypeVar "y"), MUVar (UTypeVar "x")) of
    (MUVar (UTypeVar "y"), MEVar (ETypeVar "y")) -> True
    _ -> False

substituteUVarInProp_test5 :: Test
substituteUVarInProp_test5 =
  case substituteUVarInProp (UTypeVar "x") (U $ UTypeVar "y") (MZero, MUnit) of
    (MZero, MUnit) -> True
    _ -> False

substituteUVarInProp_test6 :: Test
substituteUVarInProp_test6 =
  case substituteUVarInProp (UTypeVar "x") (U $ UTypeVar "y") (MZero, MUVar (UTypeVar "x")) of
    (MZero, MUVar (UTypeVar "y")) -> True
    _ -> False

substituteUVarInProp_test7 :: Test
substituteUVarInProp_test7 =
  case substituteUVarInProp (UTypeVar "x") (U $ UTypeVar "y") (MEVar (ETypeVar "z"), MUnit) of
    (MEVar (ETypeVar "z"), MUnit) -> True
    _ -> False

substituteUVarInProp_test8 :: Test
substituteUVarInProp_test8 =
  case substituteUVarInProp (UTypeVar "x") (U $ UTypeVar "y") (MUVar (UTypeVar "y"), MUVar (UTypeVar "x")) of
    (MUVar (UTypeVar "y"), MUVar (UTypeVar "y")) -> True
    _ -> False

--substituteUVarInType :: UTypeVar -> ETypeVar -> Type -> Type
substituteUVarInType_test1 :: Test
substituteUVarInType_test1 =
  case substituteUVarInType (UTypeVar "x") (E $ ETypeVar "y") (TArrow (TGADT "D" [ParameterType TUnit,
                            ParameterType $ TProduct [TEVar (ETypeVar "x"), TUVar (UTypeVar "z")] 2]) TUnit) of
    TArrow (TGADT "D" [ParameterType TUnit, ParameterType (TProduct [TEVar (ETypeVar "x"), TUVar (UTypeVar "z")] 2)]) TUnit -> True
    _ -> False

substituteUVarInType_test2 :: Test
substituteUVarInType_test2 =
  case substituteUVarInType (UTypeVar "x") (E $ ETypeVar "y") (TArrow (TGADT "D" [ParameterType TUnit,
                            ParameterType (TProduct [TEVar (ETypeVar "x"), TUVar (UTypeVar "x")] 2)]) TUnit) of
    TArrow (TGADT "D" [ParameterType TUnit, ParameterType (TProduct [TEVar (ETypeVar "x"), TEVar (ETypeVar "y")] 2)]) TUnit -> True
    _ -> False

substituteUVarInType_test3 :: Test
substituteUVarInType_test3 =
  case substituteUVarInType (UTypeVar "r") (E $ ETypeVar "y") (TArrow (TGADT "D" [ParameterType TUnit,
                            ParameterType (TProduct [TUVar (UTypeVar "x"), TUVar (UTypeVar "z")] 2)]) TUnit) of
    TArrow (TGADT "D" [ParameterType TUnit, ParameterType (TProduct [TUVar (UTypeVar "x"), TUVar (UTypeVar "z")] 2)]) TUnit -> True
    _ -> False

substituteUVarInType_test4 :: Test
substituteUVarInType_test4 =
  case substituteUVarInType (UTypeVar "r") (E $ ETypeVar "y") (TArrow (TUVar (UTypeVar "r")) (TExistential (UTypeVar "r") KStar (TUVar (UTypeVar "r")))) of
    TArrow (TEVar (ETypeVar "y")) (TExistential (UTypeVar "r") KStar (TUVar (UTypeVar "r"))) -> True
    _ -> False

substituteUVarInType_test5 :: Test
substituteUVarInType_test5 =
  case substituteUVarInType (UTypeVar "r") (E $ ETypeVar "y") (TArrow (TEVar (ETypeVar "r")) (TUniversal (UTypeVar "r") KStar (TUVar (UTypeVar "r")))) of
    TArrow (TEVar (ETypeVar "r")) (TUniversal (UTypeVar "r") KStar (TUVar (UTypeVar "r"))) -> True
    _ -> False

substituteUVarInType_test6 :: Test
substituteUVarInType_test6 =
  case substituteUVarInType (UTypeVar "r") (E $ ETypeVar "y") (TArrow (TUVar (UTypeVar "r")) (TExistential (UTypeVar "l") KStar (TUVar (UTypeVar "r")))) of
    TArrow (TEVar (ETypeVar "y")) (TExistential (UTypeVar "l") KStar (TEVar (ETypeVar "y"))) -> True
    _ -> False

substituteUVarInType_test7 :: Test
substituteUVarInType_test7 =
  case substituteUVarInType (UTypeVar "r") (E $ ETypeVar "y") (TArrow (TEVar (ETypeVar "r")) (TUniversal (UTypeVar "l") KStar (TUVar (UTypeVar "r")))) of
    TArrow (TEVar (ETypeVar "r")) (TUniversal (UTypeVar "l") KStar (TEVar (ETypeVar "y"))) -> True
    _ -> False

substituteUVarInType_test8 :: Test
substituteUVarInType_test8 =
  case substituteUVarInType (UTypeVar "r") (E $ ETypeVar "y") (TVec (MSucc (MUVar (UTypeVar "r"))) (TUniversal (UTypeVar "r") KStar (TUVar (UTypeVar "r")))) of
    TVec (MSucc (MEVar (ETypeVar "y"))) (TUniversal (UTypeVar "r") KStar (TUVar (UTypeVar "r"))) -> True
    _ -> False

substituteUVarInType_test9 :: Test
substituteUVarInType_test9 =
  case substituteUVarInType (UTypeVar "r") (E $ ETypeVar "y") (TVec (MSucc (MUVar (UTypeVar "r"))) (TUniversal (UTypeVar "l") KStar (TUVar (UTypeVar "r")))) of
    TVec (MSucc (MEVar (ETypeVar "y"))) (TUniversal (UTypeVar "l") KStar (TEVar (ETypeVar "y"))) -> True
    _ -> False

substituteUVarInType_test10 :: Test
substituteUVarInType_test10 =
  case substituteUVarInType (UTypeVar "r") (E $ ETypeVar "y") (TImp (MEVar (ETypeVar "r"), MUVar (UTypeVar "r")) (TUVar (UTypeVar "l"))) of
    TImp (MEVar (ETypeVar "r"), MEVar (ETypeVar "y")) (TUVar (UTypeVar "l")) -> True
    _ -> False

substituteUVarInType_test11 :: Test
substituteUVarInType_test11 =
  case substituteUVarInType (UTypeVar "r") (E $ ETypeVar "y") (TImp (MSucc MZero, MUVar (UTypeVar "r")) (TUVar (UTypeVar "r"))) of
    TImp (MSucc MZero, MEVar (ETypeVar "y")) (TEVar (ETypeVar "y")) -> True
    _ -> False

substituteUVarInType_test12 :: Test
substituteUVarInType_test12 =
  case substituteUVarInType (UTypeVar "r") (E $ ETypeVar "y") (TAnd (TUVar (UTypeVar "l")) (MEVar (ETypeVar "r"), MUVar (UTypeVar "r")) ) of
    TAnd (TUVar (UTypeVar "l")) (MEVar (ETypeVar "r"), MEVar (ETypeVar "y")) -> True
    _ -> False

substituteUVarInType_test13 :: Test
substituteUVarInType_test13 =
  case substituteUVarInType (UTypeVar "r") (E $ ETypeVar "y") (TAnd (TUVar (UTypeVar "r")) (MSucc MZero, MUVar (UTypeVar "r"))) of
    TAnd (TEVar (ETypeVar "y")) (MSucc MZero, MEVar (ETypeVar "y")) -> True
    _ -> False

substituteUVarInType_test14 :: Test
substituteUVarInType_test14 =
  case substituteUVarInType (UTypeVar "x") (U $ UTypeVar "y") (TArrow (TGADT "A" [ParameterType TUnit,
                            ParameterType (TProduct [TEVar (ETypeVar "x"), TUVar (UTypeVar "z")] 2)]) TUnit) of
    TArrow (TGADT "A" [ParameterType TUnit, ParameterType (TProduct [TEVar (ETypeVar "x"), TUVar (UTypeVar "z")] 2)]) TUnit -> True
    _ -> False

substituteUVarInType_test15 :: Test
substituteUVarInType_test15 =
  case substituteUVarInType (UTypeVar "x") (U $ UTypeVar "y") (TArrow (TGADT "A" [ParameterType TUnit,
                            ParameterType (TProduct [TEVar (ETypeVar "x"), TUVar (UTypeVar "x")] 2)]) TUnit) of
    TArrow (TGADT "A" [ParameterType TUnit, ParameterType (TProduct [TEVar (ETypeVar "x"), TUVar (UTypeVar "y")] 2)]) TUnit -> True
    _ -> False

substituteUVarInType_test16 :: Test
substituteUVarInType_test16 =
  case substituteUVarInType (UTypeVar "r") (U $ UTypeVar "y") (TArrow (TGADT "A" [ParameterType TUnit,
                             ParameterType (TProduct [TUVar (UTypeVar "x"), TUVar (UTypeVar "z")] 2)]) TUnit) of
    TArrow (TGADT "A" [ParameterType TUnit, ParameterType (TProduct [TUVar (UTypeVar "x"), TUVar (UTypeVar "z")] 2)]) TUnit -> True
    _ -> False

substituteUVarInType_test17 :: Test
substituteUVarInType_test17 =
  case substituteUVarInType (UTypeVar "r") (U $ UTypeVar "y") (TArrow (TUVar (UTypeVar "r")) (TExistential (UTypeVar "r") KStar (TUVar (UTypeVar "r")))) of
    TArrow (TUVar (UTypeVar "y")) (TExistential (UTypeVar "r") KStar (TUVar (UTypeVar "r"))) -> True
    _ -> False

substituteUVarInType_test18 :: Test
substituteUVarInType_test18 =
  case substituteUVarInType (UTypeVar "r") (U $ UTypeVar "y") (TArrow (TEVar (ETypeVar "r")) (TUniversal (UTypeVar "r") KStar (TUVar (UTypeVar "r")))) of
    TArrow (TEVar (ETypeVar "r")) (TUniversal (UTypeVar "r") KStar (TUVar (UTypeVar "r"))) -> True
    _ -> False

substituteUVarInType_test19 :: Test
substituteUVarInType_test19 =
  case substituteUVarInType (UTypeVar "r") (U $ UTypeVar "y") (TArrow (TUVar (UTypeVar "r")) (TExistential (UTypeVar "l") KStar (TUVar (UTypeVar "r")))) of
    TArrow (TUVar (UTypeVar "y")) (TExistential (UTypeVar "l") KStar (TUVar (UTypeVar "y"))) -> True
    _ -> False

substituteUVarInType_test20 :: Test
substituteUVarInType_test20 =
  case substituteUVarInType (UTypeVar "r") (U $ UTypeVar "y") (TArrow (TEVar (ETypeVar "r")) (TUniversal (UTypeVar "l") KStar (TUVar (UTypeVar "r")))) of
    TArrow (TEVar (ETypeVar "r")) (TUniversal (UTypeVar "l") KStar (TUVar (UTypeVar "y"))) -> True
    _ -> False

substituteUVarInType_test21 :: Test
substituteUVarInType_test21 =
  case substituteUVarInType (UTypeVar "r") (U $ UTypeVar "y") (TVec (MSucc (MUVar (UTypeVar "r"))) (TUniversal (UTypeVar "r") KStar (TUVar (UTypeVar "r")))) of
    TVec (MSucc (MUVar (UTypeVar "y"))) (TUniversal (UTypeVar "r") KStar (TUVar (UTypeVar "r"))) -> True
    _ -> False

substituteUVarInType_test22 :: Test
substituteUVarInType_test22 =
  case substituteUVarInType (UTypeVar "r") (U $ UTypeVar "y") (TVec (MSucc (MUVar (UTypeVar "r"))) (TUniversal (UTypeVar "l") KStar (TUVar (UTypeVar "r")))) of
    TVec (MSucc (MUVar (UTypeVar "y"))) (TUniversal (UTypeVar "l") KStar (TUVar (UTypeVar "y"))) -> True
    _ -> False

substituteUVarInType_test23 :: Test
substituteUVarInType_test23 =
  case substituteUVarInType (UTypeVar "r") (U $ UTypeVar "y") (TImp (MEVar (ETypeVar "r"), MUVar (UTypeVar "r")) (TUVar (UTypeVar "l"))) of
    TImp (MEVar (ETypeVar "r"), MUVar (UTypeVar "y")) (TUVar (UTypeVar "l")) -> True
    _ -> False

substituteUVarInType_test24 :: Test
substituteUVarInType_test24 =
  case substituteUVarInType (UTypeVar "r") (U $ UTypeVar "y") (TImp (MSucc MZero, MUVar (UTypeVar "r")) (TUVar (UTypeVar "r"))) of
    TImp (MSucc MZero, MUVar (UTypeVar "y")) (TUVar (UTypeVar "y")) -> True
    _ -> False

substituteUVarInType_test25 :: Test
substituteUVarInType_test25 =
  case substituteUVarInType (UTypeVar "r") (U $ UTypeVar "y") (TAnd (TUVar (UTypeVar "l")) (MEVar (ETypeVar "r"), MUVar (UTypeVar "r")) ) of
    TAnd (TUVar (UTypeVar "l")) (MEVar (ETypeVar "r"), MUVar (UTypeVar "y")) -> True
    _ -> False

substituteUVarInType_test26 :: Test
substituteUVarInType_test26 =
  case substituteUVarInType (UTypeVar "r") (U $ UTypeVar "y") (TAnd (TUVar (UTypeVar "r")) (MSucc MZero, MUVar (UTypeVar "r"))) of
    TAnd (TUVar (UTypeVar "y")) (MSucc MZero, MUVar (UTypeVar "y")) -> True
    _ -> False

--monotypeToType :: Monotype -> p -> Either (Error p) Type
monotypeToType_test1 :: Test
monotypeToType_test1 =
  case monotypeToType () (MArrow (MProduct [MUnit, MUnit] 2) (MGADT "K" [MUVar $ UTypeVar "x", MEVar $ ETypeVar "y"])) of
    Right (TArrow (TProduct [TUnit, TUnit] 2)
          (TGADT "K" [ParameterMonotype (MUVar (UTypeVar "x")), ParameterMonotype (MEVar (ETypeVar "y"))])) -> True
    _ -> False

monotypeToType_test2 :: Test
monotypeToType_test2 =
  case monotypeToType () (MSucc (MSucc (MSucc MZero))) of
    Left (MonotypeIsNotTypeError () (MSucc (MSucc (MSucc MZero)))) -> True
    _ -> False

monotypeToType_test3 :: Test
monotypeToType_test3 =
  case monotypeToType () (MArrow (MProduct [MUnit, MSucc MZero] 2) (MGADT "K" [MUVar $ UTypeVar "x", MEVar $ ETypeVar "y"])) of
    Left (MonotypeIsNotTypeError () (MSucc MZero)) -> True
    _ -> False

--typeToMonotype :: Type -> p -> Either (Error p) Monotype
typeToMonotype_test1 :: Test
typeToMonotype_test1 =
  case typeToMonotype () (TArrow (TProduct [TUnit, TUnit] 2)
                      (TGADT "K" [ParameterType (TUVar (UTypeVar "x")), ParameterType (TEVar (ETypeVar "y"))])) of
    Right (MArrow (MProduct [MUnit, MUnit] 2) (MGADT "K" [MUVar (UTypeVar "x"), MEVar (ETypeVar "y")])) -> True
    _ -> False

typeToMonotype_test2 :: Test
typeToMonotype_test2 =
  case typeToMonotype () (TProduct [TUniversal (UTypeVar "x") KStar TUnit, TUnit] 2) of
    Left (TypeIsNotMonotypeError () (TUniversal (UTypeVar "x") KStar TUnit)) -> True
    _ -> False

typeToMonotype_test3 :: Test
typeToMonotype_test3 =
  case typeToMonotype () (TGADT "Y" [ParameterType TUnit, ParameterType $ TExistential (UTypeVar "x") KStar (TVec MZero TUnit)]) of
    Left (TypeIsNotMonotypeError () (TExistential (UTypeVar "x") KStar (TVec MZero TUnit))) -> True
    _ -> False

typeToMonotype_test4 :: Test
typeToMonotype_test4 =
  case typeToMonotype () (TImp (MZero, MUnit) TUnit) of
    Left (TypeIsNotMonotypeError ()  (TImp (MZero, MUnit) TUnit)) -> True
    _ -> False

typeToMonotype_test5 :: Test
typeToMonotype_test5 =
  case typeToMonotype () (TAnd TUnit (MUnit, MUnit)) of
    Left (TypeIsNotMonotypeError () (TAnd TUnit (MUnit, MUnit))) -> True
    _ -> False

typeToMonotype_test6 :: Test
typeToMonotype_test6 =
  case typeToMonotype () (TVec (MSucc MZero) (TProduct [TUnit, TUnit] 2)) of
    Left (TypeIsNotMonotypeError () (TVec (MSucc MZero) (TProduct [TUnit, TUnit] 2))) -> True
    _ -> False

--applyContextToMonotype :: Context -> Monotype -> Monotype
applyContextToMonotype_test1 :: Test
applyContextToMonotype_test1 =
  case applyContextToMonotype () [] (MArrow (MProduct [MUnit, MUnit] 2) (MGADT "f" [MUVar $ UTypeVar "x", MEVar $ ETypeVar "y"])) of
    Left (UndeclaredETypeVarError () (ETypeVar "y")) -> True
    _ -> False

applyContextToMonotype_test2 :: Test
applyContextToMonotype_test2 =
  case applyContextToMonotype () context5 (MArrow (MProduct [MUnit, MUnit] 2) (MGADT "H" [MUVar $ UTypeVar "x", MEVar $ ETypeVar "x"])) of
    Right (MArrow (MProduct [MUnit, MUnit] 2) (MGADT "H" [MZero, MSucc MZero])) -> True
    _ -> False

applyContextToMonotype_test3 :: Test
applyContextToMonotype_test3 =
  case applyContextToMonotype () context5 (MArrow (MProduct [MUnit, MUnit] 2) (MGADT "H" [MUVar $ UTypeVar "y", MEVar $ ETypeVar "x"])) of
    Right (MArrow (MProduct [MUnit, MUnit] 2) (MGADT "H" [MUVar (UTypeVar "y"), MSucc MZero])) -> True
    _ -> False

applyContextToMonotype_test4 :: Test
applyContextToMonotype_test4 =
  case applyContextToMonotype () context1 (MArrow (MProduct [MUnit, MUnit] 2) (MGADT "H" [MUVar $ UTypeVar "k", MEVar $ ETypeVar "z"])) of
    Right (MArrow (MProduct [MUnit, MUnit] 2) (MGADT "H" [MUnit, MProduct [MUnit, MUnit] 2])) -> True
    _ -> False

--applyContextToProposition :: Context -> Proposition -> Proposition
applyContextToProposition_test1 :: Test
applyContextToProposition_test1 =
  case applyContextToProposition () context5 (MUnit, MUnit) of
    Right (MUnit, MUnit) -> True
    _ -> False

applyContextToProposition_test2 :: Test
applyContextToProposition_test2 =
  case applyContextToProposition () [] (MUVar (UTypeVar "x"), MEVar (ETypeVar "y")) of
    Left (UndeclaredETypeVarError () (ETypeVar "y")) -> True
    _ -> False

applyContextToProposition_test3 :: Test
applyContextToProposition_test3 =
  case applyContextToProposition () context5 (MUVar (UTypeVar "x"), MEVar (ETypeVar "x")) of
    Right (MZero, MSucc MZero) -> True
    _ -> False

--applyContextToType :: Context -> Type -> p-> Either (Error p) Type
applyContextToType_test1 :: Test
applyContextToType_test1 =
  case applyContextToType () [] (TArrow (TProduct [TUnit, TUnit] 2)
       (TGADT "y" [ParameterType $ TUVar $ UTypeVar "x", ParameterType $ TEVar $ ETypeVar "y"])) of
    Left (UndeclaredETypeVarError () (ETypeVar "y")) -> True
    _ -> False

applyContextToType_test2 :: Test
applyContextToType_test2 =
  case applyContextToType () context5 (TArrow (TProduct [TUnit, TUnit] 2)
       (TGADT "y" [ParameterType $ TUVar $ UTypeVar "x", ParameterType $ TEVar $ ETypeVar "x"])) of
    Left (MonotypeIsNotTypeError () MZero) -> True
    _ -> False

applyContextToType_test3 :: Test
applyContextToType_test3 =
  case applyContextToType () context5 (TArrow (TProduct [TUnit, TUnit] 2)
       (TGADT "y" [ParameterType $ TUVar $ UTypeVar "y", ParameterType $ TEVar $ ETypeVar "x"])) of
    Left (TypeHasWrongKindError () (TEVar (ETypeVar "x")) KStar KNat) -> True
    _ -> False

applyContextToType_test4 :: Test
applyContextToType_test4 =
  case applyContextToType () context1 (TArrow (TProduct [TUnit, TUnit] 2)
       (TGADT "R" [ParameterType $ TUVar $ UTypeVar "k", ParameterType $ TEVar $ ETypeVar "z"])) of
    Right (TArrow (TProduct [TUnit, TUnit] 2) (TGADT "R" [ParameterType TUnit, ParameterType (TProduct [TUnit, TUnit] 2)])) -> True
    _ -> False

applyContextToType_test5 :: Test
applyContextToType_test5 =
  case applyContextToType () context5 (TVec (MUVar $ UTypeVar "x") (TGADT "R" [ParameterType TUnit, ParameterType TUnit])) of
    Right (TVec MZero (TGADT "R" [ParameterType TUnit, ParameterType TUnit])) -> True
    _ -> False

applyContextToType_test6 :: Test
applyContextToType_test6 =
  case applyContextToType () context5 (TImp (MUVar $ UTypeVar "x", MZero) (TGADT "R" [ParameterType TUnit, ParameterType TUnit])) of
    Right (TImp (MZero, MZero) (TGADT "R" [ParameterType TUnit, ParameterType TUnit])) -> True
    _ -> False

applyContextToType_test7 :: Test
applyContextToType_test7 =
  case applyContextToType () [CUTypeVarEq (UTypeVar "x") (MSucc (MSucc MZero))] (TImp (MUVar $ UTypeVar "x", MZero)
       (TGADT "F" [ParameterMonotype $ MUVar $ UTypeVar "x", ParameterType TUnit])) of
    Right (TImp (MSucc (MSucc MZero), MZero) (TGADT "F" [ParameterMonotype (MSucc (MSucc MZero)), ParameterType TUnit])) -> True
    _ -> False

applyContextToType_test8 :: Test
applyContextToType_test8 =
  case applyContextToType () context1 (TAnd (TGADT "L" [ParameterType TUnit, ParameterType TUnit]) (MUVar $ UTypeVar "n", MEVar $ ETypeVar "b")) of
    Right (TAnd (TGADT "L" [ParameterType TUnit, ParameterType TUnit]) (MSucc (MSucc (MSucc MZero)), MSucc MZero)) -> True
    _ -> False

applyContextToType_test9 :: Test
applyContextToType_test9 =
  case applyContextToType () context1 (TAnd (TUVar $ UTypeVar "n") (MUVar $ UTypeVar "n", MEVar $ ETypeVar "b")) of
    Left (MonotypeIsNotTypeError () (MSucc (MSucc (MSucc MZero)))) -> True
    _ -> False

applyContextToType_test10 :: Test
applyContextToType_test10 =
  case applyContextToType () context5 (TUniversal (UTypeVar "x") KNat
                          (TVec (MUVar $ UTypeVar "x") (TGADT "Elton" [ParameterType TUnit, ParameterType TUnit]))) of
    Right (TUniversal (UTypeVar "x") KNat (TVec MZero (TGADT "Elton" [ParameterType TUnit, ParameterType TUnit]))) -> True
    _ -> False

applyContextToType_test11 :: Test
applyContextToType_test11 =
  case applyContextToType () context1 (TUniversal (UTypeVar "x") KStar
                          (TVec (MUVar $ UTypeVar "n") (TGADT "Elton" [ParameterType TUnit, ParameterType TUnit]))) of
    Right (TUniversal (UTypeVar "x") KStar (TVec (MSucc (MSucc (MSucc MZero))) (TGADT "Elton" [ParameterType TUnit, ParameterType TUnit]))) -> True
    _ -> False

applyContextToType_test12 :: Test
applyContextToType_test12 =
  case applyContextToType () context1 (TUniversal (UTypeVar "x") KStar
                          (TVec (MUVar $ UTypeVar "n") (TGADT "Elton" [ParameterType $ TUVar $ UTypeVar "x", ParameterType TUnit]))) of
    Right (TUniversal (UTypeVar "x") KStar (TVec (MSucc (MSucc (MSucc MZero)))
          (TGADT "Elton" [ParameterType (TUVar (UTypeVar "x")), ParameterType TUnit]))) -> True
    _ -> False

applyContextToType_test13 :: Test
applyContextToType_test13  =
  case applyContextToType () context1 (TExistential (UTypeVar "b") KNat
       (TImp (MUVar (UTypeVar "n"), MEVar (ETypeVar "b")) (TVec (MEVar (ETypeVar "b")) TUnit))) of
    Right (TExistential (UTypeVar "b") KNat (TImp (MSucc (MSucc (MSucc MZero)), MSucc MZero) (TVec (MSucc MZero) TUnit))) -> True
    _ -> False

applyContextToType_test14 :: Test
applyContextToType_test14  =
  case applyContextToType () context5 (TExistential (UTypeVar "x") KNat
       (TImp (MUVar (UTypeVar "x"), MUVar (UTypeVar "x")) (TVec (MUVar (UTypeVar "x")) TUnit))) of
    Right (TExistential (UTypeVar "x") KNat (TImp (MZero, MZero) (TVec MZero TUnit))) -> True
    _ -> False

applyContextToType_test15 :: Test
applyContextToType_test15  =
  case applyContextToType "1,3" context5 (TExistential (UTypeVar "y") KNat
       (TImp (MEVar (ETypeVar "x"), MEVar (ETypeVar "x")) (TVec MZero (TUVar (UTypeVar "x"))))) of
    Left (MonotypeIsNotTypeError "1,3" MZero) -> True
    _ -> False

--inferMonotypeKind :: Context -> Monotype -> p -> Either (Error p) Kind
inferMonotypeKind_test1 :: Test
inferMonotypeKind_test1 =
  case flip evalStateT startState $ inferMonotypeKind "1, 3" [] (MSucc $ MSucc MZero) of
    Right KNat -> True
    _ -> False

inferMonotypeKind_test2 :: Test
inferMonotypeKind_test2 =
  case flip evalStateT startState $ inferMonotypeKind "1, 3" [] (MSucc $ MSucc MUnit) of
    Left (MonotypeHasWrongKindError "1, 3" MUnit KNat KStar) -> True
    _ -> False

inferMonotypeKind_test3 :: Test
inferMonotypeKind_test3 =
  case flip evalStateT startState $ inferMonotypeKind "1, 3" context1 (MGADT "Terminator" [MUVar $ UTypeVar "y", MEVar $ ETypeVar "z"]) of
    Right KStar -> True
    _ -> False

inferMonotypeKind_test4 :: Test
inferMonotypeKind_test4 =
  case flip evalStateT startState $ inferMonotypeKind "1, 3" context1 (MArrow  (MEVar $ ETypeVar "b")  (MEVar $ ETypeVar "z")) of
    Left (MonotypeHasWrongKindError "1, 3" (MEVar (ETypeVar "b")) KStar KNat) -> True
    _ -> False

inferMonotypeKind_test5 :: Test
inferMonotypeKind_test5 =
  case flip evalStateT startState $ inferMonotypeKind "1, 3" context1 (MUVar $ UTypeVar "n") of
    Left (UndeclaredUTypeVarError "1, 3" (UTypeVar "n")) -> True
    _ -> False

inferMonotypeKind_test6 :: Test
inferMonotypeKind_test6 =
  case flip evalStateT startState $ inferMonotypeKind (1 :: Integer, 3 :: Integer) context1 (MEVar $ ETypeVar "Konrad") of
    Left (UndeclaredETypeVarError (1, 3) (ETypeVar "Konrad")) -> True
    _ -> False

inferMonotypeKind_test7 :: Test
inferMonotypeKind_test7 =
  case flip evalStateT startState $ inferMonotypeKind "1, 3" context2 (MArrow (MProduct [MUnit, MUnit] 2) (MEVar $ ETypeVar "c")) of
    Right KStar -> True
    _ -> False

inferMonotypeKind_test8 :: Test
inferMonotypeKind_test8 =
  case flip evalStateT startState $ inferMonotypeKind ("1", "3") context2 (MGADT "Lion" [MProduct [MUnit, MUnit] 2, MSucc $ MSucc MZero]) of
    Left (MismatchedGADTArityError ("1", "3") "Lion" 1 2) -> True
    _ -> False

inferMonotypeKind_test9 :: Test
inferMonotypeKind_test9 =
  case flip evalStateT startState $ inferMonotypeKind ("1", "3") context2 (MGADT "F" [MProduct [MZero, MUnit] 2, MSucc $ MSucc MZero]) of
    Left (UndeclaredGADTError ("1", "3") "F") -> True
    _ -> False

--checkMonotypeHasKind :: Context -> Monotype -> p -> Kind -> Either (Error p) ()
checkMonotypeHasKind_test1 :: Test
checkMonotypeHasKind_test1 =
  case flip evalStateT startState $ checkMonotypeHasKind "3.14" [] (MArrow MUnit MUnit) KStar of
    Right () -> True
    _ -> False

checkMonotypeHasKind_test2 :: Test
checkMonotypeHasKind_test2 =
  case flip evalStateT startState $ checkMonotypeHasKind () context5 (MSucc $ MSucc (MEVar $ ETypeVar "x")) KNat of
    Right () -> True
    _ -> False

checkMonotypeHasKind_test3 :: Test
checkMonotypeHasKind_test3 =
  case flip evalStateT startState $ checkMonotypeHasKind () [CTypeVar (E $ ETypeVar "a") KStar, CETypeVar (ETypeVar "a") KNat MZero]
            (MSucc $ MSucc (MEVar $ ETypeVar "a")) KNat of
    Left (MonotypeHasWrongKindError () (MEVar (ETypeVar "a")) KNat KStar) -> True
    _ -> False

checkMonotypeHasKind_test4 :: Test
checkMonotypeHasKind_test4 =
  case flip evalStateT startState $ checkMonotypeHasKind () [CTypeVar (E $ ETypeVar "a") KStar, CETypeVar (ETypeVar "a") KNat MZero]
            (MArrow MUnit (MEVar $ ETypeVar "a")) KStar of
    Right () -> True
    _ -> False

checkMonotypeHasKind_test5 :: Test
checkMonotypeHasKind_test5 =
  case flip evalStateT startState $ checkMonotypeHasKind () context5 (MSucc $ MSucc (MUVar $ UTypeVar "x")) KNat of
    Left (UndeclaredUTypeVarError () (UTypeVar "x")) -> True
    _ -> False

checkMonotypeHasKind_test6 :: Test
checkMonotypeHasKind_test6 =
  case flip evalStateT startState $ checkMonotypeHasKind () context5 (MSucc $ MSucc (MUVar $ UTypeVar "xx")) KNat of
    Left (UndeclaredUTypeVarError () (UTypeVar "xx")) -> True
    _ -> False

checkMonotypeHasKind_test7 :: Test
checkMonotypeHasKind_test7 =
  case flip evalStateT startState $ checkMonotypeHasKind () context5 (MSucc $ MSucc (MEVar $ ETypeVar "")) KNat of
    Left (UndeclaredETypeVarError () (ETypeVar "")) -> True
    _ -> False

--checkPropWellFormedness :: Context -> Proposition -> p -> Either (Error p) ()
checkPropWellFormedness_test1 :: Test
checkPropWellFormedness_test1 =
  case flip evalStateT startState $ checkPropWellFormedness (5 :: Integer) [] (MZero, MZero) of
    Right () -> True
    _ -> False

checkPropWellFormedness_test2 :: Test
checkPropWellFormedness_test2 =
  case flip evalStateT startState $ checkPropWellFormedness (5 :: Integer) [] (MZero, MSucc $ MSucc MZero) of
    Right () -> True
    _ -> False

checkPropWellFormedness_test3 :: Test
checkPropWellFormedness_test3 =
  case flip evalStateT startState $ checkPropWellFormedness (5 :: Integer) [] (MSucc $ MSucc MZero, MProduct [MUnit, MUnit] 2) of
    Left (MonotypeHasWrongKindError 5 (MProduct [MUnit, MUnit] 2) KNat KStar) -> True
    _ -> False

checkPropWellFormedness_test4 :: Test
checkPropWellFormedness_test4 =
  case flip evalStateT startState $ checkPropWellFormedness (5 :: Integer) [] (MSucc $ MSucc MZero, MProduct [MUnit, MSucc MZero] 2) of
    Left (MonotypeHasWrongKindError 5 (MSucc MZero) KStar KNat) -> True
    _ -> False

checkPropWellFormedness_test5 :: Test
checkPropWellFormedness_test5 =
  case flip evalStateT startState $ checkPropWellFormedness () context1 (MSucc $ MSucc  (MEVar $ ETypeVar "b"), MProduct [MUnit, MSucc MZero] 2) of
    Left (MonotypeHasWrongKindError () (MSucc MZero) KStar KNat) -> True
    _ -> False

checkPropWellFormedness_test6 :: Test
checkPropWellFormedness_test6 =
  case flip evalStateT startState $ checkPropWellFormedness () context5 (MSucc $ MSucc  (MUVar $ UTypeVar "x"), MEVar $ ETypeVar "x") of
    Left (UndeclaredUTypeVarError () (UTypeVar "x")) -> True
    _ -> False

checkPropWellFormedness_test7 :: Test
checkPropWellFormedness_test7 =
  case flip evalStateT startState $ checkPropWellFormedness () context5 (MSucc $ MSucc  (MUVar $ UTypeVar "r"), MEVar $ ETypeVar "x") of
    Left (UndeclaredUTypeVarError () (UTypeVar "r")) -> True
    _ -> False

--checkTypeWellFormedness :: Context -> Type -> p -> Either (Error p) ()
checkTypeWellFormedness_test1 :: Test
checkTypeWellFormedness_test1 =
  case flip evalStateT startState $ checkTypeWellFormedness () context1
            (TArrow TUnit $ TGADT "Lion" [ParameterType $ TProduct [TUnit, TUnit] 2]) of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test2 :: Test
checkTypeWellFormedness_test2 =
  case flip evalStateT startState $ checkTypeWellFormedness () context1 (TGADT "Terminator" [ParameterType $ TUVar $ UTypeVar "y",
                                                    ParameterType $ TProduct [TEVar $ ETypeVar "z", TEVar $ ETypeVar "a"] 2]) of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test3 :: Test
checkTypeWellFormedness_test3 =
  case flip evalStateT startState $ checkTypeWellFormedness ((), ()) context1 (TGADT "Terminator" [ParameterType $ TUVar $ UTypeVar "y",
                                                    ParameterType $ TProduct [TEVar $ ETypeVar "z", TEVar $ ETypeVar "b"] 2]) of
    Left (TypeHasWrongKindError ((), ()) (TEVar (ETypeVar "b")) KStar KNat) -> True
    _ -> False

checkTypeWellFormedness_test4 :: Test
checkTypeWellFormedness_test4 =
  case flip evalStateT startState $ checkTypeWellFormedness ((), ()) [] (TGADT "Terminator" [ParameterType $ TUVar $ UTypeVar "y",
                                              ParameterType $ TProduct [TEVar $ ETypeVar "z", TEVar $ ETypeVar "b"] 2]) of
    Left (UndeclaredUTypeVarError ((), ()) (UTypeVar "y")) -> True
    _ -> False

checkTypeWellFormedness_test5 :: Test
checkTypeWellFormedness_test5 =
  case flip evalStateT startState $ checkTypeWellFormedness ((), ()) [] (TProduct [TEVar $ ETypeVar "z", TEVar $ ETypeVar "b"] 2) of
    Left (UndeclaredETypeVarError ((), ()) (ETypeVar "z")) -> True
    _ -> False

checkTypeWellFormedness_test6 :: Test
checkTypeWellFormedness_test6 =
  case flip evalStateT startState $ checkTypeWellFormedness (5 :: Integer) context5 (TUVar $ UTypeVar "x") of
    Left (UndeclaredUTypeVarError 5 (UTypeVar "x")) -> True
    _ -> False

checkTypeWellFormedness_test7 :: Test
checkTypeWellFormedness_test7 =
  case flip evalStateT startState $ checkTypeWellFormedness () context5 (TUniversal (UTypeVar "x") KStar (TArrow (TUVar $ UTypeVar "x") TUnit)) of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test8 :: Test
checkTypeWellFormedness_test8 =
  case flip evalStateT startState $ checkTypeWellFormedness () context5
            (TUniversal (UTypeVar "Konrad") KStar (TArrow (TUVar $ UTypeVar "Konrad") TUnit)) of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test9 :: Test
checkTypeWellFormedness_test9 =
  case flip evalStateT startState $ checkTypeWellFormedness () []
            (TUniversal (UTypeVar "Konrad") KStar (TArrow (TUVar $ UTypeVar "Konrad") TUnit)) of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test10 :: Test
checkTypeWellFormedness_test10 =
  case flip evalStateT startState $ checkTypeWellFormedness () context1
            (TExistential (UTypeVar "b") KStar (TArrow (TEVar $ ETypeVar "b") TUnit)) of
    Left (UndeclaredETypeVarError () (ETypeVar "b")) -> True
    _ -> False

checkTypeWellFormedness_test11 :: Test
checkTypeWellFormedness_test11 =
  case flip evalStateT startState $ checkTypeWellFormedness () context1
            (TExistential (UTypeVar "Konrad") KStar (TArrow (TUVar $ UTypeVar "Konrad") TUnit)) of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test12 :: Test
checkTypeWellFormedness_test12 =
  case flip evalStateT startState $ checkTypeWellFormedness () []
        (TExistential (UTypeVar "Konrad") KStar (TArrow (TEVar $ ETypeVar "Konrad") TUnit)) of
    Left (UndeclaredETypeVarError () (ETypeVar "Konrad")) -> True
    _ -> False

checkTypeWellFormedness_test13 :: Test
checkTypeWellFormedness_test13 =
  case flip evalStateT startState $ checkTypeWellFormedness () []
        (TUniversal (UTypeVar "x") KStar (TArrow (TUVar $ UTypeVar "y") TUnit)) of
    Left (UndeclaredUTypeVarError () (UTypeVar "y")) -> True
    _ -> False

checkTypeWellFormedness_test14 :: Test
checkTypeWellFormedness_test14 =
  case flip evalStateT startState $ checkTypeWellFormedness () []
        (TExistential (UTypeVar "x") KStar (TArrow (TEVar $ ETypeVar "y") TUnit)) of
    Left (UndeclaredETypeVarError () (ETypeVar "y")) -> True
    _ -> False

checkTypeWellFormedness_test15 :: Test
checkTypeWellFormedness_test15 =
  case flip evalStateT startState $ checkTypeWellFormedness () context1 (TImp (MZero, MSucc MZero) (TArrow (TEVar $ ETypeVar "z") TUnit)) of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test16 :: Test
checkTypeWellFormedness_test16 =
  case flip evalStateT startState $ checkTypeWellFormedness () [] (TImp (MZero, MZero) (TArrow (TEVar $ ETypeVar "y") TUnit)) of
    Left (UndeclaredETypeVarError () (ETypeVar "y")) -> True
    _ -> False

checkTypeWellFormedness_test17 :: Test
checkTypeWellFormedness_test17 =
  case flip evalStateT startState $ checkTypeWellFormedness () []
            (TExistential (UTypeVar "x") KStar (TImp (MZero, MSucc MZero) (TArrow (TUVar $ UTypeVar "x") TUnit))) of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test18 :: Test
checkTypeWellFormedness_test18 =
  case flip evalStateT startState $ checkTypeWellFormedness () []
            (TExistential (UTypeVar "x") KStar (TImp (MZero, MSucc (MUVar $ UTypeVar "x")) (TArrow (TEVar $ ETypeVar "z") TUnit))) of
    Left (MonotypeHasWrongKindError () (MUVar (UTypeVar "x")) KNat KStar) -> True
    _ -> False

checkTypeWellFormedness_test19 :: Test
checkTypeWellFormedness_test19 =
  case flip evalStateT startState $ checkTypeWellFormedness () context1
            (TAnd (TArrow (TEVar $ ETypeVar "z") TUnit) (MEVar $ ETypeVar "b", MSucc MZero)) of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test20 :: Test
checkTypeWellFormedness_test20 =
  case flip evalStateT startState $ checkTypeWellFormedness () context1
            (TAnd (TArrow (TUVar $ UTypeVar "Haskell") TUnit) (MEVar $ ETypeVar "Konrad", MSucc MZero)) of
    Left (UndeclaredUTypeVarError () (UTypeVar "Haskell")) -> True
    _ -> False

checkTypeWellFormedness_test21 :: Test
checkTypeWellFormedness_test21 =
  case flip evalStateT startState $ checkTypeWellFormedness () []
            (TUniversal (UTypeVar "x") KStar (TAnd (TArrow (TUVar $ UTypeVar "x") TUnit)  (MUVar $ UTypeVar "x", MUnit))) of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test22 :: Test
checkTypeWellFormedness_test22 =
  case flip evalStateT startState $ checkTypeWellFormedness () []
            (TUniversal (UTypeVar "x") KStar (TAnd (TArrow (TUVar $ UTypeVar "x") TUnit)  (MEVar $ ETypeVar "x", MUnit))) of
    Left (UndeclaredETypeVarError () (ETypeVar "x")) -> True
    _ -> False

checkTypeWellFormedness_test23 :: Test
checkTypeWellFormedness_test23 =
  case flip evalStateT startState $ checkTypeWellFormedness () context1 (TVec (MSucc $ MSucc (MEVar $ ETypeVar "b")) (TProduct [TUnit, TUnit] 2)) of
    Right () -> True
    _ -> False

checkTypeWellFormedness_test24 :: Test
checkTypeWellFormedness_test24 =
  case flip evalStateT startState $ checkTypeWellFormedness () []
            (TUniversal (UTypeVar "n") KNat $ TVec (MSucc $ MSucc (MUVar $ UTypeVar "n")) (TProduct [TUnit, TUVar $ UTypeVar "n"] 2)) of
    Left (TypeHasWrongKindError () (TUVar (UTypeVar "n")) KStar KNat) -> True
    _ -> False

checkTypeWellFormedness_test25 :: Test
checkTypeWellFormedness_test25 =
  case flip evalStateT startState $ checkTypeWellFormedness () []
            (TExistential (UTypeVar "x") KStar $ TVec (MSucc $ MSucc (MUVar $ UTypeVar "x")) (TProduct [TUnit, TUnit] 2)) of
    Left (MonotypeHasWrongKindError () (MUVar (UTypeVar "x")) KNat KStar) -> True
    _ -> False

checkTypeWellFormedness_test26 :: Test
checkTypeWellFormedness_test26 =
  case flip evalStateT startState $ checkTypeWellFormedness () context1 (TUniversal (UTypeVar "n") KNat $ TVec (MSucc $ MSucc (MUVar $ UTypeVar "n"))
       (TImp (MEVar $ ETypeVar "b", MUVar $ UTypeVar "n") (TProduct [TUnit, TUnit] 2))) of
    Right () -> True
    _ -> False

--checkTypeWellFormednessWithPrnc :: Context -> Type -> Principality -> p -> Either (Error p) ()
checkTypeWellFormednessWithPrnc_test1 :: Test
checkTypeWellFormednessWithPrnc_test1 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () context1
            (TArrow TUnit $ TArrow TUnit (TProduct [TUnit, TUnit] 2)) Principal of
    Right () -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test2 :: Test
checkTypeWellFormednessWithPrnc_test2 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () context1
            (TArrow (TUVar $ UTypeVar "y") (TProduct [TEVar $ ETypeVar "z", TEVar $ ETypeVar "a"] 2)) Principal of
    Left (TypeFormednessPrcFEVError () [ETypeVar "a", ETypeVar "z"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test3 :: Test
checkTypeWellFormednessWithPrnc_test3 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc ((),()) context1 (TArrow (TUVar $ UTypeVar "y")
                                                (TProduct [TEVar $ ETypeVar "z", TEVar $ ETypeVar "b"] 2)) Principal of
    Left (TypeFormednessPrcFEVError ((),()) [ETypeVar "b", ETypeVar "z"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test4 :: Test
checkTypeWellFormednessWithPrnc_test4 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc ((),()) []
            (TArrow (TUVar $ UTypeVar "y") (TProduct [TEVar $ ETypeVar "z", TEVar $ ETypeVar "b"] 2)) Principal of
    Left (TypeFormednessPrcFEVError ((),()) [ETypeVar "b", ETypeVar "z"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test5 :: Test
checkTypeWellFormednessWithPrnc_test5 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc ((),()) []
            (TProduct [TEVar $ ETypeVar "z", TEVar $ ETypeVar "b"] 2) Principal of
    Left (TypeFormednessPrcFEVError ((),()) [ETypeVar "b", ETypeVar "z"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test6 :: Test
checkTypeWellFormednessWithPrnc_test6 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc (5 :: Integer) context4 (TUVar $ UTypeVar "x") Principal of
    Right () -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test7 :: Test
checkTypeWellFormednessWithPrnc_test7 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () context5
            (TUniversal (UTypeVar "x") KStar (TArrow (TUVar $ UTypeVar "x") TUnit)) Principal of
    Right () -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test8 :: Test
checkTypeWellFormednessWithPrnc_test8 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () context5
            (TUniversal (UTypeVar "Konrad") KStar (TArrow (TUVar $ UTypeVar "Konrad") TUnit)) Principal of
    Right () -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test9 :: Test
checkTypeWellFormednessWithPrnc_test9 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () []
            (TUniversal (UTypeVar "Konrad") KStar (TArrow (TUVar $ UTypeVar "Konrad") TUnit)) Principal of
    Right () -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test10 :: Test
checkTypeWellFormednessWithPrnc_test10 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () context1
            (TExistential (UTypeVar "b") KStar (TArrow (TUVar $ UTypeVar "b") TUnit)) Principal of
    Right () -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test11 :: Test
checkTypeWellFormednessWithPrnc_test11 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () context1
            (TExistential (UTypeVar "Konrad") KStar (TArrow (TEVar $ ETypeVar "Konrad") TUnit)) Principal of
    Left (UndeclaredETypeVarError () (ETypeVar "Konrad")) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test12 :: Test
checkTypeWellFormednessWithPrnc_test12 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () []
            (TExistential (UTypeVar "Konrad") KStar (TArrow (TUVar $ UTypeVar "Konrad") TUnit)) Principal of
    Right () -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test13 :: Test
checkTypeWellFormednessWithPrnc_test13 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () []
            (TUniversal (UTypeVar "x") KStar (TArrow (TUVar $ UTypeVar "y") TUnit)) Principal of
    Left (UndeclaredUTypeVarError () (UTypeVar "y")) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test14 :: Test
checkTypeWellFormednessWithPrnc_test14 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () []
            (TExistential (UTypeVar "x") KStar (TArrow (TEVar $ ETypeVar "y") TUnit)) Principal of
    Left (TypeFormednessPrcFEVError () [ETypeVar "y"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test15 :: Test
checkTypeWellFormednessWithPrnc_test15 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () context1
            (TImp (MZero, MSucc MZero) (TArrow (TEVar $ ETypeVar "z") TUnit)) Principal of
    Left (TypeFormednessPrcFEVError () [ETypeVar "z"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test16 :: Test
checkTypeWellFormednessWithPrnc_test16 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () []
            (TImp (MZero, MZero) (TArrow (TEVar $ ETypeVar "y") TUnit)) Principal of
    Left (TypeFormednessPrcFEVError () [ETypeVar "y"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test17 :: Test
checkTypeWellFormednessWithPrnc_test17 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () [] (TExistential (UTypeVar "x") KStar
       (TImp (MZero, MSucc MZero) (TArrow (TUVar $ UTypeVar "x") TUnit))) Principal of
    Right () -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test18 :: Test
checkTypeWellFormednessWithPrnc_test18 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () []
            (TExistential (UTypeVar "x") KStar (TImp (MZero, MSucc (MEVar $ ETypeVar "x")) (TArrow (TEVar $ ETypeVar "z") TUnit))) Principal of
    Left (TypeFormednessPrcFEVError () [ETypeVar "z"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test19 :: Test
checkTypeWellFormednessWithPrnc_test19 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () context1
            (TAnd (TArrow (TEVar $ ETypeVar "z") TUnit) (MEVar $ ETypeVar "b", MSucc MZero)) Principal of
    Left (TypeFormednessPrcFEVError () [ETypeVar "b", ETypeVar "z"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test20 :: Test
checkTypeWellFormednessWithPrnc_test20 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () context1
            (TAnd (TArrow (TUVar $ UTypeVar "Haskell") TUnit) (MEVar $ ETypeVar "Konrad", MSucc MZero)) Principal of
    Left (TypeFormednessPrcFEVError () [ETypeVar "Konrad"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test21 :: Test
checkTypeWellFormednessWithPrnc_test21 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () []
            (TUniversal (UTypeVar "x") KStar (TAnd (TArrow (TUVar $ UTypeVar "x") TUnit) (MUVar $ UTypeVar "x", MUnit))) Principal of
    Right () -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test22 :: Test
checkTypeWellFormednessWithPrnc_test22 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () []
            (TUniversal (UTypeVar "x") KStar (TAnd (TArrow (TUVar $ UTypeVar "x") TUnit) (MEVar $ ETypeVar "x", MUnit))) Principal of
    Left (TypeFormednessPrcFEVError () [ETypeVar "x"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test23 :: Test
checkTypeWellFormednessWithPrnc_test23 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () context1
            (TVec (MSucc $ MSucc (MEVar $ ETypeVar "b")) (TProduct [TUnit, TUnit] 2)) Principal of
    Left (TypeFormednessPrcFEVError () [ETypeVar "b"]) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test24 :: Test
checkTypeWellFormednessWithPrnc_test24 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () []
            (TUniversal (UTypeVar "n") KNat $ TVec (MSucc $ MSucc (MUVar $ UTypeVar "n"))
       (TProduct [TUnit, TUVar $ UTypeVar "n"] 2)) Principal of
    Left (TypeHasWrongKindError () (TUVar (UTypeVar "n")) KStar KNat) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test25 :: Test
checkTypeWellFormednessWithPrnc_test25 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () [] (TExistential (UTypeVar "x") KStar $
       TVec (MSucc $ MSucc (MUVar $ UTypeVar "x")) (TProduct [TUnit, TUnit] 2)) Principal of
    Left (MonotypeHasWrongKindError () (MUVar (UTypeVar "x")) KNat KStar) -> True
    _ -> False

checkTypeWellFormednessWithPrnc_test26 :: Test
checkTypeWellFormednessWithPrnc_test26 =
  case flip evalStateT startState $ checkTypeWellFormednessWithPrnc () context1
            (TUniversal (UTypeVar "n") KNat $ TVec (MSucc $ MSucc (MUVar $ UTypeVar "n"))
            (TImp (MEVar $ ETypeVar "b", MUVar $ UTypeVar "n") (TProduct [TUnit, TUnit] 2))) Principal of
    Left (TypeFormednessPrcFEVError () [ETypeVar "b"]) -> True
    _ -> False

--instantiateEVar :: Context -> ETypeVar -> Monotype -> Kind -> p -> Either (Error p) Context

instantiateEVar_test1 :: Test
instantiateEVar_test1 =
  case flip evalStateT startState $ instantiateEVar context2 (ETypeVar "b") MUnit KStar () of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CMarker, CETypeVar (ETypeVar "b") KStar MUnit, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

instantiateEVar_test2 :: Test
instantiateEVar_test2 =
  case flip evalStateT startState $ instantiateEVar context2 (ETypeVar "a") MZero KNat () of
    Right [CETypeVar (ETypeVar "a") KNat MZero, CMarker, CTypeVar (E (ETypeVar "b")) KStar, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

instantiateEVar_test3 :: Test
instantiateEVar_test3 =
  case flip evalStateT startState $ instantiateEVar context2 (ETypeVar "a") (MSucc (MSucc MZero)) KNat () of
    Right [CETypeVar (ETypeVar "a") KNat (MSucc (MEVar (ETypeVar "a-1"))), CETypeVar (ETypeVar "a-1") KNat (MSucc (MEVar (ETypeVar "a-1-1"))),
           CETypeVar (ETypeVar "a-1-1") KNat MZero, CMarker, CTypeVar (E (ETypeVar "b")) KStar, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

instantiateEVar_test4 :: Test
instantiateEVar_test4 =
  case flip evalStateT startState $ instantiateEVar context2 (ETypeVar "b") (MProduct [MUnit, MUnit] 2) KStar () of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CMarker, CETypeVar (ETypeVar "b") KStar (MProduct [MEVar (ETypeVar "b-1"), MEVar (ETypeVar "b-2")] 2),
           CETypeVar (ETypeVar "b-1") KStar MUnit, CETypeVar (ETypeVar "b-2") KStar MUnit, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

instantiateEVar_test5 :: Test
instantiateEVar_test5 =
  case flip evalStateT startState $ instantiateEVar context2 (ETypeVar "b") (MGADT "Ko" [MUnit, MUnit]) KStar () of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CMarker, CETypeVar (ETypeVar "b") KStar (MGADT "Ko" [MEVar (ETypeVar "b-1"), MEVar (ETypeVar "b-2")]),
           CETypeVar (ETypeVar "b-1") KStar MUnit, CETypeVar (ETypeVar "b-2") KStar MUnit, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

instantiateEVar_test6 :: Test
instantiateEVar_test6 =
  case flip evalStateT startState $ instantiateEVar context2 (ETypeVar "b") (MArrow MUnit MUnit) KStar () of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CMarker, CETypeVar (ETypeVar "b") KStar (MArrow (MEVar (ETypeVar "b-1")) (MEVar (ETypeVar "b-2"))),
           CETypeVar (ETypeVar "b-1") KStar MUnit, CETypeVar (ETypeVar "b-2") KStar MUnit, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

instantiateEVar_test7 :: Test
instantiateEVar_test7 =
  case flip evalStateT startState $ instantiateEVar context2 (ETypeVar "b") MUnit KNat () of
    Left (MonotypeHasWrongKindError () MUnit KNat KStar) -> True
    _ -> False

instantiateEVar_test8 :: Test
instantiateEVar_test8 =
  case flip evalStateT startState $ instantiateEVar context2 (ETypeVar "a") MZero KStar () of
    Left (MonotypeHasWrongKindError () MZero KStar KNat) -> True
    _ -> False

instantiateEVar_test9 :: Test
instantiateEVar_test9 =
  case flip evalStateT startState $ instantiateEVar context2 (ETypeVar "a") (MSucc (MSucc MZero)) KStar () of
    Left (MonotypeHasWrongKindError () (MSucc (MSucc MZero)) KStar KNat) -> True
    _ -> False

instantiateEVar_test10 :: Test
instantiateEVar_test10 =
  case flip evalStateT startState $ instantiateEVar context2 (ETypeVar "b") (MProduct [MUnit, MUnit] 2) KNat () of
    Left (MonotypeHasWrongKindError () (MProduct [MUnit, MUnit] 2) KNat KStar) -> True
    _ -> False

instantiateEVar_test11 :: Test
instantiateEVar_test11 =
  case flip evalStateT startState $ instantiateEVar context2 (ETypeVar "b") (MGADT "F" [MUnit, MZero]) KStar () of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CMarker, CETypeVar (ETypeVar "b") KStar (MGADT "F" [MEVar (ETypeVar "b-1"), MEVar (ETypeVar "b-2")]),
           CETypeVar (ETypeVar "b-1") KStar MUnit, CETypeVar (ETypeVar "b-2") KNat MZero, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

instantiateEVar_test12 :: Test
instantiateEVar_test12 =
  case flip evalStateT startState $ instantiateEVar context2 (ETypeVar "b") (MArrow (MSucc MZero) MZero) KStar () of
    Left (MonotypeHasWrongKindError () (MSucc MZero) KStar KNat) -> True
    _ -> False

instantiateEVar_test13 :: Test
instantiateEVar_test13 =
  case flip evalStateT startState $ instantiateEVar context2 (ETypeVar "c") (MEVar (ETypeVar "b")) KStar () of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CMarker, CETypeVar (ETypeVar "b") KStar (MEVar (ETypeVar "c")), CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

instantiateEVar_test14 :: Test
instantiateEVar_test14 =
  case flip evalStateT startState $ instantiateEVar context2 (ETypeVar "b") (MEVar (ETypeVar "c")) KStar () of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CMarker, CETypeVar (ETypeVar "b") KStar (MEVar (ETypeVar "c")), CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

instantiateEVar_test15 :: Test
instantiateEVar_test15 =
  case flip evalStateT startState $ instantiateEVar context1 (ETypeVar "a") (MEVar (ETypeVar "z")) KStar () of
    Left (ETypeVarTypeMismatchError () (ETypeVar "z") (MProduct [MUnit, MUnit] 2) (MEVar (ETypeVar "a"))) -> True
    _ -> False

instantiateEVar_test16 :: Test
instantiateEVar_test16 =
  case flip evalStateT startState $ instantiateEVar context3 (ETypeVar "z") (MEVar (ETypeVar "a")) KStar () of
    Left (ETypeVarTypeMismatchError () (ETypeVar "z") (MProduct [MUnit, MUnit] 2) (MEVar (ETypeVar "a"))) -> True
    _ -> False

instantiateEVar_test17 :: Test
instantiateEVar_test17 =
  case flip evalStateT startState $ instantiateEVar context2 (ETypeVar "c") (MEVar (ETypeVar "b")) KNat () of
    Left (ETypeVarKindMismatchError () (ETypeVar "b") KStar KNat) -> True
    _ -> False

instantiateEVar_test18 :: Test
instantiateEVar_test18 =
  case flip evalStateT startState $ instantiateEVar context2 (ETypeVar "c") (MEVar (ETypeVar "a")) KStar () of
    Left (ETypeVarKindMismatchError () (ETypeVar "a") KNat KStar) -> True
    _ -> False

instantiateEVar_test19 :: Test
instantiateEVar_test19 =
  case flip evalStateT startState $ instantiateEVar context3 (ETypeVar "b") (MEVar (ETypeVar "a")) KStar () of
    Left (ETypeVarTypeMismatchError () (ETypeVar "a") MUnit (MEVar(ETypeVar "b"))) -> True
    _ -> False

instantiateEVar_test20 :: Test
instantiateEVar_test20 =
  case flip evalStateT startState $ instantiateEVar [CTypeVar (U (UTypeVar "a")) KStar, CTypeVar (E (ETypeVar "b")) KStar]
            (ETypeVar "b") (MEVar (ETypeVar "a")) KStar () of
    Left (UndeclaredETypeVarError () (ETypeVar "a")) -> True
    _ -> False

instantiateEVar_test21 :: Test
instantiateEVar_test21 =
  case flip evalStateT startState $ instantiateEVar context1 (ETypeVar "Konrad") MUnit KStar () of
    Left (UndeclaredETypeVarError () (ETypeVar "Konrad")) -> True
    _ -> False

instantiateEVar_test22 :: Test
instantiateEVar_test22 =
  case flip evalStateT startState $ instantiateEVar context1 (ETypeVar "Konrad") (MEVar (ETypeVar "a")) KStar () of
    Left (UndeclaredETypeVarError () (ETypeVar "Konrad")) -> True
    _ -> False

instantiateEVar_test23 :: Test
instantiateEVar_test23 =
  case flip evalStateT startState $ instantiateEVar context5 (ETypeVar "x") (MEVar (ETypeVar "x")) KNat () of
    Right c -> c == context5
    _ -> False

instantiateEVar_test24 :: Test
instantiateEVar_test24 =
  case flip evalStateT startState $ instantiateEVar context4 (ETypeVar "x") (MEVar (ETypeVar "x")) KStar () of
    Left (UndeclaredETypeVarError () (ETypeVar "x")) -> True
    _ -> False

instantiateEVar_test25 :: Test
instantiateEVar_test25 =
  case flip evalStateT startState $ instantiateEVar [CETypeVar (ETypeVar "a") KStar (MEVar (ETypeVar "r")), CTypeVar (E (ETypeVar "r")) KStar]
                       (ETypeVar "r") (MEVar (ETypeVar "a")) KStar () of
    Right [CETypeVar (ETypeVar "a") KStar (MEVar (ETypeVar "r")), CTypeVar (E (ETypeVar "r")) KStar] -> True
    _ -> False

instantiateEVar_test26 :: Test
instantiateEVar_test26 =
  case flip evalStateT startState $ instantiateEVar context2 (ETypeVar "b") (MGADT "F" [MArrow MUnit MZero, MZero]) KStar () of
    Left (MonotypeHasWrongKindError () MZero KStar KNat) -> True
    _ -> False

--checkEquation :: Context -> Monotype -> Monotype -> Kind -> p -> Either (Error p) Context
checkEquation_test1 :: Test
checkEquation_test1 =
  case flip evalStateT startState $ checkEquation context1
            (MArrow (MProduct [MUnit, MUnit] 2) MUnit) (MArrow (MProduct [MUnit, MUnit] 2) MUnit) KStar () of
    Right c -> context1 == c
    _ -> False

checkEquation_test2 :: Test
checkEquation_test2 =
  case flip evalStateT startState $ checkEquation context1 (MSucc (MSucc (MSucc MZero))) (MSucc (MSucc (MSucc MZero))) KNat () of
    Right c -> context1 == c
    _ -> False

checkEquation_test3 :: Test
checkEquation_test3 =
  case flip evalStateT startState $ checkEquation context1
            (MArrow (MProduct [MUnit, MUnit] 2) MUnit) (MArrow (MGADT "F" [MUnit, MUnit]) MUnit) KStar () of
    Left (EquationFalseError () (MProduct [MUnit, MUnit] 2) (MGADT "F" [MUnit, MUnit]) KStar) -> True
    _ -> False

checkEquation_test4 :: Test
checkEquation_test4 =
  case flip evalStateT startState $ checkEquation context1
            (MArrow (MProduct [MUnit, MUnit] 2) MUnit) (MArrow (MProduct [MUnit, MUnit] 2) MUnit) KNat () of
    Left (EquationFalseError () (MArrow (MProduct [MUnit, MUnit] 2) MUnit) (MArrow (MProduct [MUnit, MUnit] 2) MUnit) KNat) -> True
    _ -> False

checkEquation_test5 :: Test
checkEquation_test5 =
  case flip evalStateT startState $ checkEquation context1 (MSucc (MSucc (MSucc MZero))) (MSucc (MSucc (MSucc MZero))) KStar () of
    Left (EquationFalseError () (MSucc (MSucc (MSucc MZero))) (MSucc (MSucc (MSucc MZero))) KStar) -> True
    _ -> False

checkEquation_test6 :: Test
checkEquation_test6 =
  case flip evalStateT startState $ checkEquation context1
            (MArrow (MProduct [MUnit, MUnit] 2) MUnit) (MSucc (MSucc (MSucc MZero))) KStar () of
    Left (EquationFalseError () (MArrow (MProduct [MUnit, MUnit] 2) MUnit) (MSucc (MSucc (MSucc MZero))) KStar) -> True
    _ -> False

checkEquation_test7 :: Test
checkEquation_test7 =
  case flip evalStateT startState $ checkEquation context1
            (MArrow (MProduct [MUnit, MUnit] 2) MUnit) (MSucc (MSucc (MSucc MZero))) KNat () of
    Left (EquationFalseError () (MArrow (MProduct [MUnit, MUnit] 2) MUnit) (MSucc (MSucc (MSucc MZero))) KNat) -> True
    _ -> False

checkEquation_test8 :: Test
checkEquation_test8 =
  case flip evalStateT startState $ checkEquation context1 (MSucc (MSucc MZero)) (MSucc (MSucc (MSucc MZero))) KNat () of
    Left (EquationFalseError ()  MZero (MSucc MZero) KNat)  -> True
    _ -> False

checkEquation_test9 :: Test
checkEquation_test9 =
  case flip evalStateT startState $ checkEquation context1
            (MArrow (MProduct [MUnit, MUnit] 2) MUnit) (MSucc (MSucc (MSucc MZero))) KStar () of
    Left (EquationFalseError () (MArrow (MProduct [MUnit, MUnit] 2) MUnit) (MSucc (MSucc (MSucc MZero))) KStar) -> True
    _ -> False

checkEquation_test10 :: Test
checkEquation_test10 =
  case flip evalStateT startState $ checkEquation context1
            (MSucc (MSucc (MSucc (MUVar (UTypeVar "x"))))) (MSucc (MSucc (MSucc (MUVar (UTypeVar "x"))))) KNat () of
    Right c -> c == context1
    _ -> False

checkEquation_test11 :: Test
checkEquation_test11 =
  case flip evalStateT startState $ checkEquation context1
            (MSucc (MSucc (MSucc (MUVar (UTypeVar "x"))))) (MSucc (MSucc (MSucc (MUVar (UTypeVar "y"))))) KNat () of
    Left (EquationFalseError () (MUVar (UTypeVar "x")) (MUVar (UTypeVar "y")) KNat) -> True
    _ -> False

checkEquation_test12 :: Test
checkEquation_test12 =
  case flip evalStateT startState $ checkEquation context1
            (MSucc (MSucc (MSucc (MUVar (UTypeVar "x"))))) (MSucc (MSucc (MUVar (UTypeVar "x")))) KNat () of
    Left (EquationFalseError () (MSucc (MUVar (UTypeVar "x"))) (MUVar (UTypeVar "x")) KNat) -> True
    _ -> False

checkEquation_test13 :: Test
checkEquation_test13 =
  case flip evalStateT startState $ checkEquation context1 (MEVar (ETypeVar "a")) MUnit KStar () of
    Right c -> c == context3
    _ -> False

checkEquation_test14 :: Test
checkEquation_test14 =
  case flip evalStateT startState $ checkEquation context1  MUnit (MEVar (ETypeVar "a")) KStar () of
    Right c -> c == context3
    _ -> False

checkEquation_test15 :: Test
checkEquation_test15 =
  case flip evalStateT startState $ checkEquation context1 (MEVar (ETypeVar "a")) MUnit KNat () of
    Left (MonotypeHasWrongKindError () MUnit KNat KStar) -> True
    _ -> False

checkEquation_test16 :: Test
checkEquation_test16 =
  case flip evalStateT startState $ checkEquation context1  MUnit (MEVar (ETypeVar "a")) KNat () of
    Left (MonotypeHasWrongKindError () MUnit KNat KStar) -> True
    _ -> False

checkEquation_test17 :: Test
checkEquation_test17 =
  case flip evalStateT startState $ checkEquation context5 (MEVar (ETypeVar "x")) (MEVar (ETypeVar "x")) KStar () of
    Right c -> c == context5
    _ -> False

checkEquation_test18 :: Test
checkEquation_test18 =
  case flip evalStateT startState $ checkEquation context2
            (MEVar (ETypeVar "x")) (MGADT "E" [MEVar (ETypeVar "x"), MEVar (ETypeVar "x")]) KStar () of
    Left (EquationFalseError () (MEVar (ETypeVar "x")) (MGADT "E" [MEVar (ETypeVar "x"), MEVar (ETypeVar "x")]) KStar) -> True
    _ -> False

checkEquation_test19 :: Test
checkEquation_test19 =
  case flip evalStateT startState $ checkEquation context2
            (MEVar (ETypeVar "b")) (MGADT "R" [MEVar (ETypeVar "c"), MEVar (ETypeVar "c")]) KStar () of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CMarker, CETypeVar (ETypeVar "b") KStar (MGADT "R" [MEVar (ETypeVar "b-1"), MEVar (ETypeVar "b-2")]),
           CETypeVar (ETypeVar "b-1") KStar (MEVar (ETypeVar "c")), CETypeVar (ETypeVar "b-2") KStar (MEVar (ETypeVar "c")),
           CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

checkEquation_test20 :: Test
checkEquation_test20 =
  case flip evalStateT startState $ checkEquation context2
            (MEVar (ETypeVar "b")) (MGADT "F" [MEVar (ETypeVar "y"), MEVar (ETypeVar "z")]) KStar () of
    Left (UndeclaredETypeVarError () (ETypeVar "y")) -> True
    _ -> False

checkEquation_test21 :: Test
checkEquation_test21 =
  case flip evalStateT startState $ checkEquation [CTypeVar (E (ETypeVar "k")) KNat, CTypeVar (E (ETypeVar "a")) KNat]
            (MEVar (ETypeVar "a")) (MSucc (MEVar (ETypeVar "k"))) KNat () of
    Right [CETypeVar (ETypeVar "k") KNat (MEVar (ETypeVar "a-1")), CETypeVar (ETypeVar "a") KNat (MSucc (MEVar (ETypeVar "a-1"))),
           CTypeVar (E (ETypeVar "a-1")) KNat] -> True
    _ -> False

checkEquation_test22 :: Test
checkEquation_test22 =
  case flip evalStateT startState $ checkEquation [CTypeVar (E (ETypeVar "k")) KNat, CTypeVar (E (ETypeVar "a")) KNat]
            (MEVar (ETypeVar "a")) (MSucc (MEVar (ETypeVar "r"))) KNat () of
    Left (UndeclaredETypeVarError () (ETypeVar "r")) -> True
    _ -> False

checkEquation_test23 :: Test
checkEquation_test23 =
  case flip evalStateT startState $ checkEquation context2
            (MEVar (ETypeVar "b")) (MGADT "F" [MArrow (MEVar (ETypeVar "c")) MUnit, MEVar (ETypeVar "c")]) KStar () of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CMarker, CETypeVar (ETypeVar "b") KStar (MGADT "F" [MEVar (ETypeVar "b-1"), MEVar (ETypeVar "b-2")]),
           CETypeVar (ETypeVar "b-1") KStar (MArrow (MEVar (ETypeVar "b-1-1")) (MEVar (ETypeVar "b-1-2"))),
           CETypeVar (ETypeVar "b-1-1") KStar (MEVar (ETypeVar "c")), CETypeVar (ETypeVar "b-1-2") KStar MUnit,
           CETypeVar (ETypeVar "b-2") KStar (MEVar (ETypeVar "c")), CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

checkEquation_test24 :: Test
checkEquation_test24 =
  case flip evalStateT startState $ checkEquation context2
            (MEVar (ETypeVar "b")) (MGADT "W" [MArrow (MEVar (ETypeVar "r")) MUnit, MEVar (ETypeVar "c")]) KStar () of
    Left (UndeclaredETypeVarError () (ETypeVar "r")) -> True
    _ -> False

--equivalentProp :: Context -> Proposition -> Proposition -> p -> Either (Error p) Context
equivalentProp_test1 :: Test
equivalentProp_test1 =
  case flip evalStateT startState $ equivalentProp context1
            (MArrow (MProduct [MUnit, MUnit] 2) MUnit, MGADT "Terminator" [MUnit, MProduct [MUnit, MUnit] 2])
            (MArrow (MProduct [MUnit, MUnit] 2) MUnit, MGADT "Terminator" [MUnit, MProduct [MUnit, MUnit] 2]) () of
    Right c -> c == context1
    _ -> False

equivalentProp_test2 :: Test
equivalentProp_test2 =
  case flip evalStateT startState $ equivalentProp context1
            (MArrow (MProduct [MUnit, MUnit] 2) MUnit, MGADT "Terminator" [MUnit, MProduct [MUnit, MUnit] 2])
            (MArrow (MProduct [MUnit, MUnit] 2) MUnit, MGADT "Terminator" [MUnit, MArrow MUnit MUnit]) () of
    Left (EquationFalseError () (MProduct [MUnit, MUnit] 2) (MArrow MUnit MUnit) KStar) -> True
    _ -> False

equivalentProp_test3 :: Test
equivalentProp_test3 =
  case flip evalStateT startState $ equivalentProp context1
            (MArrow (MProduct [MGADT "Terminator" [MUnit, MUnit], MUnit] 2) MUnit, MGADT "Terminator" [MUnit, MProduct [MUnit, MUnit] 2])
            (MArrow (MProduct [MUnit, MUnit] 2) MUnit, MGADT "Terminator" [MUnit, MArrow MUnit MUnit]) () of
    Left (EquationFalseError () (MGADT "Terminator" [MUnit, MUnit]) MUnit KStar) -> True
    _ -> False

equivalentProp_test4 :: Test
equivalentProp_test4 =
  case flip evalStateT startState $ equivalentProp context1
            (MArrow (MProduct [MGADT "Terminator" [MUnit, MUnit], MUnit] 2) MUnit, MSucc MZero)
            (MArrow (MProduct [MUnit, MUnit] 2) MUnit, MGADT "Terminator" [MUnit, MArrow MUnit MUnit]) () of
    Left (MonotypeHasWrongKindError () (MSucc MZero) KStar KNat) -> True
    _ -> False

equivalentProp_test5 :: Test
equivalentProp_test5 =
  case flip evalStateT startState $ equivalentProp context1 (MZero, MSucc MZero) (MZero, MSucc MZero) () of
    Right c -> c == context1
    _ -> False

equivalentProp_test6 :: Test
equivalentProp_test6 =
  case flip evalStateT startState $ equivalentProp context1 (MZero, MSucc MZero) (MZero, MSucc (MSucc MZero)) () of
    Left (EquationFalseError () MZero (MSucc MZero) KNat) -> True
    _ -> False

equivalentProp_test7 :: Test
equivalentProp_test7 =
  case flip evalStateT startState $ equivalentProp context2 (MEVar (ETypeVar "a"),  MSucc (MSucc MZero)) (MZero, MSucc (MSucc MZero)) () of
    Right [CETypeVar (ETypeVar "a") KNat MZero, CMarker, CTypeVar (E (ETypeVar "b")) KStar, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

equivalentProp_test8 :: Test
equivalentProp_test8 =
  case flip evalStateT startState $ equivalentProp context5 (MSucc MZero, MEVar (ETypeVar "a")) (MSucc MZero, MZero) () of
    Left (UndeclaredETypeVarError () (ETypeVar "a")) -> True
    _ -> False

equivalentProp_test9 :: Test
equivalentProp_test9 =
  case flip evalStateT startState $ equivalentProp context5
            (MEVar (ETypeVar "a"), MSucc (MEVar $ ETypeVar "R")) (MEVar (ETypeVar "a"), MSucc (MEVar $ ETypeVar "R")) () of
    Left (UndeclaredETypeVarError () (ETypeVar "a")) -> True
    _ -> False

equivalentProp_test10 :: Test
equivalentProp_test10 =
  case flip evalStateT startState $ equivalentProp context1
            (MArrow (MProduct [MUnit, MUnit] 2) MUnit, MGADT "Terminator" [MUnit, MProduct [MUnit, MUnit] 2])
            (MArrow (MProduct [MUnit, MUnit] 2) MUnit, MGADT "Lion" [MProduct [MUnit, MUnit] 2]) () of
    Left (EquationFalseError () (MGADT "Terminator" [MUnit, MProduct [MUnit, MUnit] 2]) (MGADT "Lion" [MProduct [MUnit, MUnit] 2]) KStar) -> True
    _ -> False

--equivalentType :: Context -> Type -> Type -> p -> StateT Integer (Either (Error p)) Context
equivalentType_test1 :: Test
equivalentType_test1 =
  case flip evalStateT startState $ equivalentType context1 (TProduct [TGADT "Y" [ParameterType $ TUVar $ UTypeVar "r",
                                                             ParameterType TUnit], TArrow TUnit (TEVar $ ETypeVar "z")] 2)
                                                            (TProduct [TGADT "Y" [ParameterType $ TUVar $ UTypeVar "r",
                                                             ParameterType TUnit], TArrow TUnit (TEVar $ ETypeVar "z")] 2) () of
    Right c -> c == context1
    _ -> False

equivalentType_test2 :: Test
equivalentType_test2 =
  case flip evalStateT startState $ equivalentType context5 (TProduct [TGADT "U" [ParameterType $ TUVar $ UTypeVar "r",
                                                             ParameterType TUnit], TArrow TUnit (TEVar $ ETypeVar "p")] 2)
                                                            (TProduct [TGADT "U" [ParameterType $ TUVar $ UTypeVar "l",
                                                             ParameterType TUnit], TArrow TUnit (TEVar $ ETypeVar "p")] 2) () of
    Left (TypesNotEquivalentError () (TUVar (UTypeVar "r")) (TUVar (UTypeVar "l"))) -> True
    _ -> False

equivalentType_test3 :: Test
equivalentType_test3 =
  case flip evalStateT startState $ equivalentType context5 (TProduct [TGADT "K" [ParameterType $ TUVar $ UTypeVar "r", ParameterType TUnit],
                                                             TArrow TUnit (TEVar $ ETypeVar "p")] 2)
                                                            (TGADT "K" [ParameterType $ TProduct [TUVar $ UTypeVar "r", TUnit] 2,
                                                            ParameterType $ TArrow TUnit (TEVar $ ETypeVar "p")]) () of
    Left (TypesNotEquivalentError () (TProduct [TGADT "K" [ParameterType (TUVar (UTypeVar "r")), ParameterType TUnit], TArrow TUnit (TEVar (ETypeVar "p"))] 2)
                                     (TGADT "K" [ParameterType (TProduct [TUVar (UTypeVar "r"), TUnit] 2),
                                     ParameterType (TArrow TUnit (TEVar (ETypeVar "p")))])) -> True
    _ -> False

equivalentType_test4 :: Test
equivalentType_test4 =
  case flip evalStateT startState $ equivalentType context1 (TProduct [TGADT "K" [ParameterType $ TUVar $ UTypeVar "r",
                                                             ParameterType TUnit], TArrow TUnit (TEVar $ ETypeVar "a")] 2)
                                                            (TProduct [TGADT "K" [ParameterType $ TUVar $ UTypeVar "r",
                                                             ParameterType TUnit], TArrow TUnit TUnit] 2) () of
    Right c -> c == context3
    _ -> False

equivalentType_test5 :: Test
equivalentType_test5 =
  case flip evalStateT startState $ equivalentType [CETypeVar(ETypeVar "z") KStar (MProduct [MEVar (ETypeVar "z-1"), MEVar (ETypeVar "z-2")] 2),
                                           CETypeVar(ETypeVar "z-1") KStar MUnit, CETypeVar(ETypeVar "z-2") KStar MUnit,
                                           CETypeVar (ETypeVar "b") KNat (MSucc (MEVar (ETypeVar "b-1"))), CETypeVar(ETypeVar "b-1") KNat MZero]
                                          (TVec (MEVar (ETypeVar "b"))  (TProduct [TUnit, TUnit] 2))
                                          (TVec (MSucc MZero) (TEVar (ETypeVar "z"))) () of
     Right [CETypeVar(ETypeVar "z") KStar (MProduct [MEVar (ETypeVar "z-1"), MEVar (ETypeVar "z-2")] 2),
            CETypeVar(ETypeVar "z-1") KStar MUnit, CETypeVar(ETypeVar "z-2") KStar MUnit,
            CETypeVar (ETypeVar "b") KNat (MSucc (MEVar (ETypeVar "b-1"))), CETypeVar(ETypeVar "b-1") KNat MZero] -> True
     _ -> False

equivalentType_test6 :: Test
equivalentType_test6 =
  case flip evalStateT startState $ equivalentType context2 (TVec (MEVar (ETypeVar "a"))  (TProduct [TUnit, TUnit] 2))
                                                   (TVec (MSucc MZero) (TEVar (ETypeVar "c"))) () of
      Right c -> c == [CETypeVar (ETypeVar "a") KNat (MSucc (MEVar (ETypeVar "a-1"))), CETypeVar(ETypeVar "a-1") KNat MZero,
                       CMarker, CTypeVar (E (ETypeVar "b")) KStar,
                       CETypeVar(ETypeVar "c") KStar (MProduct [MEVar (ETypeVar "c-1"), MEVar (ETypeVar "c-2")] 2),
                       CETypeVar(ETypeVar "c-1") KStar MUnit, CETypeVar(ETypeVar "c-2") KStar MUnit]
      _ -> False

equivalentType_test7 :: Test
equivalentType_test7 =
  case flip evalStateT startState $ equivalentType context1 (TVec (MEVar (ETypeVar "b")) (TEVar (ETypeVar "z")))
                                                   (TVec (MEVar (ETypeVar "b")) (TEVar (ETypeVar "z"))) () of
     Right c -> c == context1
     _ -> False

equivalentType_test8 :: Test
equivalentType_test8 =
 case flip evalStateT startState $ equivalentType [CETypeVar (ETypeVar "b") KNat (MSucc (MEVar (ETypeVar "b-1"))), CETypeVar(ETypeVar "b-1") KNat MZero]
                                         (TVec (MEVar (ETypeVar "b"))  (TProduct [TUnit, TUnit] 2))
                                         (TVec (MSucc (MSucc MZero))   (TEVar (ETypeVar "z"))) () of
    Left (ETypeVarTypeMismatchError () (ETypeVar "b-1") MZero (MSucc (MEVar (ETypeVar "b-1-1")))) -> True
    _ -> False

equivalentType_test9 :: Test
equivalentType_test9 =
  case flip evalStateT startState $ equivalentType context2 (TVec (MEVar (ETypeVar "a"))  (TEVar (ETypeVar "b")))
                                                   (TVec (MSucc MZero) (TEVar (ETypeVar "c"))) () of
      Right c -> c == [CETypeVar (ETypeVar "a") KNat (MSucc (MEVar (ETypeVar "a-1"))), CETypeVar(ETypeVar "a-1") KNat MZero,
                       CMarker, CETypeVar (ETypeVar "b") KStar (MEVar (ETypeVar "c")), CTypeVar (E (ETypeVar "c")) KStar]
      _ -> False

equivalentType_test10 :: Test
equivalentType_test10 =
  case flip evalStateT startState $ equivalentType context2 (TVec (MEVar (ETypeVar "a"))  (TEVar (ETypeVar "a")))
                                                   (TVec (MSucc MZero) (TEVar (ETypeVar "b"))) () of
      Left (TypeHasWrongKindError () (TEVar (ETypeVar  "a")) KStar KNat) -> True
      _ -> False

equivalentType_test11 :: Test
equivalentType_test11 =
  case flip evalStateT startState $ equivalentType context2 (TVec (MEVar (ETypeVar "b"))  (TEVar (ETypeVar "b")))
                                                   (TVec (MSucc MZero) (TEVar (ETypeVar "a"))) () of
      Left (ETypeVarKindMismatchError () (ETypeVar "b") KStar KNat) -> True
      _ -> False

equivalentType_test12 :: Test
equivalentType_test12 =
  case flip evalStateT startState $ equivalentType context2 (TUniversal (UTypeVar "r") KNat (TVec (MUVar (UTypeVar "r"))  (TEVar (ETypeVar "b"))))
                                                   (TUniversal (UTypeVar "r") KNat (TVec (MSucc MZero) (TEVar (ETypeVar "b")))) () of
      Left (EquationFalseError () (MUVar (UTypeVar "#0")) (MSucc MZero) KNat) -> True
      _ -> False

equivalentType_test13 :: Test
equivalentType_test13 =
  case flip evalStateT startState $ equivalentType context2 (TUniversal (UTypeVar "r") KNat (TVec (MUVar (UTypeVar "r"))  (TEVar (ETypeVar "b"))))
                                                   (TUniversal (UTypeVar "l") KNat (TVec (MUVar (UTypeVar "l"))  (TEVar (ETypeVar "b")))) () of
      Right c -> c == context2
      _ -> False

equivalentType_test14 :: Test
equivalentType_test14 =
  case flip evalStateT startState $ equivalentType context2 (TExistential (UTypeVar "r") KStar (TVec MZero (TUVar (UTypeVar "r"))))
                                                   (TExistential (UTypeVar "l") KStar (TVec MZero (TUVar (UTypeVar "l")))) () of
      Right c -> c == context2
      _ -> False

equivalentType_test15 :: Test
equivalentType_test15 =
  case flip evalStateT startState $ equivalentType context2 (TExistential (UTypeVar "r") KStar (TVec MZero (TUVar (UTypeVar "r"))))
                                                   (TExistential (UTypeVar "l") KStar (TVec MZero (TEVar (ETypeVar "b")))) () of
      Left (UndeclaredUTypeVarError () (UTypeVar "#0")) -> True
      _ -> False

equivalentType_test16 :: Test
equivalentType_test16 =
  case flip evalStateT startState $ equivalentType context2 (TExistential (UTypeVar "r") KNat (TVec MZero (TUVar (UTypeVar "r"))))
                                                   (TExistential (UTypeVar "l") KNat (TVec MZero (TUVar (UTypeVar "prl")))) () of
      Left (TypesNotEquivalentError () (TUVar (UTypeVar "#0")) (TUVar (UTypeVar "prl"))) -> True
      _ -> False

equivalentType_test17 :: Test
equivalentType_test17 =
  case flip evalStateT startState $ equivalentType [] (TExistential (UTypeVar "r") KStar (TVec MZero (TUVar (UTypeVar "r"))))
                                             (TExistential (UTypeVar "l") KStar (TVec MZero (TUVar (UTypeVar "l")))) () of
      Right [] -> True
      _ -> False


equivalentType_test18 :: Test
equivalentType_test18 =
  case flip evalStateT startState $ equivalentType [] (TExistential (UTypeVar "r") KStar (TVec MZero (TUVar (UTypeVar "r"))))
                                             (TUniversal (UTypeVar "l") KStar (TVec MZero (TUVar (UTypeVar "l")))) () of
      Left (TypesNotEquivalentError () TExistential {} TUniversal {}) -> True
      _ -> False

equivalentType_test19 :: Test
equivalentType_test19 =
  case flip evalStateT startState $ equivalentType context2 (TImp (MEVar (ETypeVar "a"), MSucc MZero) (TVec (MEVar (ETypeVar "a")) TUnit))
                                                   (TImp (MSucc MZero, MEVar (ETypeVar "a")) (TVec (MSucc MZero) (TEVar (ETypeVar "b")))) () of
    Right [CETypeVar (ETypeVar "a") KNat (MSucc (MEVar (ETypeVar "a-1"))), CETypeVar (ETypeVar "a-1") KNat MZero,
           CMarker, CETypeVar (ETypeVar "b") KStar MUnit, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

equivalentType_test20 :: Test
equivalentType_test20 =
  case flip evalStateT startState $ equivalentType context2 (TAnd (TVec (MEVar (ETypeVar "a")) TUnit) (MEVar (ETypeVar "b"), MUnit))
                                                   (TAnd (TVec (MSucc MZero) (TEVar (ETypeVar "b"))) (MUnit, MEVar (ETypeVar "b"))) () of
    Right [CETypeVar (ETypeVar "a") KNat (MSucc (MEVar (ETypeVar "a-1"))), CETypeVar (ETypeVar "a-1") KNat MZero,
           CMarker, CETypeVar (ETypeVar "b") KStar MUnit, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

equivalentType_test21 :: Test
equivalentType_test21 =
  case flip evalStateT startState $ equivalentType context2 (TImp (MEVar (ETypeVar "a"), MUnit) (TVec (MEVar (ETypeVar "a")) TUnit))
                                                   (TAnd (TVec (MSucc MZero) (TEVar (ETypeVar "b"))) (MSucc MZero, MEVar (ETypeVar "b"))) () of
    Left (TypesNotEquivalentError () TImp {} TAnd {}) -> True
    _ -> False

equivalentType_test22 :: Test
equivalentType_test22 =
  case flip evalStateT startState $ equivalentType context2 (TAnd (TVec (MEVar (ETypeVar "a")) TUnit) (MEVar (ETypeVar "b"), MProduct [MUnit, MUnit] 2))
                                                   (TAnd (TVec (MSucc MZero) (TEVar (ETypeVar "b"))) (MUnit, MEVar (ETypeVar "b"))) () of
    Left (EquationFalseError () (MProduct [MUnit, MUnit] 2) MUnit KStar) -> True
    _ -> False

equivalentType_test23 :: Test
equivalentType_test23 =
  case flip evalStateT startState $ equivalentType context2 (TImp (MEVar (ETypeVar "a"), MZero) (TVec (MEVar (ETypeVar "a")) TUnit))
                                                   (TImp (MSucc MZero, MEVar (ETypeVar "a")) (TVec (MSucc MZero) (TEVar (ETypeVar "b")))) () of
    Left (EquationFalseError () MZero (MSucc MZero) KNat) -> True
    _ -> False

equivalentType_test24 :: Test
equivalentType_test24 =
  case flip evalStateT startState $ equivalentType [] (TEVar (ETypeVar "a")) (TArrow (TEVar (ETypeVar "a") ) TUnit) () of
    Left (TypesNotEquivalentError () TEVar {} TArrow {}) -> True
    _ -> False

equivalentType_test25 :: Test
equivalentType_test25 =
  case flip evalStateT startState $ equivalentType [] (TArrow (TEVar (ETypeVar "a") ) TUnit) (TEVar (ETypeVar "a"))  () of
    Left (TypesNotEquivalentError () TArrow {} TEVar {}) -> True
    _ -> False

equivalentType_test26 :: Test
equivalentType_test26 =
  case flip evalStateT startState $ equivalentType [CTypeVar (E (ETypeVar "a")) KStar] (TEVar (ETypeVar "a")) TUnit () of
    Right [CETypeVar (ETypeVar "a") KStar MUnit] -> True
    _ -> False

equivalentType_test27 :: Test
equivalentType_test27 =
  case flip evalStateT startState $ equivalentType [CETypeVar (ETypeVar "a") KStar MUnit] TUnit (TEVar (ETypeVar "a"))  () of
    Right [CETypeVar (ETypeVar "a") KStar MUnit] -> True
    _ -> False

--subtype :: Context -> Type -> Polarity -> Type -> p -> StateT Integer (Either (Error p)) Context
subtype_test1 :: Test
subtype_test1 =
  case flip evalStateT startState $ subtype [CTypeVar (E (ETypeVar "x")) KStar] (TArrow (TUVar (UTypeVar "r")) (TEVar (ETypeVar "x")))
                          (joinPolarity (polarity (TArrow (TUVar (UTypeVar "r")) (TEVar (ETypeVar "x")))) (polarity (TArrow (TUVar (UTypeVar "r")) TUnit)))
                          (TArrow (TUVar (UTypeVar "r")) TUnit) () of
    Right [CETypeVar (ETypeVar "x") KStar MUnit] -> True
    _ -> False

subtype_test2 :: Test
subtype_test2 =
  case flip evalStateT startState $ subtype context5 (TUniversal (UTypeVar "x") KStar (TUVar (UTypeVar "x")))
                          (joinPolarity (polarity $ TUniversal (UTypeVar "x") KStar (TUVar (UTypeVar "x"))) (polarity $ TProduct [TUnit, TUnit] 2))
                          (TProduct [TUnit, TUnit] 2) () of
    Right c -> c == context5
    _ -> False

subtype_test3 :: Test
subtype_test3 =
  case flip evalStateT startState $ subtype context5 (TProduct [TUnit, TUnit] 2)
                          (joinPolarity  (polarity $ TProduct [TUnit, TUnit] 2) (polarity $ TExistential (UTypeVar "x") KStar (TUVar (UTypeVar "x"))))
                          (TExistential (UTypeVar "x") KStar (TUVar (UTypeVar "x"))) () of
    Right c -> c == context5
    _ -> False

subtype_test4 :: Test
subtype_test4 =
  case flip evalStateT startState $ subtype context5 (TUniversal (UTypeVar "x") KStar (TUVar (UTypeVar "x")))
                          (joinPolarity (polarity $ TUniversal (UTypeVar "x") KStar (TUVar (UTypeVar "x")))
                          (polarity $ TExistential (UTypeVar "x") KStar (TUVar (UTypeVar "x"))))
                          (TExistential (UTypeVar "x") KStar (TUVar (UTypeVar "x"))) () of
    Right c -> c == context5
    _ -> False

subtype_test5 :: Test
subtype_test5 =
  case flip evalStateT startState $ subtype context5 (TUniversal (UTypeVar "x") KStar (TArrow TUnit (TUVar (UTypeVar "x"))))
                          (joinPolarity (polarity $ TUniversal (UTypeVar "x") KStar (TArrow TUnit (TUVar (UTypeVar "x"))))
                          (polarity $ TExistential (UTypeVar "x") KStar (TArrow (TUVar (UTypeVar "x")) TUnit)))
                          (TExistential (UTypeVar "x") KStar (TArrow (TUVar (UTypeVar "x")) TUnit)) () of
    Right c -> c == context5
    _ -> False

subtype_test6 :: Test
subtype_test6 =
  case flip evalStateT startState $ subtype context5 (TUniversal (UTypeVar "x") KStar (TUVar (UTypeVar "x")))
                          (joinPolarity (polarity $ TUniversal (UTypeVar "x") KStar (TUVar (UTypeVar "x")))
                          (polarity $ TUniversal (UTypeVar "x") KStar (TUVar (UTypeVar "x"))))
                          (TUniversal (UTypeVar "x") KStar (TUVar (UTypeVar "x"))) () of
    Right c -> c == context5
    _ -> False

subtype_test7 :: Test
subtype_test7 =
  case flip evalStateT startState $ subtype context5 (TExistential (UTypeVar "x") KStar (TUVar (UTypeVar "x")))
                          (joinPolarity (polarity $ TExistential (UTypeVar "x") KStar (TUVar (UTypeVar "x")))
                          (polarity $ TExistential (UTypeVar "x") KStar (TUVar (UTypeVar "x"))))
                          (TExistential (UTypeVar "x") KStar (TUVar (UTypeVar "x"))) () of
    Right c -> c == context5
    _ -> False

subtype_test8 :: Test
subtype_test8 =
  case flip evalStateT startState $ subtype context5 (TUniversal (UTypeVar "x") KStar (TUVar (UTypeVar "x")))
            Positive (TUniversal (UTypeVar "x") KStar (TUVar (UTypeVar "x"))) () of
    Right c -> c == context5
    _ -> False

subtype_test9 :: Test
subtype_test9 =
  case flip evalStateT startState $ subtype context5 (TExistential (UTypeVar "x") KStar (TUVar (UTypeVar "x")))
            Negative (TExistential (UTypeVar "x") KStar (TUVar (UTypeVar "x"))) () of
    Right c -> c == context5
    _ -> False

subtype_test10 :: Test
subtype_test10 =
  case flip evalStateT startState $ subtype [] (TUVar (UTypeVar "y")) Positive (TUniversal (UTypeVar "x") KStar (TUVar (UTypeVar "y"))) () of
    Right [] -> True
    _ -> False

subtype_test11 :: Test
subtype_test11 =
  case flip evalStateT startState $ subtype context4 (TUVar (UTypeVar "x")) Negative (TExistential (UTypeVar "x") KStar (TUVar (UTypeVar "x"))) () of
    Right c -> c == context4
    _ -> False

subtype_test12 :: Test
subtype_test12 =
  case flip evalStateT startState $ subtype context1
            (TUniversal (UTypeVar "x") KStar (TUniversal (UTypeVar "y") KStar (TArrow (TUVar (UTypeVar "x")) (TUVar (UTypeVar "y")))))
             Negative
            (TExistential (UTypeVar "a") KStar (TExistential (UTypeVar "b") KStar (TArrow (TUVar (UTypeVar "b"))  (TUVar (UTypeVar "a"))))) () of
    Right c -> c == context1
    _ -> False

subtype_test13 :: Test
subtype_test13 =
  case flip evalStateT startState $ subtype [] (TExistential (UTypeVar "x") KStar (TUVar (UTypeVar "x")))
                           Positive (TUniversal (UTypeVar "x") KStar (TUVar (UTypeVar "x"))) () of
    Left (TypesNotEquivalentError () (TUVar (UTypeVar "#0")) (TUVar (UTypeVar "#1"))) -> True
    _ -> False

subtype_test14 :: Test
subtype_test14 =
  case flip evalStateT startState $ subtype [] TUnit Positive (TArrow TUnit TUnit) () of
    Left (TypesNotEquivalentError () TUnit (TArrow TUnit TUnit)) -> True
    _ -> False

--eliminateEquation :: Context -> Monotype -> Monotype -> Kind -> p -> MaybeT (Either (Error p)) Context
eliminateEquation_test1 :: Test
eliminateEquation_test1 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation [] (MProduct [MArrow (MGADT "F" [MFloat, MString]) MChar, MInt] 2)
                                        (MProduct [MArrow (MGADT "F" [MFloat, MString]) MChar, MInt] 2) KStar () of
    Right (Just []) -> True
    _ -> False

eliminateEquation_test2 :: Test
eliminateEquation_test2 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation context1 (MSucc (MSucc (MSucc MZero))) (MSucc (MSucc (MSucc MZero))) KNat () of
    Right (Just c) -> c == context1
    _ -> False

eliminateEquation_test3 :: Test
eliminateEquation_test3 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation [] (MProduct [MArrow (MGADT "F" [MFloat, MString]) MBool, MInt] 2)
                                        (MProduct [MArrow (MGADT "F" [MFloat, MString]) MChar, MInt] 2) KStar () of
    Right Nothing -> True
    _ -> False

eliminateEquation_test4 :: Test
eliminateEquation_test4 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation context1 (MSucc (MSucc (MSucc MZero))) (MSucc (MSucc (MSucc (MSucc MZero)))) KNat () of
    Right Nothing -> True
    _ -> False

eliminateEquation_test5 :: Test
eliminateEquation_test5 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation context5
            (MSucc (MSucc (MSucc (MUVar $ UTypeVar "x")))) (MSucc (MSucc (MSucc (MUVar $ UTypeVar "x")))) KNat () of
    Right (Just c) -> context5 == c
    _ -> False

eliminateEquation_test6 :: Test
eliminateEquation_test6 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation context1 (MUVar $ UTypeVar "y") (MSucc (MSucc (MSucc MZero))) KNat () of
    Right (Just c) -> c == CUTypeVarEq (UTypeVar "y") (MSucc (MSucc (MSucc MZero))) : context1
    _ -> False

eliminateEquation_test7 :: Test
eliminateEquation_test7 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation context1 (MUVar $ UTypeVar "n") (MSucc (MSucc (MSucc MZero))) KNat () of
    Left (UndeclaredUTypeVarError () (UTypeVar "n")) -> True
    _ -> False

eliminateEquation_test8 :: Test
eliminateEquation_test8 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation context1 MString (MUVar $ UTypeVar "y")  KStar () of
    Right (Just c) -> c == CUTypeVarEq (UTypeVar "y") MString : context1
    _ -> False

eliminateEquation_test9 :: Test
eliminateEquation_test9 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation [CUTypeVarEq (UTypeVar "y") (MArrow MString MChar),
                                      CTypeVar (U $ UTypeVar "y") KStar] (MUVar $ UTypeVar "y") MChar KStar () of
    Left (EquationAlreadyExistsError () (UTypeVar "y") (MArrow MString MChar) MChar) -> True
    _ -> False

eliminateEquation_test10 :: Test
eliminateEquation_test10 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation [CUTypeVarEq (UTypeVar "y") MString, CTypeVar (U $ UTypeVar "y") KStar]
            MString (MUVar $ UTypeVar "y")  KStar () of
    Left (EquationAlreadyExistsError () (UTypeVar "y") MString MString) -> True
    _ -> False

eliminateEquation_test11 :: Test
eliminateEquation_test11 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation context1 (MUVar $ UTypeVar "y") (MUVar $ UTypeVar "yolo") KNat () of
    Right (Just c) -> c == CUTypeVarEq (UTypeVar "y") (MUVar (UTypeVar "yolo")) : context1
    _ -> False

eliminateEquation_test12 :: Test
eliminateEquation_test12 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation context1 (MUVar $ UTypeVar "y") (MArrow MInt (MUVar $ UTypeVar "y")) KNat () of
    Right Nothing -> True
    _ -> False

eliminateEquation_test13 :: Test
eliminateEquation_test13 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation context1 MChar (MSucc MZero) KNat () of
    Left (EliminateEquationError () MChar (MSucc MZero) KNat) -> True
    _ -> False

eliminateEquation_test14 :: Test
eliminateEquation_test14 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation context1 MZero MBool KStar () of
    Left (EliminateEquationError () MZero MBool KStar) -> True
    _ -> False

eliminateEquation_test15 :: Test
eliminateEquation_test15 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation context1 MChar (MSucc MZero) KStar () of
    Left (EliminateEquationError () MChar (MSucc MZero) KStar) -> True
    _ -> False

eliminateEquation_test16 :: Test
eliminateEquation_test16 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation context1 MZero MBool KNat () of
    Left (EliminateEquationError () MZero MBool KNat) -> True
    _ -> False

eliminateEquation_test17 :: Test
eliminateEquation_test17 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation context1 (MEVar $ ETypeVar "k") (MSucc MZero) KNat () of
    Left (EliminateEquationError () (MEVar (ETypeVar "k")) (MSucc MZero) KNat) -> True
    _ -> False

eliminateEquation_test18 :: Test
eliminateEquation_test18 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation context1 MBool (MEVar $ ETypeVar "o") KStar () of
    Left (EliminateEquationError () MBool (MEVar (ETypeVar "o")) KStar) -> True
    _ -> False

eliminateEquation_test19 :: Test
eliminateEquation_test19 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation context1 (MEVar $ ETypeVar "n") (MEVar $ ETypeVar "r") KStar () of
    Left (EliminateEquationError () (MEVar (ETypeVar "n")) (MEVar (ETypeVar "r")) KStar) -> True
    _ -> False

eliminateEquation_test20 :: Test
eliminateEquation_test20 =
  case flip evalStateT startState $ runMaybeT $ eliminateEquation context1 (MEVar $ ETypeVar "a") (MEVar $ ETypeVar "a") KNat () of
    Left (EliminateEquationError () (MEVar (ETypeVar "a")) (MEVar (ETypeVar "a")) KNat) -> True
    _ -> False

--inferSpine ::
--  Context -> Spine p -> Type -> Principality
--  -> StateT TypecheckerState (Either (Error p)) (Type, Principality, Context)
inferSpine_test1 :: Test
inferSpine_test1 =
  case flip evalStateT startState $ inferSpine [] [] TInt Principal of
    Right (TInt, Principal, []) -> True
    _ -> False

inferSpine_test2 :: Test
inferSpine_test2 =
  case flip evalStateT startState $ inferSpine [] [EBool () True] (TArrow TBool TInt) Principal of
    Right (TInt, Principal, []) -> True
    _ -> False

inferSpine_test3 :: Test
inferSpine_test3 =
  case flip evalStateT startState $ inferSpine [] [EString () "KW"] (TArrow TBool TInt) Principal of
    Left (TypeInferenceError (EString () "KW")) -> True
    _ -> False

inferSpine_test4 :: Test
inferSpine_test4 =
  case flip evalStateT startState $ inferSpine [] [EBool () True, EChar  () 'k'] (TArrow TBool (TArrow TChar TString)) NotPrincipal of
    Right (TString, NotPrincipal, []) -> True
    _ -> False

inferSpine_test5 :: Test
inferSpine_test5 =
  case flip evalStateT startState $ inferSpine [] [EBool () True, EBool () False] (TArrow TBool (TArrow TChar TString)) NotPrincipal of
    Left (TypeInferenceError (EBool () False)) -> True
    _ -> False

inferSpine_test6 :: Test
inferSpine_test6 =
  case flip evalStateT startState $ inferSpine [] [EBool () True, EChar  () 'k']
                                    (TUniversal (UTypeVar "a") KStar (TArrow TBool (TArrow (TUVar (UTypeVar "a")) TString))) NotPrincipal of
    Right (TString, NotPrincipal, [CETypeVar (ETypeVar "a") KStar MChar]) -> True
    _ -> False

inferSpine_test7 :: Test
inferSpine_test7 =
  case flip evalStateT startState $ inferSpine [] [EBool () True, ETuple () [EChar  () 'k', EInt () 2] 2]
                                    (TUniversal (UTypeVar "a") KStar (TArrow TBool (TArrow (TUVar (UTypeVar "a")) TString))) NotPrincipal of
    Right (TString, NotPrincipal, [CETypeVar (ETypeVar "a") KStar (MProduct [MEVar (ETypeVar "a-1"), MEVar (ETypeVar "a-2")] 2),
                                   CETypeVar (ETypeVar "a-1") KStar MChar, CETypeVar (ETypeVar "a-2") KStar MInt]) -> True
    _ -> False

inferSpine_test8 :: Test
inferSpine_test8 =
  case flip evalStateT startState $ inferSpine [] [EBool () True, EChar  () 'k']
                                    (TUniversal (UTypeVar "a") KStar (TArrow TBool (TArrow (TUVar (UTypeVar "a")) TString))) Principal of
    Right (TString, NotPrincipal, [CETypeVar (ETypeVar "a") KStar MChar]) -> True
    _ -> False

inferSpine_test9 :: Test
inferSpine_test9 =
  case flip evalStateT startState $ inferSpine [] [EBool () True, ETuple () [EChar  () 'k', EInt () 2] 2]
                                    (TUniversal (UTypeVar "a") KStar (TArrow TBool (TArrow (TUVar (UTypeVar "a")) TString))) Principal of
    Right (TString, NotPrincipal, [CETypeVar (ETypeVar "a") KStar (MProduct [MEVar (ETypeVar "a-1"), MEVar (ETypeVar "a-2")] 2),
                                   CETypeVar (ETypeVar "a-1") KStar MChar, CETypeVar (ETypeVar "a-2") KStar MInt]) -> True
    _ -> False

inferSpine_test10 :: Test
inferSpine_test10 =
  case flip evalStateT startState $ inferSpine [] [EBool () True, EChar  () 'k']
                                    (TUniversal (UTypeVar "a") KStar (TImp (MUVar (UTypeVar "a"), MChar)
                                    (TArrow TBool (TArrow (TUVar (UTypeVar "a")) TString)))) NotPrincipal of
    Right (TString, NotPrincipal, [CETypeVar (ETypeVar "a") KStar MChar]) -> True
    _ -> False

inferSpine_test11 :: Test
inferSpine_test11 =
  case flip evalStateT startState $ inferSpine [] [EBool () True, EChar  () 'k']
                                    (TUniversal (UTypeVar "a") KStar (TImp (MUVar (UTypeVar "a"), MInt)
                                    (TArrow TBool (TArrow (TUVar (UTypeVar "a")) TString)))) NotPrincipal of
    Left (TypeInferenceError (EChar () 'k')) -> True
    _ -> False

inferSpine_test12 :: Test
inferSpine_test12 =
  case flip evalStateT startState $ inferSpine [] [EBool () True, EChar  () 'k']
                                    (TUniversal (UTypeVar "a") KStar (TImp (MUVar (UTypeVar "a"), MChar)
                                    (TArrow TBool (TArrow (TUVar (UTypeVar "a")) TString)))) Principal of
    Right (TString, NotPrincipal, [CETypeVar (ETypeVar "a") KStar MChar]) -> True
    _ -> False

inferSpine_test13 :: Test
inferSpine_test13 =
  case flip evalStateT startState $ inferSpine [] [EBool () True, EChar  () 'k']
                                    (TUniversal (UTypeVar "a") KStar (TImp (MUVar (UTypeVar "a"), MInt)
                                    (TArrow TBool (TArrow (TUVar (UTypeVar "a")) TString)))) Principal of
    Left (TypeInferenceError (EChar () 'k')) -> True
    _ -> False

--checkExpr :: Context -> Expr p -> Type -> Principality -> StateT sTypecheckerState (Either (Error p)) Context
checkExpr_ESimpleType_test1 :: Test
checkExpr_ESimpleType_test1 =
  case flip evalStateT startState $ checkExpr context1 (EInt () 5) TInt Principal of
    Right c -> c == context1
    _ -> False

checkExpr_ESimpleType_test2 :: Test
checkExpr_ESimpleType_test2 =
  case flip evalStateT startState $ checkExpr [] (EBool () True) TBool NotPrincipal of
    Right [] -> True
    _ -> False

checkExpr_ESimpleType_test3 :: Test
checkExpr_ESimpleType_test3 =
  case flip evalStateT startState $ checkExpr context1 (EUnit ()) (TEVar $ ETypeVar "a") NotPrincipal of
    Right c -> c == context3
    _ -> False

checkExpr_ESimpleType_test4 :: Test
checkExpr_ESimpleType_test4 =
  case flip evalStateT startState $ checkExpr context1 (EFloat () 3.14) (TEVar $ ETypeVar "z") NotPrincipal of
    Left (ETypeVarTypeMismatchError () (ETypeVar "z") (MProduct [MUnit, MUnit] 2) MFloat) -> True
    _ -> False

checkExpr_ESimpleType_test5 :: Test
checkExpr_ESimpleType_test5 =
  case flip evalStateT startState $ checkExpr context3 (EUnit ()) (TEVar $ ETypeVar "a") NotPrincipal of
    Right c -> c == context3
    _ -> False

checkExpr_ESimpleType_test6 :: Test
checkExpr_ESimpleType_test6 =
  case flip evalStateT startState $ checkExpr context3 (EChar () 'k') (TEVar $ ETypeVar "Konrad") NotPrincipal of
    Left (UndeclaredETypeVarError () (ETypeVar "Konrad")) -> True
    _ -> False

checkExpr_ESimpleType_test7 :: Test
checkExpr_ESimpleType_test7 =
  case flip evalStateT startState $ checkExpr context3 (EString () "Konrad") TString Principal of
    Right c -> c == context3
    _ -> False

checkExpr_ETuple_test1 :: Test
checkExpr_ETuple_test1 =
  case flip evalStateT startState $ checkExpr context1 (ETuple () [EUnit (), EBool () False] 2) (TProduct [TUnit, TBool] 2) Principal of
    Right c -> c == context1
    _ -> False

checkExpr_ETuple_test2 :: Test
checkExpr_ETuple_test2 =
  case flip evalStateT startState $ checkExpr context5 (ETuple () [ETuple () [EInt () 44, EFloat () 3.14] 2, EChar () 'c'] 2)
                          (TProduct [TProduct [TInt, TFloat] 2, TChar] 2) NotPrincipal of
    Right c -> c == context5
    _ -> False

checkExpr_ETuple_test3 :: Test
checkExpr_ETuple_test3 =
  case flip evalStateT startState $ checkExpr
            [CTypeVar (E $ ETypeVar "x") KStar] (ETuple () [ETuple () [EUnit (), EUnit ()] 2, EUnit ()] 2) (TEVar $ ETypeVar "x") NotPrincipal of
    Right c -> c == [CETypeVar (ETypeVar "x") KStar (MProduct [MEVar (ETypeVar "x-1"), MEVar (ETypeVar "x-2")] 2),
                     CETypeVar (ETypeVar "x-1") KStar (MProduct [MEVar (ETypeVar "x-1-1"), MEVar (ETypeVar "x-1-2")] 2),
                     CETypeVar (ETypeVar "x-1-1") KStar MUnit, CETypeVar (ETypeVar "x-1-2") KStar MUnit, CETypeVar (ETypeVar "x-2") KStar MUnit]
    _ -> False

checkExpr_ETuple_test4 :: Test
checkExpr_ETuple_test4 =
  case flip evalStateT startState $ checkExpr context1 (ETuple () [EUnit (), EUnit ()] 2) (TEVar $ ETypeVar "z") NotPrincipal of
    Left (ETypeVarTypeMismatchError () (ETypeVar "z") (MProduct [MUnit, MUnit] 2) (MProduct [MEVar (ETypeVar "z-1"), MEVar (ETypeVar "z-2")] 2)) -> True
    _ -> False

checkExpr_ETuple_test5 :: Test
checkExpr_ETuple_test5 =
  case flip evalStateT startState $ checkExpr [CETypeVar (ETypeVar "x") KStar (MProduct [MEVar (ETypeVar "x-1"), MEVar (ETypeVar "x-2")] 2),
                  CETypeVar (ETypeVar "x-1") KStar MUnit, CETypeVar (ETypeVar "x-2") KStar MUnit]
                 (ETuple () [EUnit (), EUnit ()] 2) (TEVar $ ETypeVar "x") NotPrincipal of
    Right c -> c == [CETypeVar (ETypeVar "x") KStar (MProduct [MEVar (ETypeVar "x-1"), MEVar (ETypeVar "x-2")] 2),
                     CETypeVar (ETypeVar "x-1") KStar MUnit, CETypeVar (ETypeVar "x-2") KStar MUnit]
    _ -> False

checkExpr_ETuple_test6 :: Test
checkExpr_ETuple_test6 =
  case flip evalStateT startState $ checkExpr context1 (ETuple () [EUnit (), EUnit ()] 2) (TEVar $ ETypeVar "zz") NotPrincipal of
    Left (UndeclaredETypeVarError () (ETypeVar "zz")) -> True
    _ -> False

checkExpr_ETuple_test7 :: Test
checkExpr_ETuple_test7 =
  case flip evalStateT startState $ checkExpr [CTypeVar (E $ ETypeVar "x") KStar] (ETuple () [ETuple () [ETuple () [EUnit (), EUnit ()] 2, EUnit ()] 2,
                  ETuple () [EUnit (), EUnit ()] 2] 2) (TProduct [TEVar $ ETypeVar "x", TEVar $ ETypeVar "x"] 2) NotPrincipal of
    Left (TypeInferenceError (EUnit ())) -> True
    _ -> False

checkExpr_ETuple_test8 :: Test
checkExpr_ETuple_test8 =
  case flip evalStateT startState $ checkExpr [CTypeVar (E $ ETypeVar "x") KStar] (ETuple () [ETuple () [EUnit (), EUnit ()] 2,
                  ETuple () [EUnit (), EUnit ()] 2] 2) (TProduct [TEVar $ ETypeVar "x", TEVar $ ETypeVar "x"] 2) NotPrincipal of
    Right c -> c == [CETypeVar (ETypeVar "x") KStar (MProduct [MEVar (ETypeVar "x-1"), MEVar (ETypeVar "x-2")] 2),
                     CETypeVar (ETypeVar "x-1") KStar MUnit, CETypeVar (ETypeVar "x-2") KStar MUnit]
    _ -> False

checkExpr_ETuple_test9 :: Test
checkExpr_ETuple_test9 =
  case flip evalStateT startState $ checkExpr [CTypeVar (U $ UTypeVar "x") KStar] (ETuple () [ETuple () [EUnit (), EUnit ()] 2,
                  ETuple () [EUnit (), EUnit ()] 2] 2)
                  (TImp (MUVar $ UTypeVar "x", MProduct [MUnit, MUnit] 2) (TProduct [TUVar $ UTypeVar "x", TUVar $ UTypeVar "x"] 2)) Principal of
    Right [CTypeVar (U (UTypeVar "x")) KStar] -> True
    _ -> False

checkExpr_ETuple_test10 :: Test
checkExpr_ETuple_test10 =
  case flip evalStateT startState $ checkExpr [CTypeVar (U $ UTypeVar "x") KStar] (ETuple () [ETuple () [EUnit (), EUnit ()] 2,
                  ETuple () [EUnit (), EUnit ()] 2] 2)
                  (TImp (MSucc MZero, MZero) TBool) Principal of
    Right [CTypeVar (U (UTypeVar "x")) KStar] -> True
    _ -> False

checkExpr_ETuple_test11 :: Test
checkExpr_ETuple_test11 =
  case flip evalStateT startState $ checkExpr [CTypeVar (E $ ETypeVar "x") KStar] (ETuple () [ETuple () [EUnit (), EUnit ()] 2,
                  ETuple () [EUnit (), EUnit ()] 2] 2)
                  (TAnd (TProduct [TEVar $ ETypeVar "x", TEVar $ ETypeVar "x"] 2) (MEVar $ ETypeVar "x", MProduct [MUnit, MUnit] 2)) Principal of
    Right [CETypeVar (ETypeVar "x") KStar (MProduct [MEVar (ETypeVar "x-1"),MEVar (ETypeVar "x-2")] 2),
           CETypeVar (ETypeVar "x-1") KStar MUnit, CETypeVar (ETypeVar "x-2") KStar MUnit] -> True
    _ -> False

checkExpr_ELambda_test1 :: Test
checkExpr_ELambda_test1 =
  case flip evalStateT startState $ checkExpr [] (ELambda () "x" $ EVar () "x") (TArrow TUnit TUnit) NotPrincipal of
    Right [] -> True
    _ -> False

checkExpr_ELambda_test2 :: Test
checkExpr_ELambda_test2 =
  case flip evalStateT startState $ checkExpr context2 (ELambda () "x" $ EVar () "x") (TArrow TUnit TUnit) Principal of
    Right c -> c == context2
    _ -> False

checkExpr_ELambda_test3 :: Test
checkExpr_ELambda_test3 =
  case flip evalStateT startState $ checkExpr [] (ELambda () "x" (ELambda () "y" $ EVar () "x")) (TArrow TUnit (TArrow TUnit TUnit)) NotPrincipal of
    Right [] -> True
    _ -> False

checkExpr_ELambda_test4 :: Test
checkExpr_ELambda_test4 =
  case flip evalStateT startState $ checkExpr context2 (ELambda () "x" (ELambda () "y" $ EVar () "x")) (TArrow TUnit (TArrow TUnit TUnit)) Principal of
    Right c -> c == context2
    _ -> False

checkExpr_ELambda_test5 :: Test
checkExpr_ELambda_test5 =
  case flip evalStateT startState $ checkExpr [] (ELambda () "x" (ELambda () "x" $ EVar () "x")) (TArrow TUnit (TArrow TUnit TUnit)) NotPrincipal of
    Right [] -> True
    _ -> False

checkExpr_ELambda_test6 :: Test
checkExpr_ELambda_test6 =
  case flip evalStateT startState $ checkExpr context2 (ELambda () "x" (ELambda () "x" $ EVar () "x")) (TArrow TUnit (TArrow TUnit TUnit)) NotPrincipal of
    Right c -> c == context2
    _ -> False

checkExpr_ELambda_test7 :: Test
checkExpr_ELambda_test7 =
  case flip evalStateT startState $ checkExpr context2 (ELambda () "x" $ EVar () "x") (TEVar $ ETypeVar "b") NotPrincipal of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CMarker, CETypeVar (ETypeVar "b") KStar (MArrow (MEVar (ETypeVar "b-1")) (MEVar (ETypeVar "b-2"))),
           CETypeVar (ETypeVar "b-1") KStar (MEVar (ETypeVar "b-2")), CTypeVar (E (ETypeVar "b-2")) KStar, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

checkExpr_ELambda_test8 :: Test
checkExpr_ELambda_test8 =
  case flip evalStateT startState $ checkExpr context2 (ELambda () "x" (ELambda () "y" $ EVar () "x")) (TEVar $ ETypeVar "b") NotPrincipal of
    Right [CTypeVar (E (ETypeVar "a")) KNat, CMarker, CETypeVar (ETypeVar "b") KStar (MArrow (MEVar (ETypeVar "b-1")) (MEVar (ETypeVar "b-2"))),
           CETypeVar (ETypeVar "b-1") KStar (MEVar (ETypeVar "b-2-2")),
           CETypeVar (ETypeVar "b-2") KStar (MArrow (MEVar (ETypeVar "b-2-1")) (MEVar (ETypeVar "b-2-2"))),
           CTypeVar (E (ETypeVar "b-2-1")) KStar, CTypeVar (E (ETypeVar "b-2-2")) KStar, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

checkExpr_ELambda_test9 :: Test
checkExpr_ELambda_test9 =
  case flip evalStateT startState $ checkExpr context2  (ELambda () "x" $ EVar () "x")
            (TUniversal (UTypeVar "a") KStar (TArrow (TUVar (UTypeVar "a")) (TUVar (UTypeVar "a")))) NotPrincipal of
    Right c -> c == context2
    _ -> False

checkExpr_ELambda_test10 :: Test
checkExpr_ELambda_test10=
  case flip evalStateT startState $ checkExpr context2 (ELambda () "x" (ELambda () "y" $ EVar () "x"))
            (TExistential (UTypeVar "r") KStar (TUVar $ UTypeVar "r")) NotPrincipal of
    Right [CETypeVar (ETypeVar "r") KStar (MArrow (MEVar (ETypeVar "r-1")) (MEVar (ETypeVar "r-2"))),
           CETypeVar (ETypeVar "r-1") KStar (MEVar (ETypeVar "r-2-2")),
           CETypeVar (ETypeVar "r-2") KStar (MArrow (MEVar (ETypeVar "r-2-1")) (MEVar (ETypeVar "r-2-2"))),
           CTypeVar (E (ETypeVar "r-2-1")) KStar, CTypeVar (E (ETypeVar "r-2-2")) KStar,
           CTypeVar (E (ETypeVar "a")) KNat, CMarker, CTypeVar (E (ETypeVar "b")) KStar, CTypeVar (E (ETypeVar "c")) KStar] -> True
    _ -> False

checkExpr_ELambda_test11 :: Test
checkExpr_ELambda_test11 =
  case flip evalStateT startState $ checkExpr context5 (ELambda () "x" $ EVar () "x")
            (TUniversal (UTypeVar "a") KNat (TArrow (TVec (MUVar (UTypeVar "a")) TUnit) (TVec (MUVar (UTypeVar "a")) TUnit))) NotPrincipal of
    Right c -> c == context5
    _ -> False

checkExpr_ELambda_test12 :: Test
checkExpr_ELambda_test12 =
  case flip evalStateT startState $ checkExpr context2 (ELambda () "x" (ELambda () "y" $ EVar () "x"))
            (TExistential (UTypeVar "r") KNat (TUVar $ UTypeVar "r")) NotPrincipal of
    Left (ETypeVarKindMismatchError () (ETypeVar "r") KNat KStar) -> True
    _ -> False

checkExpr_ELambda_test13 :: Test
checkExpr_ELambda_test13 =
  case flip evalStateT startState $ checkExpr context2 (ELambda () "x" (ELambda () "x" $ EVar () "x"))
            (TUniversal (UTypeVar "a") KStar (TArrow (TUVar (UTypeVar "a")) (TArrow (TUVar (UTypeVar "a")) (TUVar (UTypeVar "a"))))) Principal of
    Right c -> c == context2
    _ -> False

checkExpr_ELambda_test14 :: Test
checkExpr_ELambda_test14 =
  case flip evalStateT startState $ checkExpr context2 (ELambda () "x" (ELambda () "x" $ EVar () "x"))
            (TUniversal (UTypeVar "a") KStar (TArrow (TUVar (UTypeVar "a")) (TUVar (UTypeVar "a")))) NotPrincipal of
    Left (TypeInferenceError (ELambda () "x" (EVar () "x"))) -> True
    _ -> False

checkExpr_ECons_test1 :: Test
checkExpr_ECons_test1 =
  case flip evalStateT startState $ checkExpr [CTypeVar (E (ETypeVar "x")) KNat] (ECons () (EInt () 5) (ENil ()))
            (TAnd (TVec (MSucc (MEVar (ETypeVar "x"))) TInt) (MZero, MEVar (ETypeVar "x"))) NotPrincipal of
    Right [CETypeVar (ETypeVar "x") KNat MZero] -> True
    _ -> False

checkExpr_ECons_test2 :: Test
checkExpr_ECons_test2 =
  case flip evalStateT startState $ checkExpr [CTypeVar (E (ETypeVar "x")) KNat]  (ECons () (EInt () 5) (ECons () (EInt () 6) (ENil ())))
            (TAnd (TVec (MSucc (MEVar (ETypeVar "x"))) TInt) (MZero, MEVar (ETypeVar "x"))) Principal of
    Left (EquationFalseError () MZero (MSucc (MEVar (ETypeVar "#1"))) KNat) -> True
    _ -> False

checkExpr_EConstr_test1 :: Test
checkExpr_EConstr_test1 =
  case flip evalStateT startState $ checkExpr [] (EConstr () "Simba" [EInt () 44, EBool () True])
            (TGADT "Terminator" [ParameterType TInt, ParameterType TBool]) NotPrincipal of
    Left (MismatchedConstructorError (EConstr () "Simba" [EInt () 44, EBool () True]) "Lion" "Terminator") -> True
    _ -> False

checkExpr_EConstr_test2 :: Test
checkExpr_EConstr_test2 =
  case flip evalStateT startState $ checkExpr [] (EConstr () "Simba" [EInt () 44, EBool () True])
            (TGADT "Lion" [ParameterType (TAnd (TVec (MSucc (MEVar (ETypeVar "x"))) TInt) (MZero, MEVar (ETypeVar "x")))]) NotPrincipal of
    Right [] -> True
    _ -> False

checkExpr_EConstr_test3 :: Test
checkExpr_EConstr_test3 =
  case flip evalStateT startState $ checkExpr [] (EConstr () "Simba" [EInt () 44, EBool () True, EUnit ()])
            (TGADT "Lion" [ParameterType (TAnd (TVec (MSucc (MEVar (ETypeVar "x"))) TInt) (MZero, MEVar (ETypeVar "x")))]) NotPrincipal of
    Left (MismatchedConstructorArityError (EConstr () "Simba" [EInt () 44, EBool () True, EUnit ()]) 2 3) -> True
    _ -> False

checkExpr_EConstr_test4 :: Test
checkExpr_EConstr_test4 =
  case flip evalStateT startState $ checkExpr context1 (EConstr () "TX" [])
            (TGADT "Terminator" [ParameterType (TAnd (TVec (MSucc (MEVar (ETypeVar "x"))) TInt) (MZero, MEVar (ETypeVar "x"))),
            ParameterType TInt]) Principal of
    Right c -> c == context1
    _ -> False

checkExpr_EConstr_test5 :: Test
checkExpr_EConstr_test5 =
  case flip evalStateT startState $ checkExpr [] (EConstr () "TX" [EInt () 44, EBool () True, EUnit ()])
            (TGADT "Terminator" [ParameterType (TAnd (TVec (MSucc (MEVar (ETypeVar "x"))) TInt) (MZero, MEVar (ETypeVar "x"))),
            ParameterType TInt]) NotPrincipal of
    Left (MismatchedConstructorArityError (EConstr () "TX" [EInt () 44, EBool () True, EUnit ()]) 0 3) -> True
    _ -> False

checkExpr_EConstr_test6 :: Test
checkExpr_EConstr_test6 =
  case flip evalStateT startState $ checkExpr [CTypeVar (E (ETypeVar "x")) KNat]
            (EConstr () "T1000" [EString () "Konrad", ECons () (EInt () 5) (ENil ()), EInt () 6])
            (TGADT "Terminator" [ParameterType (TAnd (TVec (MSucc (MEVar (ETypeVar "x"))) TInt) (MZero, MEVar (ETypeVar "x"))),
            ParameterType TInt]) Principal of
    Right [CETypeVar (ETypeVar "x") KNat MZero] -> True
    _ -> False

checkExpr_EConstr_test7 :: Test
checkExpr_EConstr_test7 =
  case flip evalStateT startState $ checkExpr [CTypeVar (E (ETypeVar "x")) KNat]
            (EConstr () "T1000" [EString () "Konrad", ECons () (EInt () 5) (ENil ()), EUnit ()])
            (TGADT "Terminator" [ParameterType (TAnd (TVec (MSucc (MEVar (ETypeVar "x"))) TInt) (MZero, MEVar (ETypeVar "x"))),
            ParameterType TInt]) Principal of
    Left (TypeInferenceError (EUnit ())) -> True
    _ -> False

checkExpr_EConstr_test8 :: Test
checkExpr_EConstr_test8 =
  case flip evalStateT startState $ checkExpr [CTypeVar (E (ETypeVar "x")) KNat]
            (EConstr () "T1000" [EFloat () 3.14, ECons () (EInt () 5) (ENil ()), EUnit ()])
            (TGADT "Terminator" [ParameterType (TAnd (TVec (MSucc (MEVar (ETypeVar "x"))) TUnit) (MZero, MEVar (ETypeVar "x"))),
            ParameterType TInt]) Principal of
    Left (TypeInferenceError (EFloat () 3.14)) -> True
    _ -> False

checkExpr_EConstr_test9 :: Test
checkExpr_EConstr_test9 =
  case flip evalStateT startState $ checkExpr [CTypeVar (E (ETypeVar "x")) KNat]
            (EConstr () "T1000" [EString () "Konrad", ENil (), EInt () 6])
            (TGADT "Terminator" [ParameterType (TAnd (TVec (MSucc (MEVar (ETypeVar "x"))) TInt) (MZero, MEVar (ETypeVar "x"))),
            ParameterType TInt]) Principal of
    Left (EquationFalseError () (MSucc MZero) MZero KNat) -> True
    _ -> False

checkExpr_EConstr_test10 :: Test
checkExpr_EConstr_test10 =
  case flip evalStateT startState $ checkExpr [CTypeVar (E (ETypeVar "x")) KNat]
            (EConstr () "T1000" [EString () "Konrad", ECons () (EInt () 5) (ECons () (EInt () 5) (ENil ())), EInt () 6])
            (TGADT "Terminator" [ParameterType (TAnd (TVec (MSucc (MEVar (ETypeVar "x"))) TInt) (MZero, MEVar (ETypeVar "x"))),
            ParameterType TInt]) Principal of
    Left (EquationFalseError () MZero (MSucc (MEVar (ETypeVar "#1"))) KNat) -> True
    _ -> False

checkExpr_EConstr_test11 :: Test
checkExpr_EConstr_test11 =
  case flip evalStateT startState $ checkExpr []
            (EConstr () "T800" [EInt () 5, ECons () (EInt () 5) (ECons () (EInt () 5) (ENil ())), EBool () True])
            (TGADT "Terminator" [ParameterMonotype (MSucc . MSucc . MSucc $ MZero), ParameterType TInt]) Principal of
    Right [] -> True
    _ -> False

checkExpr_EConstr_test12 :: Test
checkExpr_EConstr_test12 =
  case flip evalStateT startState $ checkExpr []
            (EConstr () "T800" [EInt () 5, ECons () (EBool () True) (ECons () (EBool () True) (ENil ())), EBool () True])
            (TGADT "Terminator" [ParameterMonotype (MSucc MZero), ParameterType TBool]) Principal of
    Left (EquationFalseError () MInt MBool KStar) -> True
    _ -> False

--inferExpr :: Context -> Expr p -> Either (Error p) (Type, Principality, Context)
inferExpr_EVar_test1 :: Test
inferExpr_EVar_test1 =
  case flip evalStateT startState $ inferExpr context1 (EVar () "r") of
    Right (TProduct [TUnit, TUnit] 2, NotPrincipal, c) -> c == context1
    _ -> False

inferExpr_EVar_test2 :: Test
inferExpr_EVar_test2 =
  case flip evalStateT startState $ inferExpr context1 (EVar () "x") of
    Right (TUnit, Principal, c) -> c == context1
    _ -> False

inferExpr_EVar_test3 :: Test
inferExpr_EVar_test3 =
  case flip evalStateT startState $ inferExpr context5 (EVar () "x") of
    Left (MonotypeIsNotTypeError () MZero) -> True
    _ -> False

inferExpr_EVar_test4 :: Test
inferExpr_EVar_test4 =
  case flip evalStateT startState $ inferExpr context5 (EVar () "y") of
    Left (UndeclaredVariableError () "y") -> True
    _ -> False

inferExpr_EVar_test5 :: Test
inferExpr_EVar_test5 =
  case flip evalStateT startState $ inferExpr context4 (EVar () "zz") of
    Left (UndeclaredETypeVarError () (ETypeVar "r")) -> True
    _ -> False

inferExpr_EVar_test6 :: Test
inferExpr_EVar_test6 =
  case flip evalStateT startState $ inferExpr [CVar "zz" (TUVar $ UTypeVar "v") Principal] (EVar () "zz") of
    Right (TUVar (UTypeVar "v"), Principal, c)  -> c == [CVar "zz" (TUVar $ UTypeVar "v") Principal]
    _ -> False

inferExpr_EVar_test7 :: Test
inferExpr_EVar_test7 =
  case flip evalStateT startState $ inferExpr
            [CVar "zz" (TUVar $ UTypeVar "v") Principal, CUTypeVarEq (UTypeVar "v") (MGADT "A" [MUnit, MUnit])] (EVar () "zz") of
    Right (TGADT "A" [ParameterMonotype MUnit, ParameterMonotype MUnit], Principal, c)  ->
          c == [CVar "zz" (TUVar $ UTypeVar "v") Principal, CUTypeVarEq (UTypeVar "v") (MGADT "A" [MUnit, MUnit])]
    _ -> False

inferExpr_EVar_test8 :: Test
inferExpr_EVar_test8 =
  case flip evalStateT startState $ inferExpr [] (EVar () "zz") of
    Left (UndeclaredVariableError () "zz") -> True
    _ -> False

inferExpr_EAnnot_test1 :: Test
inferExpr_EAnnot_test1 =
  case flip evalStateT startState $ inferExpr context2 (EAnnot () (ELambda () "x" $ EVar () "x")
            (TUniversal (UTypeVar "a") KStar (TArrow (TUVar (UTypeVar "a")) (TUVar (UTypeVar "a"))))) of
    Right (TUniversal (UTypeVar "a") KStar (TArrow (TUVar (UTypeVar "a")) (TUVar (UTypeVar "a"))), Principal, c)   -> c == context2
    _ -> False

inferExpr_EAnnot_test2 :: Test
inferExpr_EAnnot_test2 =
  case flip evalStateT startState $ inferExpr context2 (EAnnot () (ELambda () "x" $ EVar () "x")
            (TUniversal (UTypeVar "a") KNat (TArrow (TUVar (UTypeVar "a")) (TUVar (UTypeVar "a"))))) of
    Left (TypeHasWrongKindError () (TUVar (UTypeVar "a")) KStar KNat) -> True
    _ -> False

inferExpr_EAnnot_test3 :: Test
inferExpr_EAnnot_test3 =
  case flip evalStateT startState $ inferExpr context5 (EAnnot () (ETuple () [ETuple () [EInt () 44, EFloat () 3.14] 2, EChar () 'c'] 2)
                          (TProduct [TProduct [TInt, TFloat] 2, TChar] 2)) of
    Right (TProduct [TProduct [TInt, TFloat] 2, TChar] 2, Principal, c) -> c == context5
    _ -> False

inferExpr_EAnnot_test4 :: Test
inferExpr_EAnnot_test4 =
  case flip evalStateT startState $ inferExpr
            [CTypeVar (E $ ETypeVar "x") KStar]  (EAnnot () (ETuple () [ETuple () [EUnit (), EUnit ()] 2, EUnit ()] 2) (TEVar $ ETypeVar "x")) of
    Left (TypeFormednessPrcFEVError () [ETypeVar "x"]) -> True
    _ -> False

inferExpr_EAnnot_test5 :: Test
inferExpr_EAnnot_test5 =
  case flip evalStateT startState $ inferExpr
            [] (EAnnot () (ETuple () [ETuple () [EUnit (), EUnit ()] 2, EUnit ()] 2)
            (TExistential (UTypeVar "x") KStar (TUVar $ UTypeVar "x"))) of
    Right (TExistential (UTypeVar "x") KStar (TUVar (UTypeVar "x")), Principal, c) -> c ==
                    [CETypeVar (ETypeVar "x") KStar (MProduct [MEVar (ETypeVar "x-1"), MEVar (ETypeVar "x-2")] 2),
                     CETypeVar (ETypeVar "x-1") KStar (MProduct [MEVar (ETypeVar "x-1-1"), MEVar (ETypeVar "x-1-2")] 2),
                     CETypeVar (ETypeVar "x-1-1") KStar MUnit, CETypeVar (ETypeVar "x-1-2") KStar MUnit, CETypeVar (ETypeVar "x-2") KStar MUnit]
    _ -> False

inferExpr_EAnnot_test6 :: Test
inferExpr_EAnnot_test6 =
  case flip evalStateT startState $ inferExpr [] (EAnnot () (ENil ()) (TVec MZero TInt)) of
    Right (TVec MZero TInt, Principal, []) -> True
    _ -> False

inferExpr_EAnnot_test7 :: Test
inferExpr_EAnnot_test7 =
  case flip evalStateT startState $ inferExpr [] (EAnnot () (ECons () (EInt () 5)(ENil ())) (TVec (MSucc MZero) TInt)) of
    Right (TVec (MSucc MZero) TInt, Principal, []) -> True
    _ -> False

inferExpr_EAnnot_test8 :: Test
inferExpr_EAnnot_test8 =
  case flip evalStateT startState $ inferExpr [CUTypeVarEq (UTypeVar "r") MZero, CTypeVar (U (UTypeVar "r")) KNat]
            (EAnnot () (ENil ()) (TVec (MUVar $ UTypeVar "r") TInt)) of
    Right (TVec MZero TInt, Principal, [CUTypeVarEq (UTypeVar "r") MZero, CTypeVar (U (UTypeVar "r")) KNat]) -> True
    _ -> False

inferExpr_EAnnot_test9 :: Test
inferExpr_EAnnot_test9 =
  case flip evalStateT startState $ inferExpr [] (EAnnot () (ENil ())
            (TUniversal (UTypeVar "r") KNat (TImp (MZero, MUVar (UTypeVar "r")) (TVec (MUVar $ UTypeVar "r") TInt)))) of
    Right (TUniversal (UTypeVar "r") KNat (TImp (MZero, MUVar (UTypeVar "r")) (TVec (MUVar (UTypeVar "r")) TInt)), Principal, []) -> True
    _ -> False

inferExpr_EAnnot_test10 :: Test
inferExpr_EAnnot_test10 =
  case flip evalStateT startState $ inferExpr [] (EAnnot () (ENil ()) (TVec (MSucc MZero) TInt)) of
    Left (EquationFalseError () (MSucc MZero) MZero KNat) -> True
    _ -> False

inferExpr_EAnnot_test11 :: Test
inferExpr_EAnnot_test11 =
  case flip evalStateT startState $ inferExpr [] (EAnnot () (ECons () (EInt () 5) (ENil ())) (TVec (MSucc MZero) TInt)) of
    Right (TVec (MSucc MZero) TInt, Principal, []) -> True
    _ -> False

inferExpr_EAnnot_test12 :: Test
inferExpr_EAnnot_test12 =
  case flip evalStateT startState $ inferExpr [] (EAnnot () (EInt () 5) (TImp (MSucc MZero, MZero) TBool)) of
    Right (TImp (MSucc MZero, MZero) TBool, Principal, []) -> True
    _ -> False

-- checkBranch ::
--   Context -> Branch p -> [Type] -> Principality -> Type -> Principality
--   -> StateT TypecheckerState (Either (Error p)) Context
checkBranch_test1 :: Test
checkBranch_test1 =
  case flip evalStateT startState $ checkBranch [] ([PTuple () [PUnit (), PInt () 5, PFloat () 3.14] 3], EInt () 5, ())
        [TProduct [TUnit, TInt, TFloat] 3] Principal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test2 :: Test
checkBranch_test2 =
  case flip evalStateT startState $ checkBranch [] ([PTuple () [PChar () 'k', PBool () True] 2, PString () "Bestrafer"], EInt () 5, ())
        [TProduct [TChar, TBool] 2, TString] NotPrincipal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test3 :: Test
checkBranch_test3 =
  case flip evalStateT startState $ checkBranch [] ([PTuple () [PUnit (), PFloat () 5, PFloat () 3.14] 3], EInt () 5, ())
        [TProduct [TUnit, TInt, TFloat] 3] Principal TInt Principal of
    Left (PatternMatchingTypecheckingError (PFloat () 5) TInt) -> True
    _ -> False

checkBranch_test4 :: Test
checkBranch_test4 =
  case flip evalStateT startState $ checkBranch [] ([PTuple () [PChar () 'k', PBool () True] 2, PChar () 'B'], EInt () 5, ())
        [TProduct [TChar, TBool] 2, TString] NotPrincipal TInt Principal of
    Left (PatternMatchingTypecheckingError (PChar () 'B') TString) -> True
    _ -> False

checkBranch_test5 :: Test
checkBranch_test5 =
  case flip evalStateT startState $ checkBranch [] ([PTuple () [PUnit (), PInt () 5, PFloat () 3.14] 3], EInt () 5, ())
        [TProduct [TUnit, TInt, TFloat] 3, TString] Principal TInt Principal of
    Left (TooShortPatternError ()) -> True
    _ -> False

checkBranch_test6 :: Test
checkBranch_test6 =
  case flip evalStateT startState $ checkBranch [] ([PTuple () [PChar () 'k', PBool () True] 2, PString () "Bestrafer"], EInt () 5, ())
        [TProduct [TChar, TBool] 2] NotPrincipal TInt Principal of
    Left (TooLongPatternError ()) -> True
    _ -> False

checkBranch_test7 :: Test
checkBranch_test7 =
  case flip evalStateT startState $ checkBranch [] ([PTuple () [PUnit (), PInt () 5, PWild ()] 3], EInt () 5, ())
        [TProduct [TUnit, TInt, TFloat] 3] Principal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test8 :: Test
checkBranch_test8 =
  case flip evalStateT startState $ checkBranch [] ([PTuple () [PChar () 'k', PBool () True] 2, PVar () "Bestrafer"], EInt () 5, ())
        [TProduct [TChar, TBool] 2, TString] NotPrincipal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test9 :: Test
checkBranch_test9 =
  case flip evalStateT startState $ checkBranch [] ([PTuple () [PUnit (), PInt () 5, PWild ()] 3], EInt () 5, ())
        [TAnd (TProduct [TUnit, TInt, TFloat] 3) (MZero, MZero)] Principal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test10 :: Test
checkBranch_test10 =
  case flip evalStateT startState $ checkBranch [] ([PTuple () [PChar () 'k', PBool () True] 2, PVar () "Bestrafer"], EInt () 5, ())
        [TExistential (UTypeVar "R") KNat $ TProduct [TChar, TBool] 2, TString] NotPrincipal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test11 :: Test
checkBranch_test11 =
  case flip evalStateT startState $ checkBranch [] ([PWild ()], EInt () 5, ())
        [TAnd (TProduct [TUnit, TInt, TFloat] 3) (MZero, MZero)] Principal TInt Principal of
    Left (VarPatternHeadedByExistsOrAndError (PWild ()) (TAnd (TProduct [TUnit, TInt, TFloat] 3) (MZero, MZero))) -> True
    _ -> False

checkBranch_test12 :: Test
checkBranch_test12 =
  case flip evalStateT startState $ checkBranch [] ([PVar () "Bestrafer"], EInt () 5, ())
        [TExistential (UTypeVar "R") KNat $ TProduct [TChar, TBool] 2, TString] NotPrincipal TInt Principal of
    Left (VarPatternHeadedByExistsOrAndError (PVar () "Bestrafer") (TExistential (UTypeVar "R") KNat (TProduct [TChar, TBool] 2))) -> True
    _ -> False

checkBranch_test13 :: Test
checkBranch_test13 =
  case flip evalStateT startState $ checkBranch [] ([PWild ()], EInt () 5, ())
        [TProduct [TUnit, TInt, TFloat] 3] Principal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test14 :: Test
checkBranch_test14 =
  case flip evalStateT startState $ checkBranch [] ([PVar () "Bestrafer"], EInt () 5, ())
        [TProduct [TChar, TBool] 2, TString] NotPrincipal TInt Principal of
    Left (TooShortPatternError ()) -> True
    _ -> False

checkBranch_test15 :: Test
checkBranch_test15 =
  case flip evalStateT startState $ checkBranch [] ([PCons () (PInt () 5) (PWild ())], EInt () 5, ())
        [TVec (MSucc . MSucc . MSucc $ MZero) TInt] Principal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test16 :: Test
checkBranch_test16 =
  case flip evalStateT startState $ checkBranch [] ([PCons () (PInt () 5) (PNil ())], EInt () 5, ())
        [TVec (MSucc MZero) TInt] Principal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test17 :: Test
checkBranch_test17 =
  case flip evalStateT startState $ checkBranch [] ([PCons () (PInt () 5) (PWild ())], EInt () 5, ())
        [TVec MZero TInt] Principal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test18 :: Test
checkBranch_test18 =
  case flip evalStateT startState $ checkBranch [] ([PCons () (PInt () 5) (PNil ())], EInt () 5, ())
        [TVec (MSucc (MSucc MZero)) TInt] Principal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test19 :: Test
checkBranch_test19 =
  case flip evalStateT startState $ checkBranch [] ([PConstr () "LCons" [PInt () 5, PWild ()]], EInt () 5, ())
        [TGADT "List" [ParameterType TInt]] Principal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test20 :: Test
checkBranch_test20 =
  case flip evalStateT startState $ checkBranch [] ([PConstr () "LCons" [PInt () 5, PConstr () "LNil" []]], EInt () 5, ())
        [TGADT "List" [ParameterType TInt]] Principal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test21 :: Test
checkBranch_test21 =
  case flip evalStateT startState $ checkBranch [] ([PConstr () "Cons" [PInt () 5, PWild ()]], EInt () 5, ())
        [TGADT "Vec" [ParameterMonotype . MSucc . MSucc . MSucc $ MZero , ParameterType TInt]] Principal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test22 :: Test
checkBranch_test22 =
  case flip evalStateT startState $ checkBranch [] ([PConstr () "Cons" [PInt () 5, PConstr () "Nil" []]], EInt () 5, ())
        [TGADT "Vec" [ParameterMonotype . MSucc $ MZero, ParameterType TInt]] Principal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test23 :: Test
checkBranch_test23 =
  case flip evalStateT startState $ checkBranch [] ([PConstr () "Cons" [PInt () 5, PWild ()]], EInt () 5, ())
        [TGADT "Vec" [ParameterMonotype MZero , ParameterType TInt]] Principal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test24 :: Test
checkBranch_test24 =
  case flip evalStateT startState $ checkBranch [] ([PConstr () "Cons" [PInt () 5, PConstr () "Nil" []]], EInt () 5, ())
        [TGADT "Vec" [ParameterMonotype . MSucc . MSucc $ MZero, ParameterType TInt]] Principal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test25 :: Test
checkBranch_test25 =
  case flip evalStateT startState $ checkBranch [] ([PCons () (PInt () 5) (PWild ())], EInt () 5, ())
        [TVec MZero TInt] NotPrincipal TInt NotPrincipal of
    Right [] -> True
    _ -> False

checkBranch_test26 :: Test
checkBranch_test26 =
  case flip evalStateT startState $ checkBranch [] ([PConstr () "LCons" [PInt () 5, PConstr () "LNil" []]], EInt () 5, ())
        [TGADT "List" [ParameterType TInt]] NotPrincipal TInt NotPrincipal of
    Right [] -> True
    _ -> False

checkBranch_test27 :: Test
checkBranch_test27 =
  case flip evalStateT startState $ checkBranch [] ([PConstr () "Cons" [PInt () 5, PConstr () "Nil" []]], EInt () 5, ())
        [TGADT "Vec" [ParameterMonotype . MSucc . MSucc $ MZero, ParameterType TInt]] NotPrincipal TInt NotPrincipal of
    Right [] -> True
    _ -> False

checkBranch_test28 :: Test
checkBranch_test28 =
  case flip evalStateT startState $ checkBranch [] ([PConstr () "Cons" [PInt () 5, PWild ()]], EInt () 5, ())
        [TExistential (UTypeVar "R") KStar $ TAnd (TGADT "Vec"
        [ParameterMonotype . MSucc $ MZero, ParameterType . TUVar $ UTypeVar "R"])
        (MUVar $ UTypeVar "R", MInt)] Principal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test29 :: Test
checkBranch_test29 =
  case flip evalStateT startState $ checkBranch [] ([PConstr () "Cons" [PInt () 5, PConstr () "Nil" []]], EInt () 5, ())
        [TExistential (UTypeVar "R") KNat $ TGADT "Vec"
        [ParameterMonotype . MUVar $ UTypeVar "R", ParameterType TInt]] Principal TInt Principal of
    Right [] -> True
    _ -> False

checkBranch_test30 :: Test
checkBranch_test30 =
  case flip evalStateT startState $ checkBranch [] ([PConstr () "Cons" [PInt () 5, PWild ()]], EInt () 5, ())
        [TExistential (UTypeVar "R") KStar $ TGADT "Vec"
        [ParameterMonotype . MSucc $ MZero, ParameterType . TUVar $ UTypeVar "R"]] Principal TInt Principal of
    Left (PatternMatchingTypecheckingError (PInt () 5) (TUVar (UTypeVar "R"))) -> True
    _ -> False

tests :: [(TestName, Test)]
tests = [("typeFromTemplate_test1", typeFromTemplate_test1),
         ("typeFromTemplate_test2", typeFromTemplate_test2),
         ("typeFromTemplate_test3", typeFromTemplate_test3),
         ("typeFromTemplate_test4", typeFromTemplate_test4),
         ("typeFromTemplate_test5", typeFromTemplate_test5),
         ("typeFromTemplate_test6", typeFromTemplate_test6),
         ("freeExistentialVariablesOfMonotype_test1", freeExistentialVariablesOfMonotype_test1),
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
         ("freeVariablesOfMonotype_test1", freeVariablesOfMonotype_test1),
         ("freeVariablesOfMonotype_test2", freeVariablesOfMonotype_test2),
         ("freeVariablesOfMonotype_test3", freeVariablesOfMonotype_test3),
         ("freeVariablesOfMonotype_test4", freeVariablesOfMonotype_test4),
         ("freeVariablesOfMonotype_test5", freeVariablesOfMonotype_test5),
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
         ("typeVarContextLookup_test1", typeVarContextLookup_test1),
         ("typeVarContextLookup_test2", typeVarContextLookup_test2),
         ("typeVarContextLookup_test3", typeVarContextLookup_test3),
         ("typeVarContextLookup_test4", typeVarContextLookup_test4),
         ("typeVarContextLookup_test5", typeVarContextLookup_test5),
         ("typeVarContextLookup_test6", typeVarContextLookup_test6),
         ("typeVarContextLookup_test7", typeVarContextLookup_test7),
         ("typeVarContextLookup_test8", typeVarContextLookup_test8),
         ("typeVarContextLookup_test9", typeVarContextLookup_test9),
         ("typeVarContextLookup_test10", typeVarContextLookup_test10),
         ("typeVarContextLookup_test11", typeVarContextLookup_test11),
         ("typeVarContextLookup_test12", typeVarContextLookup_test12),
         ("typeVarContextLookup_test13", typeVarContextLookup_test13),
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
         ("eTypeVarContextReplace_test12", eTypeVarContextReplace_test12),
         ("eTypeVarContextReplace_test13", eTypeVarContextReplace_test13),
         ("eTypeVarContextReplace_test14", eTypeVarContextReplace_test14),
         ("eTypeVarContextReplace_test15", eTypeVarContextReplace_test15),
         ("dropContextToMarker_test1", dropContextToMarker_test1),
         ("dropContextToMarker_test2", dropContextToMarker_test2),
         ("dropContextToMarker_test3", dropContextToMarker_test3),
         ("dropContextToMarker_test4", dropContextToMarker_test4),
         ("dropContextToMarker_test5", dropContextToMarker_test5),
         ("dropContextToETypeVar_test1", dropContextToETypeVar_test1),
         ("dropContextToETypeVar_test2", dropContextToETypeVar_test2),
         ("dropContextToETypeVar_test3", dropContextToETypeVar_test3),
         ("dropContextToETypeVar_test4", dropContextToETypeVar_test4),
         ("dropContextToETypeVar_test5", dropContextToETypeVar_test5),
         ("dropContextToETypeVar_test6", dropContextToETypeVar_test6),
         ("takeContextToETypeVar_test1", takeContextToETypeVar_test1),
         ("takeContextToETypeVar_test2", takeContextToETypeVar_test2),
         ("takeContextToETypeVar_test3", takeContextToETypeVar_test3),
         ("takeContextToETypeVar_test4", takeContextToETypeVar_test4),
         ("takeContextToETypeVar_test5", takeContextToETypeVar_test5),
         ("takeContextToUTypeVar_test1", takeContextToUTypeVar_test1),
         ("takeContextToUTypeVar_test2", takeContextToUTypeVar_test2),
         ("takeContextToUTypeVar_test3", takeContextToUTypeVar_test3),
         ("takeContextToUTypeVar_test4", takeContextToUTypeVar_test4),
         ("takeContextToUTypeVar_test5", takeContextToUTypeVar_test5),
         ("substituteUVarInMonotype_test1", substituteUVarInMonotype_test1),
         ("substituteUVarInMonotype_test2", substituteUVarInMonotype_test2),
         ("substituteUVarInMonotype_test3", substituteUVarInMonotype_test3),
         ("substituteUVarInMonotype_test4", substituteUVarInMonotype_test4),
         ("substituteUVarInMonotype_test5", substituteUVarInMonotype_test5),
         ("substituteUVarInMonotype_test6", substituteUVarInMonotype_test6),
         ("substituteUVarInMonotype_test7", substituteUVarInMonotype_test7),
         ("substituteUVarInMonotype_test8", substituteUVarInMonotype_test8),
         ("substituteUVarInMonotype_test9", substituteUVarInMonotype_test9),
         ("substituteUVarInMonotype_test10", substituteUVarInMonotype_test10),
         ("substituteUVarInMonotype_test11", substituteUVarInMonotype_test11),
         ("substituteUVarInMonotype_test12", substituteUVarInMonotype_test12),
         ("substituteUVarInProp_test1", substituteUVarInProp_test1),
         ("substituteUVarInProp_test2", substituteUVarInProp_test2),
         ("substituteUVarInProp_test3", substituteUVarInProp_test3),
         ("substituteUVarInProp_test4", substituteUVarInProp_test4),
         ("substituteUVarInProp_test5", substituteUVarInProp_test5),
         ("substituteUVarInProp_test6", substituteUVarInProp_test6),
         ("substituteUVarInProp_test7", substituteUVarInProp_test7),
         ("substituteUVarInProp_test8", substituteUVarInProp_test8),
         ("substituteUVarInType_test1", substituteUVarInType_test1),
         ("substituteUVarInType_test2", substituteUVarInType_test2),
         ("substituteUVarInType_test3", substituteUVarInType_test3),
         ("substituteUVarInType_test4", substituteUVarInType_test4),
         ("substituteUVarInType_test5", substituteUVarInType_test5),
         ("substituteUVarInType_test6", substituteUVarInType_test6),
         ("substituteUVarInType_test7", substituteUVarInType_test7),
         ("substituteUVarInType_test8", substituteUVarInType_test8),
         ("substituteUVarInType_test9", substituteUVarInType_test9),
         ("substituteUVarInType_test10", substituteUVarInType_test10),
         ("substituteUVarInType_test11", substituteUVarInType_test11),
         ("substituteUVarInType_test12", substituteUVarInType_test12),
         ("substituteUVarInType_test13", substituteUVarInType_test13),
         ("substituteUVarInType_test14", substituteUVarInType_test14),
         ("substituteUVarInType_test15", substituteUVarInType_test15),
         ("substituteUVarInType_test16", substituteUVarInType_test16),
         ("substituteUVarInType_test17", substituteUVarInType_test17),
         ("substituteUVarInType_test18", substituteUVarInType_test18),
         ("substituteUVarInType_test19", substituteUVarInType_test19),
         ("substituteUVarInType_test20", substituteUVarInType_test20),
         ("substituteUVarInType_test21", substituteUVarInType_test21),
         ("substituteUVarInType_test22", substituteUVarInType_test22),
         ("substituteUVarInType_test23", substituteUVarInType_test23),
         ("substituteUVarInType_test24", substituteUVarInType_test24),
         ("substituteUVarInType_test25", substituteUVarInType_test25),
         ("substituteUVarInType_test26", substituteUVarInType_test26),
         ("monotypeToType_test1", monotypeToType_test1),
         ("monotypeToType_test2", monotypeToType_test2),
         ("monotypeToType_test3", monotypeToType_test3),
         ("typeToMonotype_test1", typeToMonotype_test1),
         ("typeToMonotype_test2", typeToMonotype_test2),
         ("typeToMonotype_test3", typeToMonotype_test3),
         ("typeToMonotype_test4", typeToMonotype_test4),
         ("typeToMonotype_test5", typeToMonotype_test5),
         ("typeToMonotype_test6", typeToMonotype_test6),
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
         ("inferMonotypeKind_test9", inferMonotypeKind_test9),
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
         ("instantiateEVar_test1", instantiateEVar_test1),
         ("instantiateEVar_test2", instantiateEVar_test2),
         ("instantiateEVar_test3", instantiateEVar_test3),
         ("instantiateEVar_test4", instantiateEVar_test4),
         ("instantiateEVar_test5", instantiateEVar_test5),
         ("instantiateEVar_test6", instantiateEVar_test6),
         ("instantiateEVar_test7", instantiateEVar_test7),
         ("instantiateEVar_test8", instantiateEVar_test8),
         ("instantiateEVar_test9", instantiateEVar_test9),
         ("instantiateEVar_test10", instantiateEVar_test10),
         ("instantiateEVar_test11", instantiateEVar_test11),
         ("instantiateEVar_test12", instantiateEVar_test12),
         ("instantiateEVar_test13", instantiateEVar_test13),
         ("instantiateEVar_test14", instantiateEVar_test14),
         ("instantiateEVar_test15", instantiateEVar_test15),
         ("instantiateEVar_test16", instantiateEVar_test16),
         ("instantiateEVar_test17", instantiateEVar_test17),
         ("instantiateEVar_test18", instantiateEVar_test18),
         ("instantiateEVar_test19", instantiateEVar_test19),
         ("instantiateEVar_test20", instantiateEVar_test20),
         ("instantiateEVar_test21", instantiateEVar_test21),
         ("instantiateEVar_test22", instantiateEVar_test22),
         ("instantiateEVar_test23", instantiateEVar_test23),
         ("instantiateEVar_test24", instantiateEVar_test24),
         ("instantiateEVar_test25", instantiateEVar_test25),
         ("instantiateEVar_test26", instantiateEVar_test26),
         ("checkEquation_test1", checkEquation_test1),
         ("checkEquation_test2", checkEquation_test2),
         ("checkEquation_test3", checkEquation_test3),
         ("checkEquation_test4", checkEquation_test4),
         ("checkEquation_test5", checkEquation_test5),
         ("checkEquation_test6", checkEquation_test6),
         ("checkEquation_test7", checkEquation_test7),
         ("checkEquation_test8", checkEquation_test8),
         ("checkEquation_test9", checkEquation_test9),
         ("checkEquation_test10", checkEquation_test10),
         ("checkEquation_test11", checkEquation_test11),
         ("checkEquation_test12", checkEquation_test12),
         ("checkEquation_test13", checkEquation_test13),
         ("checkEquation_test14", checkEquation_test14),
         ("checkEquation_test15", checkEquation_test15),
         ("checkEquation_test16", checkEquation_test16),
         ("checkEquation_test17", checkEquation_test17),
         ("checkEquation_test18", checkEquation_test18),
         ("checkEquation_test19", checkEquation_test19),
         ("checkEquation_test20", checkEquation_test20),
         ("checkEquation_test21", checkEquation_test21),
         ("checkEquation_test22", checkEquation_test22),
         ("checkEquation_test23", checkEquation_test23),
         ("checkEquation_test24", checkEquation_test24),
         ("equivalentProp_test1", equivalentProp_test1),
         ("equivalentProp_test2", equivalentProp_test2),
         ("equivalentProp_test3", equivalentProp_test3),
         ("equivalentProp_test4", equivalentProp_test4),
         ("equivalentProp_test5", equivalentProp_test5),
         ("equivalentProp_test6", equivalentProp_test6),
         ("equivalentProp_test7", equivalentProp_test7),
         ("equivalentProp_test8", equivalentProp_test8),
         ("equivalentProp_test9", equivalentProp_test9),
         ("equivalentProp_test10", equivalentProp_test10),
         ("equivalentType_test1", equivalentType_test1),
         ("equivalentType_test2", equivalentType_test2),
         ("equivalentType_test3", equivalentType_test3),
         ("equivalentType_test4", equivalentType_test4),
         ("equivalentType_test5", equivalentType_test5),
         ("equivalentType_test6", equivalentType_test6),
         ("equivalentType_test7", equivalentType_test7),
         ("equivalentType_test8", equivalentType_test8),
         ("equivalentType_test9", equivalentType_test9),
         ("equivalentType_test10", equivalentType_test10),
         ("equivalentType_test11", equivalentType_test11),
         ("equivalentType_test12", equivalentType_test12),
         ("equivalentType_test13", equivalentType_test13),
         ("equivalentType_test14", equivalentType_test14),
         ("equivalentType_test15", equivalentType_test15),
         ("equivalentType_test16", equivalentType_test16),
         ("equivalentType_test17", equivalentType_test17),
         ("equivalentType_test18", equivalentType_test18),
         ("equivalentType_test19", equivalentType_test19),
         ("equivalentType_test20", equivalentType_test20),
         ("equivalentType_test21", equivalentType_test21),
         ("equivalentType_test22", equivalentType_test22),
         ("equivalentType_test23", equivalentType_test23),
         ("equivalentType_test24", equivalentType_test24),
         ("equivalentType_test25", equivalentType_test25),
         ("equivalentType_test26", equivalentType_test26),
         ("equivalentType_test27", equivalentType_test27),
         ("subtype_test1", subtype_test1),
         ("subtype_test2", subtype_test2),
         ("subtype_test3", subtype_test3),
         ("subtype_test4", subtype_test4),
         ("subtype_test5", subtype_test5),
         ("subtype_test6", subtype_test6),
         ("subtype_test7", subtype_test7),
         ("subtype_test8", subtype_test8),
         ("subtype_test9", subtype_test9),
         ("subtype_test10", subtype_test10),
         ("subtype_test11", subtype_test11),
         ("subtype_test12", subtype_test12),
         ("subtype_test13", subtype_test13),
         ("subtype_test14", subtype_test14),
         ("eliminateEquation_test1", eliminateEquation_test1),
         ("eliminateEquation_test2", eliminateEquation_test2),
         ("eliminateEquation_test3", eliminateEquation_test3),
         ("eliminateEquation_test4", eliminateEquation_test4),
         ("eliminateEquation_test5", eliminateEquation_test5),
         ("eliminateEquation_test6", eliminateEquation_test6),
         ("eliminateEquation_test7", eliminateEquation_test7),
         ("eliminateEquation_test8", eliminateEquation_test8),
         ("eliminateEquation_test9", eliminateEquation_test9),
         ("eliminateEquation_test10", eliminateEquation_test10),
         ("eliminateEquation_test11", eliminateEquation_test11),
         ("eliminateEquation_test12", eliminateEquation_test12),
         ("eliminateEquation_test13", eliminateEquation_test13),
         ("eliminateEquation_test14", eliminateEquation_test14),
         ("eliminateEquation_test15", eliminateEquation_test15),
         ("eliminateEquation_test16", eliminateEquation_test16),
         ("eliminateEquation_test17", eliminateEquation_test17),
         ("eliminateEquation_test18", eliminateEquation_test18),
         ("eliminateEquation_test19", eliminateEquation_test19),
         ("eliminateEquation_test20", eliminateEquation_test20),
         ("inferSpine_test1", inferSpine_test1),
         ("inferSpine_test2", inferSpine_test2),
         ("inferSpine_test3", inferSpine_test3),
         ("inferSpine_test4", inferSpine_test4),
         ("inferSpine_test5", inferSpine_test5),
         ("inferSpine_test6", inferSpine_test6),
         ("inferSpine_test7", inferSpine_test7),
         ("inferSpine_test8", inferSpine_test8),
         ("inferSpine_test9", inferSpine_test9),
         ("inferSpine_test10", inferSpine_test10),
         ("inferSpine_test11", inferSpine_test11),
         ("inferSpine_test12", inferSpine_test12),
         ("inferSpine_test13", inferSpine_test13),
         ("checkExpr_ESimpleType_test1", checkExpr_ESimpleType_test1),
         ("checkExpr_ESimpleType_test2", checkExpr_ESimpleType_test2),
         ("checkExpr_ESimpleType_test3", checkExpr_ESimpleType_test3),
         ("checkExpr_ESimpleType_test4", checkExpr_ESimpleType_test4),
         ("checkExpr_ESimpleType_test5", checkExpr_ESimpleType_test5),
         ("checkExpr_ESimpleType_test6", checkExpr_ESimpleType_test6),
         ("checkExpr_ESimpleType_test7", checkExpr_ESimpleType_test7),
         ("checkExpr_ETuple_test1", checkExpr_ETuple_test1),
         ("checkExpr_ETuple_test2", checkExpr_ETuple_test2),
         ("checkExpr_ETuple_test3", checkExpr_ETuple_test3),
         ("checkExpr_ETuple_test4", checkExpr_ETuple_test4),
         ("checkExpr_ETuple_test5", checkExpr_ETuple_test5),
         ("checkExpr_ETuple_test6", checkExpr_ETuple_test6),
         ("checkExpr_ETuple_test7", checkExpr_ETuple_test7),
         ("checkExpr_ETuple_test8", checkExpr_ETuple_test8),
         ("checkExpr_ETuple_test9", checkExpr_ETuple_test9),
         ("checkExpr_ETuple_test10", checkExpr_ETuple_test10),
         ("checkExpr_ETuple_test11", checkExpr_ETuple_test11),
         ("checkExpr_ELambda_test1", checkExpr_ELambda_test1),
         ("checkExpr_ELambda_test2", checkExpr_ELambda_test2),
         ("checkExpr_ELambda_test3", checkExpr_ELambda_test3),
         ("checkExpr_ELambda_test4", checkExpr_ELambda_test4),
         ("checkExpr_ELambda_test5", checkExpr_ELambda_test5),
         ("checkExpr_ELambda_test6", checkExpr_ELambda_test6),
         ("checkExpr_ELambda_test7", checkExpr_ELambda_test7),
         ("checkExpr_ELambda_test8", checkExpr_ELambda_test8),
         ("checkExpr_ELambda_test9", checkExpr_ELambda_test9),
         ("checkExpr_ELambda_test10", checkExpr_ELambda_test10),
         ("checkExpr_ELambda_test11", checkExpr_ELambda_test11),
         ("checkExpr_ELambda_test12", checkExpr_ELambda_test12),
         ("checkExpr_ELambda_test13", checkExpr_ELambda_test13),
         ("checkExpr_ELambda_test14", checkExpr_ELambda_test14),
         ("checkExpr_ECons_test1", checkExpr_ECons_test1),
         ("checkExpr_ECons_test2", checkExpr_ECons_test2),
         ("checkExpr_EConstr_test1", checkExpr_EConstr_test1),
         ("checkExpr_EConstr_test2", checkExpr_EConstr_test2),
         ("checkExpr_EConstr_test3", checkExpr_EConstr_test3),
         ("checkExpr_EConstr_test4", checkExpr_EConstr_test4),
         ("checkExpr_EConstr_test5", checkExpr_EConstr_test5),
         ("checkExpr_EConstr_test6", checkExpr_EConstr_test6),
         ("checkExpr_EConstr_test7", checkExpr_EConstr_test7),
         ("checkExpr_EConstr_test8", checkExpr_EConstr_test8),
         ("checkExpr_EConstr_test9", checkExpr_EConstr_test9),
         ("checkExpr_EConstr_test10", checkExpr_EConstr_test10),
         ("checkExpr_EConstr_test11", checkExpr_EConstr_test11),
         ("checkExpr_EConstr_test12", checkExpr_EConstr_test12),
         ("inferExpr_EVar_test1", inferExpr_EVar_test1),
         ("inferExpr_EVar_test2", inferExpr_EVar_test2),
         ("inferExpr_EVar_test3", inferExpr_EVar_test3),
         ("inferExpr_EVar_test4", inferExpr_EVar_test4),
         ("inferExpr_EVar_test5", inferExpr_EVar_test5),
         ("inferExpr_EVar_test6", inferExpr_EVar_test6),
         ("inferExpr_EVar_test7", inferExpr_EVar_test7),
         ("inferExpr_EVar_test8", inferExpr_EVar_test8),
         ("inferExpr_EAnnot_test1", inferExpr_EAnnot_test1),
         ("inferExpr_EAnnot_test2", inferExpr_EAnnot_test2),
         ("inferExpr_EAnnot_test3", inferExpr_EAnnot_test3),
         ("inferExpr_EAnnot_test4", inferExpr_EAnnot_test4),
         ("inferExpr_EAnnot_test5", inferExpr_EAnnot_test5),
         ("inferExpr_EAnnot_test6", inferExpr_EAnnot_test6),
         ("inferExpr_EAnnot_test7", inferExpr_EAnnot_test7),
         ("inferExpr_EAnnot_test8", inferExpr_EAnnot_test8),
         ("inferExpr_EAnnot_test9", inferExpr_EAnnot_test9),
         ("inferExpr_EAnnot_test10", inferExpr_EAnnot_test10),
         ("inferExpr_EAnnot_test11", inferExpr_EAnnot_test11),
         ("inferExpr_EAnnot_test12", inferExpr_EAnnot_test12),
         ("checkBranch_test1", checkBranch_test1),
         ("checkBranch_test2", checkBranch_test2),
         ("checkBranch_test3", checkBranch_test3),
         ("checkBranch_test4", checkBranch_test4),
         ("checkBranch_test5", checkBranch_test5),
         ("checkBranch_test6", checkBranch_test6),
         ("checkBranch_test7", checkBranch_test7),
         ("checkBranch_test8", checkBranch_test8),
         ("checkBranch_test9", checkBranch_test9),
         ("checkBranch_test10", checkBranch_test10),
         ("checkBranch_test11", checkBranch_test11),
         ("checkBranch_test12", checkBranch_test12),
         ("checkBranch_test13", checkBranch_test13),
         ("checkBranch_test14", checkBranch_test14),
         ("checkBranch_test15", checkBranch_test15),
         ("checkBranch_test16", checkBranch_test16),
         ("checkBranch_test17", checkBranch_test17),
         ("checkBranch_test18", checkBranch_test18),
         ("checkBranch_test19", checkBranch_test19),
         ("checkBranch_test20", checkBranch_test20),
         ("checkBranch_test21", checkBranch_test21),
         ("checkBranch_test22", checkBranch_test22),
         ("checkBranch_test23", checkBranch_test23),
         ("checkBranch_test24", checkBranch_test24),
         ("checkBranch_test25", checkBranch_test25),
         ("checkBranch_test26", checkBranch_test26),
         ("checkBranch_test27", checkBranch_test27),
         ("checkBranch_test28", checkBranch_test28),
         ("checkBranch_test29", checkBranch_test29),
         ("checkBranch_test30", checkBranch_test30)]

runTest :: (TestName, Test) -> String
runTest (name, t) =
  name ++ " - " ++  if t then
    "Passed\n"
  else
    "Failed!\n"

runTests :: [(TestName, Test)] -> String
runTests = foldl (flip $ flip (++) . runTest) ""

checkAll :: [(TestName, Test)] -> Bool
checkAll = foldl (flip $ (&&) . snd) True

main :: IO ()
main = do
  putStrLn $ runTests tests
  if checkAll tests then
    putStrLn "All tests have passed :)"
  else
    putStrLn "One or more tests have failed! :("
  return ()
