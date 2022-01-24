--High level Intermediate Language
module HIL where

import AST
import qualified Data.Set as Set
import Data.List (intercalate)

type HILProgram = [HILExpr]

data CapturedVar = SelfCapture Var | Weak Var | Strong Var deriving (Eq, Ord, Show)

unpackCapturedVar :: CapturedVar -> Var
unpackCapturedVar (SelfCapture x) = x
unpackCapturedVar (Weak x) = x
unpackCapturedVar (Strong x) = x

data HILExpr
  = HILVar         Var
  | HILClosureVar  Int
  | HILUnit
  | HILSelfRef
  | HILGlobalVar   Var
  | HILBool        Bool
  | HILInt         Integer
  | HILFloat       Double
  | HILChar        Char
  | HILString      String
  | HILClosure     Var (Set.Set CapturedVar) HILExpr
  | HILSpine       HILExpr HILSpine
  | HILDef         Var HILExpr
  | HILRec         Var HILExpr HILExpr
  | HILTuple       [HILExpr]
  | HILConstr      String [HILExpr]
  | HILPatternExpr HILPatternExpr
  | HILIf          HILExpr HILExpr HILExpr
  | HILLet         Var HILExpr HILExpr
  | HILBinOp       BinOp HILExpr HILExpr
  | HILUnOp        UnOp HILExpr
  | HILTry         HILExpr [HILCatch]
  | HILError       HILExpr

data HILPatternExpr
  = HILMatchedExpr HILExpr
  | HILPtrnExprLet Var HILInspectableExpr HILPatternExpr
  | HILGetElem     Int Var
  | HILCase        Var [HILBranch]
  | HILCaseJoin    HILPatternExpr HILPatternExpr

data HILInspectableExpr
  = HILInspectVar Var
  | HILInspectElem Int Var

type HILSpine = [HILExpr]

type HILBranch = (HILPattern, HILPatternExpr)

data HILPattern
  = HILPUnit
  | HILPBool   Bool
  | HILPInt    Integer
  | HILPFloat  Double
  | HILPChar   Char
  | HILPString String
  | HILPConstr String

data HILBestraferException = HILBestraferException String (Maybe Var)
type HILCatch = (HILBestraferException, HILExpr)

instance Show HILExpr where
  show HILUnit = "()"
  show HILSelfRef = "self"
  show (HILVar x) = x
  show (HILClosureVar x) = "this[" ++ show x ++ "]"
  show (HILGlobalVar x) = "global[" ++ show x ++ "]"
  show (HILBool   b) = show b
  show (HILInt    i) = show i
  show (HILFloat  d) = show d
  show (HILChar   c) = show c
  show (HILString s) = show s
  show (HILClosure x xs e) = "(" ++ "λ " ++ x ++ " {" ++ intercalate "," (map show $ Set.toList xs) ++ "} -> " ++ show e ++ ")"
  show (HILSpine  e s) = "(" ++ show e ++ (s >>= (' ' :) . show) ++ ")"
  show (HILDef    f e) = f ++ " = " ++ show e
  show (HILTuple  []) = "()"
  show (HILTuple  (e : es)) = "(" ++ show e ++ (es >>= (", " ++) . show) ++ ")"
  show (HILConstr c args) = "(" ++ c ++ (args >>= (' ' :) . show) ++ ")"
  show (HILIf     e1 e2 e3) = "(if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3 ++ ")"
  show (HILLet    x e1 e2) = "(let " ++ x ++ " = " ++ show e1 ++ " in\n" ++ show e2 ++ ")"
  show (HILRec    x e1 e2) = "(rec " ++ x ++ " = " ++ show e1 ++ " in\n" ++ show e2 ++ ")"
  show (HILBinOp  op e1 e2) = "(" ++ show e1 ++ " " ++ show op ++ " " ++ show e2 ++ ")"
  show (HILUnOp   op e) = "(" ++ show op ++ " " ++ show e ++ ")"
  show (HILTry    e cs) = "(try: " ++ show e ++ " catch:" ++ (cs >>= (" " ++) . showHILCatch) ++ ")"
  show (HILError  e) = "(error: " ++ show e ++ ")"
  show (HILPatternExpr e) = show e

instance Show HILPatternExpr where
  show (HILMatchedExpr e) = show e
  show (HILPtrnExprLet x e1 e2) = "(let " ++ x ++ " = " ++ show e1 ++ " in\n" ++ show e2 ++ ")"
  show (HILCase   e bs) = "(case " ++ show e ++ " of " ++ (bs >>= ("\n" ++) . showHILBranch) ++ ")"
  show (HILGetElem n e) = "(" ++ show e ++ ")." ++ show n
  show (HILCaseJoin e1 e2) = "[" ++ show e1 ++ "] if failed [" ++ show e2 ++ "]"

instance Show HILInspectableExpr where
    show (HILInspectVar x) = x
    show (HILInspectElem n e) = "(" ++ show e ++ ")." ++ show n

instance Show HILBestraferException where
  show (HILBestraferException ex Nothing) = ex
  show (HILBestraferException ex (Just v)) = ex ++ " " ++ v

showHILCatch :: HILCatch -> String
showHILCatch (ex, e) = show ex ++ " -> " ++ show e

instance Show HILPattern where
  show HILPUnit = "()"
  show (HILPBool   b) = show b
  show (HILPInt    i) = show i
  show (HILPFloat  d) = show d
  show (HILPChar   c) = show c
  show (HILPString s) = show s
  show (HILPConstr c) = c

showHILBranch :: HILBranch -> String
showHILBranch (p, e)=  show p ++ " -> " ++ show e
