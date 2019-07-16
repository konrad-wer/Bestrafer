module AST where

import Data.Int
import Data.Maybe
import Control.Monad
import qualified Data.Map as Map

type Var = String

--Source Syntax-----------------------------------------------------------------

newtype BinOp = BinOp String

data UnOp
  = UnOpPlus
  | UnOpMinus
  | UnOpPlusFloat
  | UnOpMinusFloat
  | UnOpNot

--TODO Arithm ?
data Expr p
  = EVar    p Var
  | EUnit   p
  | EBool   p Bool
  | EInt    p Int64
  | EFloat  p Double
  | EChar   p Char
  | EString p String
  | ELambda p Var (Expr p)
  | ESpine  p (Expr p) (Spine p)
  | ERec    p Var (Expr p)
  | EAnnot  p (Expr p) Type
  | ETuple  p [Expr p] Int
  | EConstr p String [Expr p]
  | ECase   p (Expr p) [Branch p]
  | ENil    p
  | ECons   p (Expr p) (Expr p)
  | EIf     p (Expr p) (Expr p) (Expr p)
  | ELet    p Var (Expr p) (Expr p)
  | EBinOp  p BinOp (Expr p) (Expr p)
  | EUnOp   p UnOp (Expr p)

type Program p = [Expr p]

getPos :: Expr p -> p
getPos (EVar    p _) = p
getPos (EUnit   p) = p
getPos (EBool   p _) = p
getPos (EInt    p _) = p
getPos (EFloat  p _) = p
getPos (EChar   p _) = p
getPos (EString p _) = p
getPos (ELambda p _ _) = p
getPos (ESpine  p _ _) = p
getPos (ERec    p _ _) = p
getPos (EAnnot  p _ _) = p
getPos (ETuple  p _ _) = p
getPos (EConstr p _ _) = p
getPos (ECase   p _ _) = p
getPos (ENil    p) = p
getPos (ECons   p _ _) = p
getPos (EIf     p _ _ _) = p
getPos (ELet    p _ _ _) = p
getPos (EBinOp  p _ _ _ ) = p
getPos (EUnOp   p _ _) = p

type Spine p = [Expr p]

data Pattern p
  = PVar    p Var
  | PTuple  p [Pattern p] Int
  | PNil    p
  | PCons   p (Pattern p) (Pattern p)
  | PWild   p
  | PUnit   p
  | PBool   p Bool
  | PInt    p Int64
  | PFloat  p Double
  | PChar   p Char
  | PString p String
  | PConstr p String [Pattern p]

type Branch p = ([Pattern p], Expr p, p)

getPosFromPattern :: Pattern p -> p
getPosFromPattern (PVar    p _)   = p
getPosFromPattern (PTuple  p _ _) = p
getPosFromPattern (PNil    p)     = p
getPosFromPattern (PCons   p _ _) = p
getPosFromPattern (PWild   p)     = p
getPosFromPattern (PUnit   p)     = p
getPosFromPattern (PBool   p _)   = p
getPosFromPattern (PInt    p _)   = p
getPosFromPattern (PFloat  p _)   = p
getPosFromPattern (PChar   p _)   = p
getPosFromPattern (PString p _)   = p
getPosFromPattern (PConstr p _ _) = p

getPosFromBranch :: Branch p -> p
getPosFromBranch (_, _, p) = p

--Types Syntax------------------------------------------------------------------

newtype UTypeVar = UTypeVar {uTypeVarName :: Var} deriving (Eq)
newtype ETypeVar = ETypeVar {eTypeVarName :: Var} deriving (Eq, Ord)
data TypeVar = U UTypeVar | E ETypeVar deriving (Eq)

data Kind = KStar | KNat deriving (Eq, Ord)

data GADTParameter
  = ParameterType Type
  | ParameterMonotype Monotype
  deriving (Eq)

data GADTParameterTemplate
  = ParameterTypeT TypeTemplate
  | ParameterMonotypeT Monotype
  deriving (Show, Eq)

data Type
  = TUnit
  | TBool
  | TInt
  | TFloat
  | TChar
  | TString
  | TArrow Type Type
  | TGADT String [GADTParameter]
  | TProduct [Type] Int
  | TUVar UTypeVar
  | TEVar ETypeVar
  | TUniversal UTypeVar Kind Type
  | TExistential UTypeVar Kind Type
  | TImp Proposition Type
  | TAnd Type Proposition
  | TVec Monotype Type
  deriving (Eq)

data TypeTemplate
  = TTUnit
  | TTBool
  | TTInt
  | TTFloat
  | TTChar
  | TTString
  | TTArrow TypeTemplate TypeTemplate
  | TTGADT String [GADTParameterTemplate]
  | TTProduct [TypeTemplate] Int
  | TTUVar UTypeVar
  | TTEVar ETypeVar
  | TTUniversal UTypeVar Kind TypeTemplate
  | TTExistential UTypeVar Kind TypeTemplate
  | TTImp PropositionTemplate TypeTemplate
  | TTAnd TypeTemplate PropositionTemplate
  | TTVec Monotype TypeTemplate
  | TTParam String
  deriving (Show, Eq)

type Proposition = (Monotype, Monotype)

type PropositionTemplate = (MonotypeTemplate, MonotypeTemplate)

data Monotype
  = MZero
  | MSucc Monotype
  | MUnit
  | MBool
  | MInt
  | MFloat
  | MChar
  | MString
  | MUVar UTypeVar
  | MEVar ETypeVar
  | MArrow Monotype Monotype
  | MGADT String [Monotype]
  | MProduct [Monotype] Int
  deriving (Eq)

data MonotypeTemplate
  = MTMono Monotype
  | MTParam String
  deriving (Show, Eq)

data ContextEntry
  = CTypeVar TypeVar Kind
  | CVar Var Type Principality
  | CETypeVar ETypeVar Kind Monotype
  | CUTypeVarEq UTypeVar Monotype
  | CMarker
  deriving (Show, Eq)

data Constructor = Constructor { constrTypeName :: String,
                                 constrTypeParmsTemplate :: [String],
                                 constrUVars :: [(UTypeVar, Kind)],
                                 constrProps :: [PropositionTemplate],
                                 constrArgsTemplates :: [TypeTemplate]
                               } deriving (Show)

type ConstructorsContext = Map.Map String Constructor
type FunTypeContext = Map.Map Var Type

data GADTDefParameter
  = GADTDefParamType String
  | GADTDefParamMonotype Kind
  deriving (Show, Eq, Ord)

type GADTDefs = Map.Map String [GADTDefParameter]

data ConstrDef p = ConstrDef {constrDefPos :: p, constrDefName :: String, constrDefTypeTemplate :: TypeTemplate} deriving (Show, Eq)

data ProgramBlock p
  = FunTypeAnnot p Var Type
  | FunDefCase p Var [Pattern p] (Expr p)
  | GADTDef p String [GADTDefParameter] [ConstrDef p]
  deriving (Show)

type Context = [ContextEntry]

data Principality = Principal | NotPrincipal deriving (Show, Eq)

data Polarity = Neutral | Positive | Negative deriving (Show, Eq)

instance Show BinOp where
  show (BinOp op) = op

instance Show UnOp where
  show UnOpPlus = "+"
  show UnOpMinus = "-"
  show UnOpNot = "!"
  show UnOpPlusFloat = "+."
  show UnOpMinusFloat = "-."

instance Show (Expr p) where
  show (EVar    _ x) = x
  show (EUnit   _) = "()"
  show (EBool   _ b) = show b
  show (EInt    _ i) = show i
  show (EFloat  _ d) = show d
  show (EChar   _ c) = show c
  show (EString _ s) = show s
  show (ELambda _ x e) = "(" ++ "λ " ++ x ++ " -> " ++ show e ++ ")"
  show (ESpine  _ e s) = "(" ++ show e ++ (s >>= (' ' :) . show) ++ ")"
  show (ERec    _ f e) = f ++ " = " ++ show e
  show (EAnnot  _ e t) = "(" ++ show e ++ " :: " ++ show t ++ ")"
  show (ETuple  _ [] _) = "()"
  show (ETuple  _ (e : es) _) = "(" ++ show e ++ (es >>= (", " ++) . show) ++ ")"
  show (EConstr _ c args) = "(" ++ c ++ (args >>= (' ' :) . show) ++ ")"
  show (ECase   _ e bs) = "(case " ++ show e ++ " of " ++ (bs >>= showBranch) ++ ")"
  show (ENil    _) = "[]"
  show (ECons   _ e1 e2) = "(" ++ show e1 ++ " : " ++ show e2 ++ ")"
  show (EIf     _ e1 e2 e3) = "(if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3 ++ ")"
  show (ELet    _ x e1 e2) = "(let " ++ x ++ " = " ++ show e1 ++ " = " ++ show e2 ++ ")"
  show (EBinOp  _ op e1 e2) = "(" ++ show e1 ++ " " ++ show op ++ " " ++ show e2 ++ ")"
  show (EUnOp   _ op e) = "(" ++ show op ++ " " ++ show e ++ ")"

instance Show (Pattern p) where
  show (PVar    _ x) = x
  show (PTuple  _ [] _) = "()"
  show (PTuple  _ (p : ps) _) = "(" ++ show p ++ (ps >>= (", " ++) . show) ++ ")"
  show (PNil    _) = "[]"
  show (PCons   _ p1 p2) = "(" ++ show p1 ++ " : " ++ show p2 ++ ")"
  show (PWild   _) = "_"
  show (PUnit   _) = "()"
  show (PBool   _ b) = show b
  show (PInt    _ i) = show i
  show (PFloat  _ d) = show d
  show (PChar   _ c) = show c
  show (PString _ s) = show s
  show (PConstr _ c args) = "(" ++ c ++ (args >>= (", " ++) . show) ++ ")"

showBranch :: Branch p -> String
showBranch ([], e, _)= "| -> " ++ show e
showBranch ([p], e, _)= "| " ++ show p ++ " -> " ++ show e
showBranch (p : ps, e, _)= "| " ++ show p ++ (ps >>= ("; " ++). show) ++ " -> " ++ show e

instance Show UTypeVar where
  show (UTypeVar u) = u

instance Show ETypeVar where
  show (ETypeVar e) = "(existential variable: " ++ e ++ ")"

instance Show TypeVar where
  show (U u) = show u
  show (E e) = show e

instance Show Kind where
  show KStar = "*"
  show KNat = "N"

instance Show GADTParameter where
  show (ParameterType t) = show t
  show (ParameterMonotype m) = show m

instance Show Type where
  show TUnit   = "()"
  show TBool   = "Bool"
  show TInt    = "Int"
  show TFloat  = "Float"
  show TChar   = "Char"
  show TString = "String"
  show (TArrow t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (TGADT name args) = "(" ++ name ++ (args >>= (' ' :) . show) ++ ")"
  show (TProduct [] _) = "()"
  show (TProduct (t : ts) _) = "(" ++ show t ++ (ts >>= (", " ++) . show) ++ ")"
  show (TUVar u) = show u
  show (TEVar e) = show e
  show (TUniversal u k t) = "(∀ " ++ show u ++ show k ++ " . " ++ show t ++ ")"
  show (TExistential u k t) = "(∃ " ++ show u ++ show k ++ " . " ++ show t ++ ")"
  show (TImp prop t) = "(" ++ show prop ++ " => " ++ show t ++  ")"
  show (TAnd t prop) = "(" ++ show t ++ " ^ " ++ show prop ++ ")"
  show TVec {}  = "asdasd"

showProp :: Proposition -> String
showProp (m1, m2) = show m1 ++ " = " ++ show m2

instance Show Monotype where
  show MZero   = "0"
  show MUnit   = "()"
  show MBool   = "Bool"
  show MInt    = "Int"
  show MFloat  = "Float"
  show MChar   = "Char"
  show MString = "String"
  show (MArrow m1 m2) = "(" ++ show m1 ++ " -> " ++ show m2 ++ ")"
  show (MGADT name args) = "(" ++ name ++ (args >>= (' ' :) . show) ++ ")"
  show (MProduct [] _) = "()"
  show (MProduct (m : ms) _) = "(" ++ show m ++ (ms >>= (", " ++) . show) ++ ")"
  show (MUVar u) = show u
  show (MEVar e) = show e
  show (MSucc x) = fromMaybe "" $ (show <$> tryGetInt (MSucc x)) `mplus` return ("(S" ++ show x ++ ")")
    where
      tryGetInt :: Monotype -> Maybe Integer
      tryGetInt (MSucc m) = (1 +) <$> tryGetInt m
      tryGetInt MZero = return 0
      tryGetInt _ = Nothing
