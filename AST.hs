module AST where

import Data.Int
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
  = EVar          p Var
  | EUnit         p
  | EBool         p Bool
  | EInt          p Int64
  | EFloat        p Double
  | EChar         p Char
  | EString       p String
  | ELambda       p Var (Expr p)
  | ESpine        p (Expr p) (Spine p)
  | ERec          p Var (Expr p)
  | EAnnot        p (Expr p) Type
  | ETuple        p [Expr p] Int
  | EConstr       p String [Expr p]
  | ECase         p (Expr p) [Branch p]
  | ENil          p
  | ECons         p (Expr p) (Expr p)
  | EIf           p (Expr p) (Expr p) (Expr p)
  | ELet          p Var (Expr p) (Expr p)
  | EBinOp        p BinOp (Expr p) (Expr p)
  | EUnOp         p UnOp (Expr p)
  deriving (Show)

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
  deriving (Show)

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

newtype UTypeVar = UTypeVar {uTypeVarName :: Var} deriving (Show, Eq)
newtype ETypeVar = ETypeVar {eTypeVarName :: Var} deriving (Show, Eq, Ord)
data TypeVar = U UTypeVar | E ETypeVar deriving (Show, Eq)

data Kind = KStar | KNat deriving (Show, Eq)

data GADTParameter
  = ParameterType Type
  | ParameterMonotype Monotype
  deriving (Show, Eq)

data GADTParameterTemplate
  = ParameterTypeT TypeTemplate
  | ParameterMonotypeT MonotypeTemplate
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
  deriving (Show, Eq)

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
  | TTVec MonotypeTemplate TypeTemplate
  | TTParam Int
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
  deriving (Show, Eq)

data MonotypeTemplate
  = MTZero
  | MTSucc MonotypeTemplate
  | MTUnit
  | MTBool
  | MTInt
  | MTFloat
  | MTChar
  | MTString
  | MTUVar UTypeVar
  | MTEVar ETypeVar
  | MTArrow MonotypeTemplate MonotypeTemplate
  | MTGADT String [MonotypeTemplate]
  | MTProduct [MonotypeTemplate] Int
  | MTParam Int
  deriving (Show, Eq)

data ContextEntry
  = CTypeVar TypeVar Kind
  | CVar Var Type Principality
  | CETypeVar ETypeVar Kind Monotype
  | CUTypeVarEq UTypeVar Monotype
  | CMarker
  deriving (Show, Eq)

data Constructor = Constructor { constrTypeName :: String,
                                 constrUVars :: [(UTypeVar, Kind)],
                                 constrProps :: [PropositionTemplate],
                                 constrArgsTemplates :: [TypeTemplate]
                               } deriving (Show)

type ConstructorsContext = Map.Map String Constructor

type GADTArities = Map.Map String Int

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
