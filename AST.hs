module AST where

type Var = String

--Source Syntax-------------------------------------

data ArithmBinOp
  = BinOpPlus
  | BinOpMinus
  | BinOpMult
  | BinOpDiv
  | BinOpRem

data ArithmUnOp
  = UnOpPlus
  | UnOpMinus

--TODO Arithm ?
data Expr p
  = EVar          p Var
  | EUnit         p
  | ELambda       p Var (Expr p)
  | EApp          p (Expr p) (Spine p)
  | ERec          p Var (Expr p)
  | EAnnot        p (Expr p) Type
  | EPair         p (Expr p) (Expr p)
  | EInjk         p (Expr p) Int
  | ECase         p (Expr p) [Branch p]
  | ENil          p
  | ECons         p (Expr p) (Expr p)
  | EIf           p (Expr p) (Expr p) (Expr p)
  | EArithmBinOp  p ArithmBinOp (Expr p) (Expr p)
  | EArithmUnOp   p ArithmUnOp (Expr p)
  deriving (Show)

type Spine p = [Expr p]

data Pattern p
  = PVar p Var
  | PPair p (Pattern p) (Pattern p)
  | PInjk p (Pattern p) Int
  | PNil  p
  | PCons p (Pattern p) (Pattern p)
  | PWild p
  deriving (Show)

type Branch p = ([Pattern p], Expr p)

--Types Syntax------------------------------------

newtype UTypeVar = UTypeVar {uTypeVarName :: Var} deriving (Show, Eq)
newtype ETypeVar = ETypeVar {eTypeVarName :: Var} deriving (Show, Eq, Ord)
data TypeVar = U UTypeVar | E ETypeVar deriving (Show, Eq)

data Kind = KStar | KNat deriving (Show, Eq)

data Type
  = TUnit
  | TArrow Type Type
  | TCoproduct Type Type
  | TProduct Type Type
  | TUVar UTypeVar
  | TEVar ETypeVar
  | TUniversal Var Kind Type
  | TExistential Var Kind Type
  | TImp Proposition Type
  | TAnd Type Proposition
  | TVec Monotype Type
  deriving (Show, Eq)

type Proposition = (Monotype, Monotype)

data Monotype
  = MZero
  | MSucc Monotype
  | MUnit
  | MUVar UTypeVar
  | MEVar ETypeVar
  | MArrow Monotype Monotype
  | MCoproduct Monotype Monotype
  | MProduct Monotype Monotype
  deriving (Show, Eq)

data ContextEntry
  = CTypeVar TypeVar Kind
  | CVar Var Type Principality
  | CETypeVar ETypeVar Kind Monotype
  | CUTypeVarEq UTypeVar Monotype
  | CMarker Proposition
  deriving (Show, Eq)

type Context = [ContextEntry]

data Principality = Principal | NotPrincipal deriving (Show, Eq)

data Polarity = Neutral | Positive | Negative deriving (Show, Eq)

instance Show ArithmBinOp where
  show BinOpPlus = "+"
  show BinOpMinus = "-"
  show BinOpMult = "*"
  show BinOpDiv = "/"
  show BinOpRem = "%"

instance Show ArithmUnOp where
  show UnOpPlus = "+"
  show UnOpMinus = "-"
