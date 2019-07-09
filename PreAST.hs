module PreAST where

import AST

data PreGADTParameterTemplate
  = ParameterTypePT PreTypeTemplate
  | ParameterMonotypePT MonotypeTemplate
  deriving (Show, Eq)

data PreTypeTemplate
  = PTTUnit
  | PTTBool
  | PTTInt
  | PTTFloat
  | PTTChar
  | PTTString
  | PTTArrow PreTypeTemplate PreTypeTemplate
  | PTTGADT String [PreGADTParameterTemplate]
  | PTTProduct [PreTypeTemplate] Int
  | PTTUVar UTypeVar
  | PTTEVar ETypeVar
  | PTTUniversal UTypeVar Kind PreTypeTemplate
  | PTTExistential UTypeVar Kind PreTypeTemplate
  | PTTImp PropositionTemplate PreTypeTemplate
  | PTTAnd PreTypeTemplate PropositionTemplate
  | PTTVec MonotypeTemplate PreTypeTemplate
  | PTTParam String
  deriving (Show, Eq)

data GADTDefParameter
  = GADTDefParamType String
  | GADTDefParamMonotype Kind
  deriving (Show, Eq)

data ConstrDef p = ConstrDef p String PreTypeTemplate deriving (Show, Eq)

data ProgramBlock p
  = FunTypeAnnot p Var Type
  | FunDefCase p Var [Pattern p] (Expr p)
  | GADTDef p String [GADTDefParameter] [ConstrDef p]
  deriving (Show)
