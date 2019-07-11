module PreAST where

import AST

data PreGADTParameterTemplate
  = ParameterTypePT PreTypeTemplate
  | ParameterMonotypePT Monotype
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
  | PTTVec Monotype PreTypeTemplate
  | PTTParam String
  deriving (Show, Eq)
