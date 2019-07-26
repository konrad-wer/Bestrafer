{-# LANGUAGE TemplateHaskell #-}

module EvalUtils where

import AST
import Data.Int
import Control.Monad.State
import Data.List (intercalate)
import qualified Data.Map as Map
import Control.Lens hiding (Context)

data Value
  = UnitValue
  | BoolValue Bool
  | IntValue Int64
  | FloatValue Double
  | CharValue Char
  | StringValue String
  | TupleValue [Value]
  | VecValue [Value]
  | FunValue (Value -> StateT EvalState IO Value)
  | ConstrValue String [Value]

instance Show Value where
  show UnitValue = "()"
  show (BoolValue b) = show b
  show (IntValue x) = show x
  show (FloatValue x) = show x
  show (CharValue c) = show c
  show (StringValue s) = show s
  show (TupleValue vs) = "(" ++ intercalate  ", " (map show vs) ++ ")"
  show (VecValue vs) = "[" ++ intercalate  ", " (map show vs) ++ "]"
  show (FunValue _) = "function"
  show (ConstrValue name vs) = name ++ (vs >>= (" " ++) . show)

instance Eq Value where
  (==) UnitValue UnitValue = True
  (==) (BoolValue b1) (BoolValue b2) = b1 == b2
  (==) (IntValue n1) (IntValue n2) = n1 == n2
  (==) (FloatValue x1) (FloatValue x2) = x1 == x2
  (==) (CharValue c1) (CharValue c2) = c1 == c2
  (==) (StringValue s1) (StringValue s2) = s1 == s2
  (==) (TupleValue xs) (TupleValue ys) = xs == ys
  (==) (VecValue xs) (VecValue ys) = xs == ys
  (==) (ConstrValue name1 xs) (ConstrValue name2 ys) = name1 == name2 && xs == ys
  (==) _ _ = False

instance Ord Value where
  (<=) UnitValue UnitValue = True
  (<=) (BoolValue b1) (BoolValue b2) = b1 <= b2
  (<=) (IntValue n1) (IntValue n2) = n1 <= n2
  (<=) (FloatValue x1) (FloatValue x2) = x1 <= x2
  (<=) (CharValue c1) (CharValue c2) = c1 <= c2
  (<=) (StringValue s1) (StringValue s2) = s1 <= s2
  (<=) (TupleValue xs) (TupleValue ys) = xs <= ys
  (<=) (ConstrValue name1 xs) (ConstrValue name2 ys) = name1 == name2 && xs <= ys
  (<=) _ _ = False

data GlobalContextEntry
  = Evaluated Value
  | NotEvaluated (() -> StateT EvalState IO Value)
  | InProgres


type EvalContext = Map.Map Var Value
type GlobalContext = Map.Map Var GlobalContextEntry
type ConstructorsArities = Map.Map String Int

data EvalState = EvalState
  {
    _constrArities :: ConstructorsArities,
    _globalContext :: GlobalContext,
    _freshVarNum :: Int
  }

makeLenses ''EvalState

addToEnv :: Var -> Value -> EvalContext -> EvalContext
addToEnv = Map.insert