{-# LANGUAGE RankNTypes #-}

module ASTConstantFold (foldProgram) where

import AST
import CommonUtils
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

foldProgram :: Program p -> Program p
foldProgram = map (foldConstants Map.empty)

isFolded :: Expr p -> Bool
isFolded EBool {}   = True
isFolded EInt {}    = True
isFolded EFloat {}  = True
isFolded EChar {}   = True
isFolded EString {} = True
isFolded _ = False

inRelation :: (forall a. Ord a => a -> a -> Bool) -> Expr p -> Expr p -> Bool
inRelation r (EBool _ b1) (EBool _ b2) = r b1 b2
inRelation r (EInt _ n) (EInt _ m) = r n m
inRelation r (EFloat _ x) (EFloat _ y) = r x y
inRelation r (EChar _ c1) (EChar _ c2) = r c1 c2
inRelation r (EString _ s1) (EString _ s2) = r s1 s2
inRelation _ e1 e2 = error $ "Internal interpreter error while constant folding " ++ addQuotes (show e1) ++
  " and " ++ addQuotes (show e2) ++ ".\nThat should not have happened. Please contact language creator"

type FoldingContext p = Map.Map Var (Expr p)

foldConstants :: FoldingContext p ->  Expr p -> Expr p
foldConstants fc e@(EVar _ x) = fromMaybe e (Map.lookup x fc)
foldConstants _ e@EUnit {} = e
foldConstants _ e@EBool {} = e
foldConstants _ e@EInt {} = e
foldConstants _ e@EFloat {} = e
foldConstants _ e@EChar  {} = e
foldConstants _ e@EString {} = e
foldConstants fc (ELambda p x e) = ELambda p x $ foldConstants (Map.delete x fc) e
foldConstants fc (ESpine  p e es) = ESpine p (foldConstants fc e) (foldConstants fc <$> es)
foldConstants fc (EDef    p x e) = EDef p x $ foldConstants fc e
foldConstants fc (ERec    p t x e1 e2) = ERec p t x (foldConstants (Map.delete x fc) e1) (foldConstants (Map.delete x fc) e2)
foldConstants fc (EAnnot  _ e _) = foldConstants fc e
foldConstants fc (ETuple  p es n) = ETuple p (foldConstants fc <$> es) n
foldConstants fc (EConstr p name es) = EConstr p name $ foldConstants fc <$> es
foldConstants fc (ECase   p e bs) = ECase p (foldConstants fc e) (foldConstantsBranch fc <$> bs)
foldConstants fc (EIf     p e1 e2 e3) =
  case foldConstants fc e1 of
    EBool _ True -> foldConstants fc e2
    EBool _ False -> foldConstants fc e3
    e -> EIf p e (foldConstants fc e2) (foldConstants fc e3)
foldConstants fc (ELet p x e1 e2) =
  let e1' = foldConstants fc e1 in
  if isFolded e1' then
    foldConstants (Map.insert x e1' fc) e2
  else
    ELet p x e1' (foldConstants (Map.delete x fc) e2)
foldConstants fc (ETry p e c) = ETry p (foldConstants fc e) (foldConstantsCatch fc <$> c)
foldConstants fc (EError p e) = EError p $ foldConstants fc e
foldConstants fc (EUnOp _ UnOpPlus e) = foldConstants fc e
foldConstants fc (EUnOp p UnOpMinus e) =
  case foldConstants fc e of
    EInt p' n -> EInt p' $ -n
    e' -> EUnOp p UnOpMinus e'
foldConstants fc (EUnOp _ UnOpPlusFloat e) = foldConstants fc e
foldConstants fc (EUnOp p UnOpMinusFloat e) =
  case foldConstants fc e of
    EFloat p' x -> EFloat p' $ -x
    e' -> EUnOp p UnOpMinusFloat e'
foldConstants fc (EUnOp p UnOpNot e) =
  case foldConstants fc e of
    EBool p' b -> EBool p' $ not b
    e' -> EUnOp p UnOpNot e'
foldConstants fc (EBinOp p binOp e1 e2) =
  case (binOp, foldConstants fc e1, foldConstants fc e2) of
    (BinOp "+", EInt _ n, EInt _ m) -> EInt p $ n + m
    (BinOp "-", EInt _ n, EInt _ m) -> EInt p $ n - m
    (BinOp "*", EInt _ n, EInt _ m) -> EInt p $ n * m
    (BinOp "/", EInt _ n, EInt _ m) -> EInt p $ n `div` m
    (BinOp "%", EInt _ n, EInt _ m) -> EInt p $ n `mod` m
    (BinOp "+.", EFloat _ x, EFloat _ y) -> EFloat p $ x + y
    (BinOp "-.", EFloat _ x, EFloat _ y) -> EFloat p $ x - y
    (BinOp "*.", EFloat _ x, EFloat _ y) -> EFloat p $ x * y
    (BinOp "/.", EFloat _ x, EFloat _ y) -> EFloat p $ x / y
    (BinOp "&&", EBool _ b1, EBool _ b2) -> EBool p $ b1 && b2
    (BinOp "||", EBool _ b1, EBool _ b2) -> EBool p $ b1 || b2
    (BinOp "^", EString _ s1, EString _ s2) -> EString p $ s1 ++ s2
    (BinOp "==", e1', e2') | isFolded e1' && isFolded e2' -> EBool p $ inRelation (==) e1' e2'
    (BinOp "==", EConstr _ name1 [], EConstr _ name2 [])  -> EBool p $ name1 == name2
    (BinOp "!=", e1', e2') | isFolded e1' && isFolded e2' -> EBool p $ inRelation (/=) e1' e2'
    (BinOp "!=", EConstr _ name1 [], EConstr _ name2 [])  -> EBool p $ name1 /= name2
    (BinOp "<=", e1', e2') | isFolded e1' && isFolded e2' -> EBool p $ inRelation (<=) e1' e2'
    (BinOp ">=", e1', e2') | isFolded e1' && isFolded e2' -> EBool p $ inRelation (>=) e1' e2'
    (BinOp "<", e1', e2') | isFolded e1' && isFolded e2'  -> EBool p $ inRelation (<) e1' e2'
    (BinOp ">", e1', e2') | isFolded e1' && isFolded e2'  -> EBool p $ inRelation (>) e1' e2'
    (op, e1', e2') -> EBinOp p op e1' e2'

foldConstantsBranch :: FoldingContext p -> Branch p -> Branch p
foldConstantsBranch fc (ptrn, e, p) = (ptrn, foldConstants (Map.filterWithKey (\x _ -> and $ not <$> (isVarInPattern x <$> ptrn)) fc) e, p)

foldConstantsCatch :: FoldingContext p -> Catch p -> Catch p
foldConstantsCatch fc (exc@(BestraferException _ _ Nothing), e) = (exc, foldConstants fc e)
foldConstantsCatch fc (exc@(BestraferException _ _ (Just v)), e) = (exc, foldConstants (Map.delete v fc) e)
