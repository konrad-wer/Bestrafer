module CommonUtils where

import Control.Monad (void)
import AST

pair :: (a -> b, a -> c) -> a -> (b, c)
pair (f, g) x = (f x, g x)

cross :: (a -> b) -> (c -> d) -> (a, c) -> (b, d)
cross f g = pair (f . fst, g . snd)

iterM :: Monad m => (a -> m ()) -> [a] -> m ()
iterM = (.)(.)(.) void mapM

addQuotes :: String -> String
addQuotes = ("'" ++) . (++ "'")

addParens :: String -> String
addParens = ("(" ++) . (++ ")")

isVarInPattern :: Var -> Pattern p -> Bool
isVarInPattern x (PVar _ y) = x == y
isVarInPattern _ PWild   {} = False
isVarInPattern _ PUnit   {} = False
isVarInPattern _ PBool   {} = False
isVarInPattern _ PInt    {} = False
isVarInPattern _ PFloat  {} = False
isVarInPattern _ PChar   {} = False
isVarInPattern _ PString {} = False
isVarInPattern x (PTuple  _ ps _) = or $ isVarInPattern x <$> ps
isVarInPattern x (PConstr _ _ ps) = or $ isVarInPattern x <$> ps
