module Eval (eval) where

import AST
import EvalUtils
import BuiltinFunctions
import Data.Maybe (fromJust)
import Control.Monad.State
import qualified Data.Map as Map
import Control.Lens hiding (Context, op)
import Control.Exception

makeExceptionHandler :: EvalContext -> Catch p -> HandlerT Value
makeExceptionHandler c (BestraferException _ "ArithmeticException" Nothing, expr) =
  HandlerT ((\_ -> evalExpr c expr) :: ArithException -> StateT EvalState IO Value)
makeExceptionHandler c (BestraferException _ "IOException" Nothing, expr) =
  HandlerT ((\_ -> evalExpr c expr) :: IOException -> StateT EvalState IO Value)
makeExceptionHandler c (BestraferException _ "RuntimeException" Nothing, expr) =
  HandlerT ((\_ -> evalExpr c expr) :: CustomException -> StateT EvalState IO Value)
makeExceptionHandler c (BestraferException _ _ Nothing, expr) =
  HandlerT ((\_ -> evalExpr c expr) :: SomeException -> StateT EvalState IO Value)
makeExceptionHandler c (BestraferException _ "ArithmeticException" (Just v), expr) =
  HandlerT ((\exc -> evalExpr (addToEnv v (StringValue $ show exc) c) expr) :: ArithException -> StateT EvalState IO Value)
makeExceptionHandler c (BestraferException _ "IOException" (Just v), expr) =
  HandlerT ((\exc -> evalExpr (addToEnv v (StringValue $ show exc) c) expr) :: IOException -> StateT EvalState IO Value)
makeExceptionHandler c (BestraferException _ "RuntimeException" (Just v), expr) =
  HandlerT ((\exc -> evalExpr (addToEnv v (StringValue $ show exc) c) expr) :: CustomException -> StateT EvalState IO Value)
makeExceptionHandler c (BestraferException _ _ (Just v), expr) =
  HandlerT ((\exc -> evalExpr (addToEnv v (StringValue $ show exc) c) expr) :: SomeException -> StateT EvalState IO Value)


valueOfGlobalContextEntry :: DefinitionValue -> StateT EvalState IO Value
valueOfGlobalContextEntry (Evaluated v) = return v
valueOfGlobalContextEntry (NotEvaluated e) = e ()

valueOfVar :: Value -> StateT EvalState IO Value
valueOfVar (DefValue (Evaluated v)) = return v
valueOfVar (DefValue (NotEvaluated e)) = e ()
valueOfVar v = return v

evalExpr :: EvalContext -> Expr p -> StateT EvalState IO Value
evalExpr c (EAnnot _ e _) = evalExpr c e
evalExpr _ EUnit {} = return UnitValue
evalExpr _ (EBool   _ b) = return $ BoolValue b
evalExpr _ (EInt    _ x) = return $ IntValue x
evalExpr _ (EFloat  _ x) = return $ FloatValue x
evalExpr _ (EChar   _ c) = return $ CharValue c
evalExpr _ (EString _ s) = return $ StringValue s
evalExpr c (ELambda _ arg e) = return $ FunValue (\val -> evalExpr (addToEnv arg val c) e)
evalExpr c (ETuple _ es _) = TupleValue <$> mapM (evalExpr c) es
evalExpr c (ELet _ x e1 e2) = (addToEnv x <$> evalExpr c e1 <*> pure c) >>= flip evalExpr e2
evalExpr c (ERec _ _ f e1 e2) = do
  let c2 = addToEnv f (DefValue (NotEvaluated (\() -> evalExpr c2 e1))) c
  evalExpr c2 e2
evalExpr c (EVar _ x) = do
  gc <- view globalContext <$> get
  fromJust ((valueOfVar <$> Map.lookup x c) `mplus` (valueOfGlobalContextEntry <$> Map.lookup x gc))
evalExpr _ (EDef _ f e) = do
  gc <- view globalContext <$> get
  case gc Map.! f of
    Evaluated x -> return x
    NotEvaluated _ -> do
      v <- evalExpr Map.empty e
      modify $ over globalContext (Map.insert f (Evaluated v))
      return v
evalExpr c (EIf _ e1 e2 e3) = do
  BoolValue b <- evalExpr c e1
  if b then
    evalExpr c e2
  else
    evalExpr c e3
evalExpr c (ESpine _ e s) = do
  f <- evalExpr c e
  xs <- mapM (evalExpr c) s
  foldM (\(FunValue fi) -> fi) f xs
evalExpr c (EBinOp _ (BinOp "&&") e1 e2) = do
  v1 <- evalExpr c e1
  case v1 of
    BoolValue True -> evalExpr c e2
    b1 -> return b1
evalExpr c (EBinOp _ (BinOp "||") e1 e2) = do
  v1 <- evalExpr c e1
  case v1 of
    BoolValue False -> evalExpr c e2
    b1 -> return b1
evalExpr c (EBinOp _ (BinOp opName) e1 e2) = do
  gc <- view globalContext <$> get
  FunValue op <- valueOfGlobalContextEntry $ gc Map.! opName
  v1 <- evalExpr c e1
  v2 <- evalExpr c e2
  FunValue f <- op v1
  f v2
evalExpr c (EUnOp _ UnOpPlus e) = evalExpr c e
evalExpr c (EUnOp _ UnOpMinus e) = do
  IntValue v <- evalExpr c e
  return $ IntValue (-v)
evalExpr c (EUnOp _ UnOpPlusFloat e) = evalExpr c e
evalExpr c (EUnOp _ UnOpMinusFloat e) = do
  FloatValue v <- evalExpr c e
  return $ FloatValue (-v)
evalExpr c (EUnOp _ UnOpNot e) = do
  BoolValue v <- evalExpr c e
  return $ BoolValue $ not v
evalExpr _ (EConstr _ "[]" []) = return $ VecValue []
evalExpr c (EConstr _ ":" [x, xs]) = do
  v <- evalExpr c x
  VecValue vs <- evalExpr c xs
  return $ VecValue (v : vs)
evalExpr _ (EConstr _ "{}" []) = return $ ListValue []
evalExpr c (EConstr _ ";" [x, xs]) = do
  v <- evalExpr c x
  ListValue vs <- evalExpr c xs
  return $ ListValue (v : vs)
evalExpr c (EConstr p name args) = do
  ca <- view constrArities <$> get
  if ca Map.! name == length args then do
    vs <- mapM (evalExpr c) args
    return $ ConstrValue name vs
  else do
    freshVar <- view freshVarNum <$> get
    modify $ over freshVarNum (+ (ca Map.! name - length args))
    let vars = ("#" ++) . show .  (+ freshVar) <$> [0 .. ca Map.! name - length args - 1]
    let f = foldr (ELambda p) (EConstr p name (args ++ map (EVar p) vars)) vars
    evalExpr c f
evalExpr c (ECase _ e bs) = do
  v <- evalExpr c e
  fromJust . msum $ map (match c [v]) bs
  where
    match :: EvalContext -> [Value] -> Branch p -> Maybe (StateT EvalState IO Value)
    match context values branch =
      case (context, values, branch) of
        (cb, [], ([], eb, _)) -> return $ evalExpr cb eb
        (cb, _ : vs, (PWild _ : ptrns, eb, p)) -> match cb vs (ptrns, eb, p)
        (cb, v : vs, (PVar _ x : ptrns, eb, p)) -> match (addToEnv x v cb) vs (ptrns, eb, p)
        (cb, UnitValue : vs, (PUnit _ : ptrns, eb, p)) -> match cb vs (ptrns, eb, p)
        (cb, BoolValue b1 : vs, (PBool _ b2 : ptrns, eb, p)) | b1 == b2 -> match cb vs (ptrns, eb, p)
        (cb, IntValue n1 : vs, (PInt _ n2 : ptrns, eb, p)) | n1 == n2 -> match cb vs (ptrns, eb, p)
        (cb, FloatValue x1 : vs, (PFloat _ x2 : ptrns, eb, p)) | x1 == x2 -> match cb vs (ptrns, eb, p)
        (cb, CharValue c1 : vs, (PChar _ c2 : ptrns, eb, p)) | c1 == c2 -> match cb vs (ptrns, eb, p)
        (cb, StringValue s1 : vs, (PString _ s2 : ptrns, eb, p)) | s1 == s2 -> match cb vs (ptrns, eb, p)
        (cb, VecValue [] : vs, (PConstr _ "[]" [] : ptrns, eb, p)) -> match cb vs (ptrns, eb, p)
        (cb, VecValue (x : xs) : vs, (PConstr _ ":" [y, ys] : ptrns, eb, p)) ->
          match cb (x : VecValue xs : vs) (y : ys : ptrns, eb, p)
        (cb, ListValue [] : vs, (PConstr _ "{}" [] : ptrns, eb, p)) -> match cb vs (ptrns, eb, p)
        (cb, ListValue (x : xs) : vs, (PConstr _ ";" [y, ys] : ptrns, eb, p)) ->
          match cb (x : ListValue xs : vs) (y : ys : ptrns, eb, p)
        (cb, TupleValue xs : vs, (PTuple _ ys n : ptrns, eb, p)) | length xs == n ->
          match cb (xs ++ vs) (ys ++ ptrns, eb, p)
        (cb, ConstrValue name1 xs : vs, (PConstr _ name2 ys : ptrns, eb, p)) | name1 == name2 ->
          match cb (xs ++ vs) (ys ++ ptrns, eb, p)
        _ -> Nothing
evalExpr c (ETry _ e cs) =
  evalExpr c e `catchStateT` map (makeExceptionHandler c) cs
evalExpr c (EError _ e) = do
  StringValue message <- evalExpr c e
  liftIO . throw $ CustomException message

eval :: Program p -> ConstructorsContext -> IO [Value]
eval program constrs = do
  let userFunctions = map (\(EDef p name e) -> (name, NotEvaluated (\() -> evalExpr Map.empty (EDef p name e)))) program
  let gc = Map.fromList $ builtinFunctions ++ userFunctions
  let ca = Map.map  (length . constrArgsTemplates) constrs
  let startState = EvalState {_constrArities = ca, _globalContext = gc, _freshVarNum = 0}
  evalStateT (mapM (evalExpr Map.empty) program) startState
