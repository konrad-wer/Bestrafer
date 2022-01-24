{-# LANGUAGE TemplateHaskell #-}

module Codegen (generateProgram) where

import AST
import HIL
import Data.Char
import Data.List
import Control.Lens
import Control.Monad.State
import qualified Data.Set as Set

data CodegenState = CodegenState
  {
    _freshVarNum :: Integer,
    _closures :: [String]
  } deriving (Show)

makeLenses ''CodegenState

type CodegenMonad = State CodegenState

showIndent :: Int -> String
showIndent = flip replicate ' ' . (* 2)

freshClosureName :: CodegenMonad Var
freshClosureName =  do
  a <- ("closure_" ++) . show . view freshVarNum <$> get
  modify $ over freshVarNum (+ 1)
  return a

addIncludes :: String -> String
addIncludes = ("#include \"Bestrafer.h\"\n#include \"BuiltinFunctions.h\"\n#include <optional>\n#include <vector>\n\n" ++)

addNamespace :: String -> String
addNamespace = ("namespace Bestrafer {\n\n" ++) . (++ "\n\n} // namespace Bestrafer")

generateForwardDecls :: HILProgram -> String
generateForwardDecls [] = ""
generateForwardDecls (HILDef v _ : defs) = "StoreValue " ++ v ++ "();\n" ++ generateForwardDecls defs
generateForwardDecls (_ : defs) = generateForwardDecls defs

generateProgram :: HILProgram -> String
generateProgram prog =
  let initialState = CodegenState { _freshVarNum = 0, _closures = [] } in
  let (prog', st) = runState (mapM (generate 0 None) prog) initialState in
  addIncludes (addNamespace (generateForwardDecls prog ++ "\n\n" ++ intercalate "\n\n" (reverse (view closures st) ++ prog')) ++ "\n\n" ++ generateMain prog)

generateMain :: HILProgram -> String
generateMain prog = "int main() {\n" ++ aux prog ++ "  return 0;\n}"
  where
    aux [] = ""
    aux (HILDef v _ : defs) = "  Bestrafer::" ++ v ++ "();\n" ++ aux defs
    aux (_ : defs) = aux defs

data ClosureRefStatus = None | Copy | NoCopy

instance Show ClosureRefStatus where
  show None = ""
  show Copy = "refs"
  show NoCopy = "std::move(refs)"

generateClosureValue :: Int -> ClosureRefStatus -> Bool -> Var -> Set.Set CapturedVar -> String
generateClosureValue i closureRefStatus recursive closureName captures =
  let capturing = Set.foldl (\code capture -> code ++ "\n" ++ showIndent (i + 1) ++
                  "closure_ptr->refs.push_back("++ translateCapturedVar capture ++ ");\n") "" captures in
    "({\n" ++ showIndent (i + 1) ++
      "auto closure_ptr = std::make_shared<" ++ closureName ++ ">(" ++ show closureRefStatus ++ ");\n" ++
      (if recursive then showIndent (i + 1) ++ "std::weak_ptr<" ++ closureName ++ "> weak_ref = closure_ptr;\n" ++
      showIndent (i + 1) ++ "closure_ptr->self = closure_ptr;\n" else "") ++
      capturing ++ showIndent (i + 1) ++
      "MakeRef(closure_ptr);\n" ++ showIndent i  ++ "})"
  where
    translateCapturedVar :: CapturedVar -> Var
    translateCapturedVar (Weak x) = x
    translateCapturedVar (Strong x) = x
    translateCapturedVar (SelfCapture _) = "FromSelf(self)"

generate :: Int -> ClosureRefStatus -> HILExpr -> CodegenMonad String
generate _ _ HILUnit = return "Unit"
generate _ _ HILSelfRef = return "FromSelf(self)"
generate _ _ (HILBool   v) = return $ "Bool(" ++ map toLower (show v) ++ ")"
generate _ _ (HILInt    v) = return $ "Int(" ++ show v ++ ")"
generate _ _ (HILFloat  v) = return $ "Float(" ++ show v ++ ")"
generate _ _ (HILChar   v) = return $ "Char(" ++ show v ++ ")"
generate _ _ (HILString v) = return $ "String(" ++ show v ++ ")"
generate _ _ (HILVar    v) = return v
generate _ _ (HILGlobalVar  v) = return $ v ++ "()"
generate _ _ (HILClosureVar n) = return $ "refs[" ++ show n ++ "]"
generate i closureRefStatus (HILClosure x captures e) = do
  closureName <- freshClosureName
  generateClosure closureName x e
  return $ generateClosureValue i closureRefStatus False closureName captures
generate i closureRefStatus (HILSpine e (arg : args)) = do
  f <- generate i closureRefStatus e
  x <- generate i closureRefStatus arg
  aux ("((Closure*)std::get<std::shared_ptr<HeapValue>>(" ++ f ++ ".val).get())" ++ "->Call(" ++ x ++ ")") args
  where
    aux acc [] = return acc
    aux acc (a : as) = do
      x <- generate i closureRefStatus a
      aux ("((Closure*)std::get<std::shared_ptr<HeapValue>>(" ++ acc ++ ".val).get())" ++ "->CallNoCopy(" ++ x ++ ")") as
generate i closureRefStatus (HILDef v e) = do
  body <- generate (i + 2) closureRefStatus e
  return (showIndent i  ++   "StoreValue " ++ v ++ "() {\n" ++
          showIndent (i + 1) ++ "static std::optional<StoreValue> value;\n" ++
          showIndent (i + 1) ++ "if (!value.has_value()) {\n" ++
          showIndent (i + 2) ++    "value = " ++ body ++ ";\n" ++
          showIndent (i + 1) ++ "}\n\n" ++
          showIndent (i + 1) ++ "return value.value();\n" ++
          showIndent i  ++   "}")
generate i closureRefStatus (HILRec f (HILClosure x captures e1) e2) = do
  closureName <- freshClosureName
  generateClosure closureName x e1
  let e1' = generateClosureValue (i + 1) closureRefStatus True closureName captures
  e2' <- generate (i + 1) closureRefStatus e2
  return $ "({\n" ++
    showIndent (i + 1) ++ "StoreValue " ++ f ++ " = " ++ e1' ++ ";\n" ++
    showIndent (i + 1) ++ e2' ++ ";\n" ++
    showIndent i ++ "})"
generate i closureRefStatus (HILTuple es) = do
  es' <- mapM (generate i closureRefStatus) es
  return $ "MakeRef(std::make_shared<Tuple>(std::vector<StoreValue>({" ++ intercalate ", " es' ++ "})))"
generate i closureRefStatus (HILConstr name es) = do
  es' <- mapM (generate i closureRefStatus) es
  return $ "MakeRef(std::make_shared<Constr>(" ++ show name ++ ", std::vector<StoreValue>({" ++ intercalate ", " es' ++ "})))"
generate i closureRefStatus (HILPatternExpr e) = do
  e' <- generatePatternExpr (i + 1) closureRefStatus e
  return ("({\n" ++
          showIndent (i + 1) ++ "StoreValue result;\n" ++
          showIndent (i + 1) ++ "bool matched = false;\n" ++
          showIndent (i + 1) ++ e' ++ "\n" ++
          showIndent (i + 1) ++ "result;\n" ++
          showIndent i ++ "})")
generate i closureRefStatus (HILIf cond e1 e2) = do
  cond' <- generate i closureRefStatus cond
  e1' <- generate (i + 2) closureRefStatus e1
  e2' <- generate (i + 2) closureRefStatus e2
  return ("({\n" ++
          showIndent (i + 1) ++ "StoreValue result;\n" ++
          showIndent (i + 1) ++ "if (std::get<bool>(" ++ cond' ++ ".val))\n" ++
          showIndent (i + 2) ++   "result = " ++ e1' ++ ";\n" ++
          showIndent (i + 1) ++ "else\n" ++
          showIndent (i + 2) ++    "result = " ++ e2' ++ ";\n" ++
          showIndent (i + 1) ++ "result;\n" ++
          showIndent i ++ "})")
generate i closureRefStatus (HILLet x e1 e2) = do
  e1' <- generate (i + 1) closureRefStatus e1
  e2' <- generate (i + 1) closureRefStatus e2
  return $ "({\n" ++
    showIndent (i + 1) ++ "StoreValue " ++ x ++ " = " ++ e1' ++ ";\n" ++
    showIndent (i + 1) ++ e2' ++ ";\n" ++
    showIndent i ++ "})"
generate i closureRefStatus (HILBinOp (BinOp binOp) e1 e2) = do
  e1' <- generate i closureRefStatus e1
  e2' <- generate i closureRefStatus e2
  return $ binOpMap binOp ++ "(" ++ e1' ++ ", " ++ e2' ++ ")"
  where
    binOpMap "+"  = "op_plus"
    binOpMap "-"  = "op_minus"
    binOpMap "*"  = "op_mult"
    binOpMap "/"  = "op_div"
    binOpMap "%"  = "op_mod"
    binOpMap "+." = "op_plus_float"
    binOpMap "-." = "op_minus_float"
    binOpMap "*." = "op_mult_float"
    binOpMap "/." = "op_div_float"
    binOpMap "&&" = "op_and"
    binOpMap "||" = "op_or"
    binOpMap "^"  = "op_concat"
    binOpMap "==" = "op_eq"
    binOpMap "!=" = "op_neq"
    binOpMap "<=" = "op_le"
    binOpMap ">=" = "op_ge"
    binOpMap "<"  = "op_ls"
    binOpMap ">"  = "op_gt"
    binOpMap "@"  = "op_append_list"
    binOpMap "++" = "op_append_vec"
    binOpMap "."  = "op_compose"

generate i closureRefStatus (HILUnOp unOp e) = do
  e' <- generate i closureRefStatus e
  case unOp of
    UnOpPlus -> return e'
    UnOpMinus -> return $ "op_unary_minus(" ++ e' ++ ")"
    UnOpPlusFloat -> return e'
    UnOpMinusFloat -> return $ "op_unary_minus_float(" ++ e' ++ ")"
    UnOpNot -> return $ "op_unary_not(" ++ e' ++ ")"
generate i closureRefStatus (HILTry e catches) = do
  e' <- generate (i + 2) closureRefStatus e
  catches' <- generateCatch i closureRefStatus `mapM` catches
  return $ "({\n" ++
    showIndent (i + 1) ++ "StoreValue result;\n" ++
    showIndent (i + 1) ++ "try {\n" ++
    showIndent (i + 2) ++ "result = " ++ e' ++ ";\n" ++
    showIndent (i + 1) ++ "}" ++
    concat catches' ++ "\n" ++
    showIndent (i + 1) ++ "result;" ++
    showIndent i ++ "})"
generate i closureRefStatus (HILError e) = do
  e' <- generate (i + 1) closureRefStatus e
  return $ "({\n" ++
    showIndent (i + 1) ++ "StoreValue exc = " ++ e' ++ ";\n" ++
    showIndent (i + 1) ++ "throw RuntimeException(exc);\n" ++
    showIndent (i + 1) ++ "exc;\n" ++
    showIndent i ++ "})"

generate _ _ e = error $ show e

generateInspectableExpr :: HILInspectableExpr -> CodegenMonad String
generateInspectableExpr (HILInspectVar v) = return v
generateInspectableExpr (HILInspectElem k v) =
  return $ "((Tuple*)std::get<std::shared_ptr<HeapValue>>(" ++ v ++ ".val).get())->GetElem(" ++ show k ++ ")"

generatePatternExpr :: Int -> ClosureRefStatus -> HILPatternExpr -> CodegenMonad String
generatePatternExpr i closureRefStatus (HILMatchedExpr e) = do
  e' <- generate i closureRefStatus e
  return $ "matched = true;\n" ++
    showIndent i ++ "result = " ++ e' ++ ";"
generatePatternExpr i closureRefStatus (HILPtrnExprLet x e1 e2) = do
  e1' <- generateInspectableExpr e1
  e2' <- generatePatternExpr i closureRefStatus e2
  return $
    "StoreValue " ++ x ++ " = " ++ e1' ++ ";\n" ++
    showIndent i ++ e2'
generatePatternExpr _ _ (HILGetElem k v) =
  return $ "((Tuple*)std::get<std::shared_ptr<HeapValue>>(" ++ v ++ ".val).get())->GetElem(" ++ show k ++ ")"
generatePatternExpr i closureRefStatus (HILCase v branches) = do
  branches' <- mapM (generateBranch i closureRefStatus v) branches
  return $ intercalate " else " branches'
generatePatternExpr i closureRefStatus (HILCaseJoin e1 e2) = do
  e1' <- generatePatternExpr i closureRefStatus e1
  e2' <- generatePatternExpr (i + 1) closureRefStatus e2
  return $ e1' ++ "\n" ++
    showIndent i ++ "if (!matched) {\n" ++
    showIndent (i + 1) ++ e2' ++ "\n" ++
    showIndent i ++ "}"

generateBranch :: Int -> ClosureRefStatus -> Var -> HILBranch -> CodegenMonad String
generateBranch i closureRefStatus v (ptrn, e) = do
  e' <-  generatePatternExpr (i + 1) closureRefStatus e
  return ("if (" ++ generatePatternCheck v ptrn ++ ") {\n" ++
          showIndent (i + 1) ++ e' ++ "\n" ++
          showIndent i ++ "}")

generatePatternCheck :: Var -> HILPattern -> String
generatePatternCheck _ HILPUnit = "true"
generatePatternCheck v (HILPBool   b) = "std::get<bool>(" ++ v ++ ".val) == " ++ map toLower (show b)
generatePatternCheck v (HILPInt    n) = "std::get<int64_t>(" ++ v ++ ".val) == " ++ show n
generatePatternCheck v (HILPFloat  x) = "std::get<long double>(" ++ v ++ ".val) == " ++ show x
generatePatternCheck v (HILPChar   c) = "std::get<char>(" ++ v ++ ".val) == " ++ show c
generatePatternCheck v (HILPString str) = "std::get<std::string>(" ++ v ++ ".val) == " ++ show str
generatePatternCheck v (HILPConstr name) =
  "((Constr*)std::get<std::shared_ptr<HeapValue>>(" ++ v ++ ".val).get())->GetName() == " ++ show name

generateCatch :: Int -> ClosureRefStatus -> HILCatch -> CodegenMonad String
generateCatch i closureRefStatus (HILBestraferException exc message, e) = do
  e' <- generate (i + 2) closureRefStatus e
  return $ " catch (" ++ generateExc exc ++ "& exc) {\n" ++
    generateMsg message ++
    showIndent (i + 2) ++ "result = " ++ e' ++ ";\n" ++
    showIndent (i + 1) ++ "}"
  where
    generateExc "ArithmeticException" = "ArithmeticException"
    generateExc "RuntimeException" = "RuntimeException"
    generateExc "IOException" = "std::ios_base::failure"
    generateExc _ = "std::exception"

    generateMsg Nothing = ""
    generateMsg (Just m) = showIndent (i + 2) ++ "StoreValue " ++ m ++ " = String(exc.what());\n"

closureTemplate :: String -> String -> String -> String -> String
closureTemplate name arg callBody callNoCopyBody =
  "struct " ++ name ++ " : public Closure {\n" ++
  "  StoreValue Call(const StoreValue& " ++ arg ++ ") {\n" ++
  "    return " ++ callBody ++ ";\n" ++
  "  }\n\n" ++
  "  StoreValue CallNoCopy(const StoreValue& " ++ arg ++ ") {\n" ++
  "    return " ++ callNoCopyBody ++ ";\n" ++
  "  }\n\n" ++
  "  " ++ name ++ "() : Closure() {}\n" ++
  "  explicit " ++ name ++ "(std::vector<StoreValue> refs) : Closure(std::move(refs)) {}\n" ++
  "};"

generateClosure :: Var -> Var -> HILExpr -> CodegenMonad ()
generateClosure name arg (HILClosure x captures e) =  do
  closureName <- freshClosureName
  generateClosure closureName x e
  let callBody = generateClosureValue 2 Copy False closureName captures
  let callNoCopyBody = generateClosureValue 2 NoCopy False closureName captures
  modify $ over closures (closureTemplate name arg callBody callNoCopyBody :)
generateClosure name arg e = do
  body <- generate 2 Copy e
  modify $ over closures (closureTemplate name arg body body :)
