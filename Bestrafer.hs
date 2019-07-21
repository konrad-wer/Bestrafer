
import Parser
import AST
import ASTBuilder
import Text.Megaparsec
import System.Environment
import Typechecker
import TypecheckerUtils
import CommonUtils
import Control.Monad (void)
import Control.Monad.State

readArgs :: [a] -> Maybe a
readArgs [] = Nothing
readArgs (x : _) = return x

main :: IO ()
main = do
  args <- getArgs
  case readArgs args of
    Nothing -> putStrLn "Please provide input file name!"
    Just fileName -> do
      input <- readFile fileName
      case parseProgram fileName input of
        Left err -> putStr $ errorBundlePretty err
        Right blocks -> case buildAST blocks of
          Left err -> print err
          Right (prog, cContext, gDefs, fContext) ->
            let startState = TypecheckerState { _freshVarNum = 0, _constrContext = cContext, _gadtDefs = gDefs, _funContext = fContext } in
            case iterM (void . flip evalStateT startState . inferExpr []) prog of
              Right () -> putStrLn "Deine Größe macht mich klein\nDu darfst mein Bestrafer sein"
              Left err -> print  err-- print err

depth :: Expr p -> Integer
depth (EBinOp _ _ e1 e2) = max (depth e1) (depth e2) + 1
depth _ = 0

hidePos :: [ProgramBlock p] -> [ProgramBlock ()]
hidePos = map hidePosBlock

hidePosBlock :: ProgramBlock p -> ProgramBlock ()
hidePosBlock (FunTypeAnnot _ x t) = FunTypeAnnot () x t
hidePosBlock (FunDefCase _ x ps e) = FunDefCase () x (map hidePosPat ps) $ hidePosExpr e
hidePosBlock (GADTDef _  name params constructors) = GADTDef () name params $ map hidePosConstr constructors

hidePosConstr :: ConstrDef p -> ConstrDef ()
hidePosConstr (ConstrDef _ name t) = ConstrDef () name t

hidePosExpr :: Expr p -> Expr ()
hidePosExpr (EVar _ v) = EVar () v
hidePosExpr (EUnit _) = EUnit ()
hidePosExpr (EBool _ x) = EBool () x
hidePosExpr (EInt _ x) = EInt () x
hidePosExpr (EFloat _ x) = EFloat () x
hidePosExpr (EChar _ x) = EChar () x
hidePosExpr (EString _ x) = EString () x
hidePosExpr (ELambda _ x e) = ELambda () x $ hidePosExpr e
hidePosExpr (ESpine _ e s) = ESpine () (hidePosExpr e) $ map hidePosExpr s
hidePosExpr (ERec _ x e) = ERec () x $ hidePosExpr e
hidePosExpr (EAnnot _ e t) = EAnnot () (hidePosExpr e) t
hidePosExpr (ETuple _ es l) = ETuple () (map hidePosExpr es) l
hidePosExpr (EConstr _ c es) = EConstr () c $ map hidePosExpr es
hidePosExpr (ECase _ e bs) = ECase () (hidePosExpr e) $ map hidePosBranch bs
hidePosExpr (ENil _) = ENil ()
hidePosExpr (ECons _ e1 e2) = ECons () (hidePosExpr e1) (hidePosExpr e2)
hidePosExpr (EIf _ e1 e2 e3) = EIf () (hidePosExpr e1) (hidePosExpr e2) (hidePosExpr e3)
hidePosExpr (ELet _ x e1 e2) = ELet () x (hidePosExpr e1) (hidePosExpr e2)
hidePosExpr (EBinOp _ op e1 e2) = EBinOp () op (hidePosExpr e1) (hidePosExpr e2)
hidePosExpr (EUnOp _ op e) = EUnOp () op (hidePosExpr e)

hidePosBranch :: Branch p -> Branch ()
hidePosBranch (ps, e, _) = (map hidePosPat ps, hidePosExpr e, ())

hidePosPat :: Pattern p -> Pattern ()
hidePosPat (PWild _) = PWild ()
hidePosPat (PVar _ v) = PVar () v
hidePosPat (PUnit _) = PUnit ()
hidePosPat (PBool _ x) = PBool () x
hidePosPat (PInt _ x) = PInt () x
hidePosPat (PFloat _ x) = PFloat () x
hidePosPat (PChar _ x) = PChar () x
hidePosPat (PString _ x) = PString () x
hidePosPat (PTuple _ es l) = PTuple () (map hidePosPat es) l
hidePosPat (PConstr _ c es) = PConstr () c $ map hidePosPat es
hidePosPat (PNil _) = PNil ()
hidePosPat (PCons _ e1 e2) = PCons () (hidePosPat e1) (hidePosPat e2)
