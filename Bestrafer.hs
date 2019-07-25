
import Parser
import ASTBuilder
import Text.Megaparsec
import System.Environment
import Typechecker
import TypecheckerUtils
import CommonUtils
import Eval
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
              Right () -> do
                          res <- eval prog cContext
                          print res
              Left err -> print  err-- print err
