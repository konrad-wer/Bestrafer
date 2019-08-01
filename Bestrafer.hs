
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

readArgs :: [a] -> Maybe [a]
readArgs [] = Nothing
readArgs xs = return xs

main :: IO ()
main = do
  args <- getArgs
  case readArgs args of
    Nothing -> putStrLn "Please provide input file name(s)!"
    Just fileNames -> do
      stdlib <- readFile "stdlib.br"
      let (Right stdlibBlocks) = parseProgram "stdlib.br" stdlib
      inputs <- mapM readFile fileNames
      case zipWithM parseProgram fileNames inputs of
        Left err -> putStr $ errorBundlePretty err
        Right blocks -> case buildAST (stdlibBlocks ++ concat blocks) of
          Left err -> print err
          Right (prog, cContext, gDefs, fContext) ->
            let startState = TypecheckerState { _freshVarNum = 0, _constrContext = cContext, _gadtDefs = gDefs, _funContext = fContext } in
            case iterM (void . flip evalStateT startState . inferExpr []) prog of
              Right () -> do
                          void $ eval prog cContext
                          return ()
              Left err -> print  err
