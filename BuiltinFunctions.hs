module BuiltinFunctions where

import AST
import EvalUtils
import Control.Monad
import Control.Monad.State
import Control.Exception

unPlusInt :: Value
unPlusInt = FunValue return

unMinusInt :: Value
unMinusInt = FunValue (\(IntValue x) -> return $ IntValue (-x))

unPlusFloat :: Value
unPlusFloat = FunValue return

unMinusFloat :: Value
unMinusFloat = FunValue (\(FloatValue x) -> return $ FloatValue (-x))

notBool :: Value
notBool = FunValue (\(BoolValue b) -> return . BoolValue $ not b)

addInt :: Value
addInt = FunValue (\(IntValue x) -> return (FunValue (\(IntValue y) -> return $ IntValue (x + y))))

subInt :: Value
subInt = FunValue (\(IntValue x) -> return (FunValue (\(IntValue y) -> return $ IntValue (x - y))))

multInt :: Value
multInt = FunValue (\(IntValue x) -> return (FunValue (\(IntValue y) -> return $ IntValue (x * y))))

divInt :: Value
divInt = FunValue (\(IntValue x) -> return (FunValue (\(IntValue y) ->
  if y /= 0 then
    return $ IntValue (x `div` y)
  else
    liftIO $ throw DivideByZero)))

modInt :: Value
modInt = FunValue (\(IntValue x) -> return (FunValue (\(IntValue y) ->
  if y /= 0 then
    return $ IntValue (x `mod` y)
    else
      liftIO $ throw DivideByZero)))

addFloat :: Value
addFloat = FunValue (\(FloatValue x) -> return (FunValue (\(FloatValue y) -> return $ FloatValue (x + y))))

subFloat :: Value
subFloat = FunValue (\(FloatValue x) -> return (FunValue (\(FloatValue y) -> return $ FloatValue (x - y))))

multFloat :: Value
multFloat = FunValue (\(FloatValue x) -> return (FunValue (\(FloatValue y) -> return $ FloatValue (x * y))))

divFloat :: Value
divFloat = FunValue (\(FloatValue x) -> return (FunValue (\(FloatValue y) -> return $ FloatValue (x / y))))

andBool :: Value
andBool = FunValue (\(BoolValue x) -> return (FunValue (\(BoolValue y) -> return $ BoolValue (x && y))))

orBool :: Value
orBool = FunValue (\(BoolValue x) -> return (FunValue (\(BoolValue y) -> return $ BoolValue (x || y))))

equal :: Value
equal = FunValue (\x -> return (FunValue (\y -> return $ BoolValue (x == y))))

notEqual :: Value
notEqual = FunValue (\x -> return (FunValue (\y -> return $ BoolValue (x /= y))))

less :: Value
less = FunValue (\x -> return (FunValue (\y -> return $ BoolValue (x < y))))

greater :: Value
greater = FunValue (\x -> return (FunValue (\y -> return $ BoolValue (x > y))))

lessOrEqual :: Value
lessOrEqual = FunValue (\x -> return (FunValue (\y -> return $ BoolValue (x <= y))))

greaterOrEqual :: Value
greaterOrEqual = FunValue (\x -> return (FunValue (\y -> return $ BoolValue (x >= y))))

concatStr :: Value
concatStr = FunValue (\(StringValue x) -> return (FunValue (\(StringValue y) -> return $ StringValue (x ++ y))))

concatVec :: Value
concatVec = FunValue (\(VecValue x) -> return (FunValue (\(VecValue y) -> return $ VecValue (x ++ y))))

concatList :: Value
concatList = FunValue (\(ListValue x) -> return (FunValue (\(ListValue y) -> return $ ListValue (x ++ y))))

compose :: Value
compose = FunValue (\(FunValue f) -> return (FunValue (\(FunValue g) -> return $ FunValue (f <=< g))))

pipe :: Value
pipe = FunValue (\x -> return (FunValue (\(FunValue f) -> f x)))

bfrReadFile :: Value
bfrReadFile = FunValue (\(StringValue x) -> lift (StringValue <$> readFile x))

bfrWriteFile :: Value
bfrWriteFile = FunValue (\(StringValue x) -> return (FunValue (\(StringValue y) -> lift (writeFile x y >> return UnitValue))))

bfrAppendFile :: Value
bfrAppendFile = FunValue (\(StringValue x) -> return (FunValue (\(StringValue y) -> lift (appendFile x y >> return UnitValue))))

bfrPutChar :: Value
bfrPutChar = FunValue (\(CharValue x) -> lift (putChar x >> return UnitValue))

bfrPutStr :: Value
bfrPutStr = FunValue (\(StringValue x) -> lift (putStr x >> return UnitValue))

bfrPutStrLn :: Value
bfrPutStrLn = FunValue (\(StringValue x) -> lift (putStrLn x >> return UnitValue))

bfrPrint :: Value
bfrPrint = FunValue (\x -> lift (print x >> return UnitValue))

bfrGetChar :: Value
bfrGetChar = FunValue (\UnitValue -> lift (CharValue <$> getChar))

bfrGetLine :: Value
bfrGetLine = FunValue (\UnitValue -> lift (StringValue <$> getLine))

bfrReadLnBool :: Value
bfrReadLnBool = FunValue (\UnitValue -> lift (BoolValue <$> readLn))

bfrReadLnInt :: Value
bfrReadLnInt = FunValue (\UnitValue -> lift (IntValue <$> readLn))

bfrReadLnFloat :: Value
bfrReadLnFloat = FunValue (\UnitValue -> lift (FloatValue <$> readLn))

builtinFunctions :: [(Var, GlobalContextEntry)]
builtinFunctions =
  [
    ("!u", Evaluated notBool),
    ("+u", Evaluated unPlusInt),
    ("-u", Evaluated unMinusInt),
    ("+.u", Evaluated unPlusFloat),
    ("-.u", Evaluated unMinusFloat),
    ("+", Evaluated addInt),
    ("-", Evaluated subInt),
    ("*", Evaluated multInt),
    ("/", Evaluated divInt),
    ("%", Evaluated modInt),
    ("+.", Evaluated addFloat),
    ("-.", Evaluated subFloat),
    ("*.", Evaluated multFloat),
    ("/.", Evaluated divFloat),
    ("&&", Evaluated andBool),
    ("||", Evaluated orBool),
    ("^",  Evaluated concatStr),
    ("==", Evaluated equal),
    ("!=", Evaluated notEqual),
    ("<=", Evaluated lessOrEqual),
    (">=", Evaluated greaterOrEqual),
    ("<",  Evaluated less),
    (">",  Evaluated greater),
    ("@",  Evaluated concatList),
    ("++", Evaluated concatVec),
    (".",  Evaluated compose),
    ("|>", Evaluated pipe),
    ("readFile", Evaluated bfrReadFile),
    ("writeFile", Evaluated bfrWriteFile),
    ("appendFile", Evaluated bfrAppendFile),
    ("putChar", Evaluated bfrPutChar),
    ("putStr", Evaluated bfrPutStr),
    ("putStrLn", Evaluated bfrPutStrLn),
    ("printBool", Evaluated bfrPrint),
    ("printInt", Evaluated bfrPrint),
    ("printFloat", Evaluated bfrPrint),
    ("getChar", Evaluated bfrGetChar),
    ("getLine", Evaluated bfrGetLine),
    ("readLnBool", Evaluated bfrReadLnBool),
    ("readLnInt", Evaluated bfrReadLnInt),
    ("readLnFloat", Evaluated bfrReadLnFloat)
  ]
