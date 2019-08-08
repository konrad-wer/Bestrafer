module BuiltinFunctions (builtinFunctions, builtinFunctionsTypes) where

import AST
import EvalUtils
import Control.Monad
import Control.Monad.State
import Control.Exception
import Data.Char
import Text.Read (readMaybe)

operatorsTypes :: [(Var, Type)]
operatorsTypes =
  [
    ("!u", TArrow TBool TBool),
    ("+u", TArrow TInt TInt),
    ("-u", TArrow TInt TInt),
    ("+.u", TArrow TFloat TFloat),
    ("-.u", TArrow TFloat TFloat),
    ("+", TArrow TInt $ TArrow TInt TInt),
    ("-", TArrow TInt $ TArrow TInt TInt),
    ("*", TArrow TInt $ TArrow TInt TInt),
    ("/", TArrow TInt $ TArrow TInt TInt),
    ("%", TArrow TInt $ TArrow TInt TInt),
    ("+.", TArrow TFloat $ TArrow TFloat TFloat),
    ("-.", TArrow TFloat $ TArrow TFloat TFloat),
    ("*.", TArrow TFloat $ TArrow TFloat TFloat),
    ("/.", TArrow TFloat $ TArrow TFloat TFloat),
    ("&&", TArrow TBool $ TArrow TBool TBool),
    ("||", TArrow TBool $ TArrow TBool TBool),
    ("^",  TArrow TString $ TArrow TString TString),
    ("==", TUniversal (UTypeVar "a") KStar (TArrow (TUVar $ UTypeVar "a") $ TArrow (TUVar $ UTypeVar "a") TBool)),
    ("!=", TUniversal (UTypeVar "a") KStar (TArrow (TUVar $ UTypeVar "a") $ TArrow (TUVar $ UTypeVar "a") TBool)),
    ("<=", TUniversal (UTypeVar "a") KStar (TArrow (TUVar $ UTypeVar "a") $ TArrow (TUVar $ UTypeVar "a") TBool)),
    (">=", TUniversal (UTypeVar "a") KStar (TArrow (TUVar $ UTypeVar "a") $ TArrow (TUVar $ UTypeVar "a") TBool)),
    ("<",  TUniversal (UTypeVar "a") KStar (TArrow (TUVar $ UTypeVar "a") $ TArrow (TUVar $ UTypeVar "a") TBool)),
    (">",  TUniversal (UTypeVar "a") KStar (TArrow (TUVar $ UTypeVar "a") $ TArrow (TUVar $ UTypeVar "a") TBool)),
    ("@", TUniversal (UTypeVar "a") KStar $ TArrow (TGADT "List" [ParameterType $ TUVar $ UTypeVar "a"]) $ TArrow
    (TGADT "List" [ParameterType $ TUVar $ UTypeVar "a"]) (TGADT "List" [ParameterType $ TUVar $ UTypeVar "a"])),
    ("++", TUniversal (UTypeVar "a") KStar . TUniversal (UTypeVar "n1") KNat . TUniversal (UTypeVar "n2") KNat $
    TArrow (TGADT "Vec" [ParameterMonotype $ MUVar $ UTypeVar "n1", ParameterType $ TUVar $ UTypeVar "a"]) $ TArrow
    (TGADT "Vec" [ParameterMonotype $ MUVar $ UTypeVar "n2", ParameterType $ TUVar $ UTypeVar "a"])
    (TExistential (UTypeVar "m") KNat $ TGADT "Vec" [ParameterMonotype $ MUVar $ UTypeVar "m", ParameterType $ TUVar $ UTypeVar "a"])),
    (".", TUniversal (UTypeVar "a") KStar . TUniversal (UTypeVar "b") KStar . TUniversal (UTypeVar "c") KStar $
    TArrow (TArrow (TUVar $ UTypeVar "b") (TUVar $ UTypeVar "c")) $ TArrow (TArrow (TUVar $ UTypeVar "a") (TUVar $ UTypeVar "b"))
    (TArrow (TUVar $ UTypeVar "a") (TUVar $ UTypeVar "c"))),
    ("|>",  TUniversal (UTypeVar "a") KStar . TUniversal (UTypeVar "b") KStar . TArrow (TUVar $ UTypeVar "a") $
    TArrow (TArrow (TUVar $ UTypeVar "a") (TUVar $ UTypeVar "b")) (TUVar $ UTypeVar "b")),
    ("<|",  TUniversal (UTypeVar "a") KStar . TUniversal (UTypeVar "b") KStar . TArrow
    (TArrow (TUVar $ UTypeVar "a") (TUVar $ UTypeVar "b")) $ TArrow (TUVar $ UTypeVar "a") (TUVar $ UTypeVar "b"))
  ]

ioFunctionsTypes :: [(Var, Type)]
ioFunctionsTypes =
  [
    ("readFile", TArrow TString TString),
    ("writeFile", TArrow TString (TArrow TString TUnit)),
    ("appendFile", TArrow TString (TArrow TString TUnit)),
    ("putChar", TArrow TChar TUnit),
    ("putStr", TArrow TString TUnit),
    ("putStrLn", TArrow TString TUnit),
    ("printBool", TArrow TBool TUnit),
    ("printInt", TArrow TInt TUnit),
    ("printFloat", TArrow TFloat TUnit),
    ("getChar", TArrow TUnit TChar),
    ("getLine", TArrow TUnit TString),
    ("readLnBool", TArrow TUnit TBool),
    ("readLnInt", TArrow TUnit TInt),
    ("readLnFloat", TArrow TUnit TFloat)
  ]

conversionFunctionsTypes :: [(Var, Type)]
conversionFunctionsTypes =
  [
    ("stringToList", TArrow TString (TGADT "List" [ParameterType TChar])),
    ("stringFromList", TArrow (TGADT "List" [ParameterType TChar]) TString),
    ("intToFloat", TArrow TInt TFloat),
    ("floatToInt", TArrow TFloat TInt),
    ("intToString", TArrow TInt TString),
    ("floatToString", TArrow TFloat TString),
    ("boolToString", TArrow TBool TString),
    ("charToString", TArrow TChar TString),
    ("ord", TArrow TChar TInt),
    ("chr", TArrow TInt TChar),
    ("intFromString", TArrow TString TInt),
    ("floatFromString", TArrow TString TFloat)
  ]

builtinFunctionsTypes :: [(Var, Type)]
builtinFunctionsTypes = operatorsTypes ++ ioFunctionsTypes ++ conversionFunctionsTypes

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
pipe = FunValue (\x -> return $ FunValue (\(FunValue f) -> f x))

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

operators :: [(Var, DefinitionValue)]
operators =
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
    ("<|", Evaluated $ FunValue return)
  ]

ioFunctions :: [(Var, DefinitionValue)]
ioFunctions =
  [
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

chrBestrafer :: Value
chrBestrafer = FunValue (\(IntValue x) ->
  if x <= 0x10FFFF && x >= 0 then
    return . CharValue . chr $ fromInteger x
  else
    liftIO . throw $ CustomException "chr: domain error")

intFromString :: Value
intFromString =
  FunValue (\(StringValue s) ->  case readMaybe s of
    Nothing -> liftIO . throw $ CustomException "intFromString: given string is not an int"
    Just x -> return . IntValue $ x)

floatFromString :: Value
floatFromString =
  FunValue (\(StringValue s) ->  case readMaybe s of
    Nothing -> liftIO . throw $ CustomException "floatFromString: given string is not a float"
    Just x -> return . FloatValue $ x)

conversionFunctions :: [(Var, DefinitionValue)]
conversionFunctions =
  [
    ("stringToList",  Evaluated $ FunValue (\(StringValue s) -> return . ListValue $ map CharValue s)),
    ("stringFromList",  Evaluated $ FunValue (\(ListValue s)   -> return . StringValue $ map (\(CharValue c) -> c) s)),
    ("intToFloat",    Evaluated $ FunValue (\(IntValue x)    -> return . FloatValue $ fromInteger x)),
    ("floatToInt",    Evaluated $ FunValue (\(FloatValue x)  -> return . IntValue $ truncate x)),
    ("intToString",   Evaluated $ FunValue (\(IntValue x)    -> return . StringValue $ show x)),
    ("floatToString", Evaluated $ FunValue (\(FloatValue x)  -> return . StringValue $ show x)),
    ("boolToString",  Evaluated $ FunValue (\(BoolValue x)   -> return . StringValue $ show x)),
    ("charToString",  Evaluated $ FunValue (\(CharValue x)   -> return . StringValue $ return x)),
    ("ord", Evaluated $ FunValue (\(CharValue x) -> return . IntValue . fromIntegral $ ord x)),
    ("chr", Evaluated chrBestrafer),
    ("intFromString",   Evaluated intFromString),
    ("floatFromString", Evaluated floatFromString)
  ]

builtinFunctions :: [(Var, DefinitionValue)]
builtinFunctions = operators ++ ioFunctions ++ conversionFunctions
