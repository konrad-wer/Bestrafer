
module Parser (parseProgram) where

-- "You've never heard of the Millennium Falcon?
-- …It's the ship that made the Kessel Run in less than 0.000012 megaParsecs."

import PreAST
import AST
import Control.Monad (void)
import Control.Monad.Combinators.Expr
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space space1 lineCmnt blockCmnt
  where
    lineCmnt  = L.skipLineComment "//"
    blockCmnt = L.skipBlockComment "/*" "*/"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

symbolWithPos :: String -> Parser (SourcePos, String)
symbolWithPos x = do
  pos <- getSourcePos
  sym <- symbol x
  return (pos, sym)

dot :: Parser String
dot = symbol "."

comma :: Parser String
comma = symbol ","

colon :: Parser String
colon = symbol ":"

unsignedInteger :: Parser Integer
unsignedInteger = lexeme L.decimal

unsignedFloat :: Parser Double
unsignedFloat = lexeme L.float

integer :: Parser Integer
integer = L.signed sc unsignedInteger

float :: Parser Double
float = L.signed sc unsignedFloat

charLiteral :: Parser Char
charLiteral = lexeme $ between (char '\'') (char '\'') L.charLiteral

stringLiteral :: Parser String
stringLiteral = lexeme $ char '\"' *> manyTill L.charLiteral (char '\"')

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

rword :: String -> Parser ()
rword w = (lexeme . try) (string w *> notFollowedBy alphaNumChar)

rws :: [String]
rws = ["let", "def", "data", "where", "if", "then", "else", "in",
       "False", "True", "exists", "forall", "try", "catch", "of",
       "Bool", "Int", "Float", "Char", "String", "N", "S", "λ", "case"]

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p = (:) <$> lowerChar <*> many (alphaNumChar <|> char '_')
    check x
      | x `elem` rws = fail $ "keyword " ++ show x ++ " cannot be an identifier"
      | otherwise = return x

upperIdentifier :: Parser String
upperIdentifier = (lexeme . try) (p >>= check)
  where
    p = (:) <$> upperChar <*> many alphaNumChar
    check x
      | x `elem` rws = fail $ "keyword " ++ show x ++ " cannot be an identifier"
      | otherwise = return x

gadtParamIdentifier :: Parser String
gadtParamIdentifier = (lexeme . try) ((:) <$> char '\'' <*> many alphaNumChar)

typeParser :: Parser Type
typeParser = makeExprParser tTerm [[InfixR (TArrow <$ symbol "->")]]

tTerm :: Parser Type
tTerm =
  try tGADT <|>
  tSimple <|>
  tQuantifier

tQuantifier :: Parser Type
tQuantifier = do
  q <- ((rword "∀" <|> rword "forall") >> return TUniversal) <|> ((rword "∃" <|> rword "exists") >> return TExistential)
  varAndKinds <- sepBy1 kindDef comma
  void dot
  t <- typeParser
  return $ buildQuantifier q varAndKinds t

buildQuantifier :: (UTypeVar -> Kind -> Type -> Type)-> [(Var, Kind)] -> Type -> Type
buildQuantifier _ [] t = t
buildQuantifier f ((x, k) : vs) t =
  f (UTypeVar x) k $ buildQuantifier f vs t

kind :: Parser Kind
kind = (rword "N" >> return KNat) <|> (symbol "*" >> return KStar)

kindDef :: Parser (Var, Kind)
kindDef = do
  var <- identifier
  void colon
  k <- kind
  return (var, k)

tProduct :: Parser Type
tProduct = parens
  (do
   ts <- sepBy1 typeParser comma
   case ts of
     [t] -> return t
     _ -> return $ TProduct ts $ length ts)

tSimple :: Parser Type
tSimple =
  (symbol "()" >> return TUnit) <|>
  (rword "Bool" >> return TBool) <|>
  (rword "Int" >> return TInt) <|>
  (rword "Float" >> return TFloat) <|>
  (rword "Char" >> return TChar) <|>
  (rword "String" >> return TString) <|>
  (TUVar . UTypeVar <$> identifier) <|>
  (TGADT <$> upperIdentifier <*> pure []) <|>
  try tProduct <|>
  try tImp <|>
  tAnd

tGADT :: Parser Type
tGADT = do
  name <- upperIdentifier
  args <- some (try (ParameterMonotype <$> mSimple) <|> (ParameterType <$> tSimple))
  return $ TGADT name args

tAnd :: Parser Type
tAnd =  parens (do
  t <- typeParser
  void $ symbol "^"
  prop <- propParser
  return $ TAnd t prop)

tImp :: Parser Type
tImp = parens (do
  prop <- propParser
  void $ symbol "=>"
  t <- typeParser
  return $ TImp prop t)

propParser :: Parser Proposition
propParser = do
  m1 <- monotypeParser
  void $ symbol "="
  m2 <- monotypeParser
  return (m1, m2)

monotypeParser :: Parser Monotype
monotypeParser = makeExprParser mTerm [[InfixR (MArrow <$ symbol "->")]]

mTerm :: Parser Monotype
mTerm =
  try mGADT <|>
  mSimple <|>
  mSucc

mNat :: Parser Monotype
mNat = natFromInteger <$> unsignedInteger

mSucc :: Parser Monotype
mSucc = rword "S" >> (MSucc <$> monotypeParser)

natFromInteger :: Integer -> Monotype
natFromInteger 0 = MZero
natFromInteger n = MSucc $ natFromInteger (n - 1)

mProduct :: Parser Monotype
mProduct = parens
  (do
   ms <- sepBy1 monotypeParser comma
   case ms of
     [m] -> return m
     _ -> return $ MProduct ms $ length ms)

mSimple :: Parser Monotype
mSimple =
  (symbol "()" >> return MUnit) <|>
  (rword "Bool" >> return MBool) <|>
  (rword "Int" >> return MInt) <|>
  (rword "Float" >> return MFloat) <|>
  (rword "Char" >> return MChar) <|>
  (rword "String" >> return MString) <|>
  (MUVar . UTypeVar <$> identifier) <|>
  (MGADT <$> upperIdentifier <*> pure []) <|>
  mProduct <|>
  mNat

mGADT :: Parser Monotype
mGADT = do
  name <- upperIdentifier
  args <- some mSimple
  return $ MGADT name args

typeTemplateParser :: Parser PreTypeTemplate
typeTemplateParser = makeExprParser ttTerm [[InfixR (PTTArrow <$ symbol "->")]]

ttTerm :: Parser PreTypeTemplate
ttTerm =
  try ttGADT <|>
  ttSimple <|>
  ttQuantifier

ttQuantifier :: Parser PreTypeTemplate
ttQuantifier = do
  q <- ((rword "∀" <|> rword "forall") >> return PTTUniversal) <|> ((rword "∃" <|> rword "exists") >> return PTTExistential)
  varAndKinds <- sepBy1 kindDef comma
  void dot
  t <- typeTemplateParser
  return $ buildQuantifierTemplate q varAndKinds t

buildQuantifierTemplate :: (UTypeVar -> Kind -> PreTypeTemplate -> PreTypeTemplate)-> [(Var, Kind)] -> PreTypeTemplate -> PreTypeTemplate
buildQuantifierTemplate _ [] t = t
buildQuantifierTemplate f ((x, k) : vs) t =
  f (UTypeVar x) k $ buildQuantifierTemplate f vs t

ttProduct :: Parser PreTypeTemplate
ttProduct = parens
  (do
   ts <- sepBy1 typeTemplateParser comma
   case ts of
     [t] -> return t
     _ -> return $ PTTProduct ts $ length ts)

ttSimple :: Parser PreTypeTemplate
ttSimple =
  (symbol "()" >> return PTTUnit) <|>
  (rword "Bool" >> return PTTBool) <|>
  (rword "Int" >> return PTTInt) <|>
  (rword "Float" >> return PTTFloat) <|>
  (rword "Char" >> return PTTChar) <|>
  (rword "String" >> return PTTString) <|>
  (PTTUVar . UTypeVar <$> identifier) <|>
  (PTTParam <$> gadtParamIdentifier) <|>
  (PTTGADT <$> upperIdentifier <*> pure []) <|>
  try ttProduct <|>
  try ttImp <|>
  ttAnd

ttGADT :: Parser PreTypeTemplate
ttGADT = do
  name <- upperIdentifier
  args <- some (try (ParameterMonotypePT <$> mtSimple) <|> (ParameterTypePT <$> ttSimple))
  return $ PTTGADT name args

ttAnd :: Parser PreTypeTemplate
ttAnd =  parens (do
  t <- typeTemplateParser
  void $ symbol "^"
  prop <- propTemplateParser
  return $ PTTAnd t prop)

ttImp :: Parser PreTypeTemplate
ttImp = parens (do
  prop <- propTemplateParser
  void $ symbol "=>"
  t <- typeTemplateParser
  return $ PTTImp prop t)

propTemplateParser :: Parser PropositionTemplate
propTemplateParser = do
  m1 <- monotypeTemplateParser
  void $ symbol "="
  m2 <- monotypeTemplateParser
  return (m1, m2)

monotypeTemplateParser :: Parser MonotypeTemplate
monotypeTemplateParser = makeExprParser mtTerm [[InfixR (MTArrow <$ symbol "->")]]

mtTerm :: Parser MonotypeTemplate
mtTerm =
  try mtGADT <|>
  mtSimple <|>
  mtSucc

mtNat :: Parser MonotypeTemplate
mtNat = natTemplateFromInteger <$> unsignedInteger

mtSucc :: Parser MonotypeTemplate
mtSucc = rword "S" >> (MTSucc <$> monotypeTemplateParser)

natTemplateFromInteger :: Integer -> MonotypeTemplate
natTemplateFromInteger 0 = MTZero
natTemplateFromInteger n = MTSucc $ natTemplateFromInteger (n - 1)

mtProduct :: Parser MonotypeTemplate
mtProduct = parens
  (do
   ms <- sepBy1 monotypeTemplateParser comma
   case ms of
     [m] -> return m
     _ -> return $ MTProduct ms $ length ms)

mtSimple :: Parser MonotypeTemplate
mtSimple =
  (symbol "()" >> return MTUnit) <|>
  (rword "Bool" >> return MTBool) <|>
  (rword "Int" >> return MTInt) <|>
  (rword "Float" >> return MTFloat) <|>
  (rword "Char" >> return MTChar) <|>
  (rword "String" >> return MTString) <|>
  (MTUVar . UTypeVar <$> identifier) <|>
  (MTGADT <$> upperIdentifier <*> pure []) <|>
  mtProduct <|>
  mtNat

mtGADT :: Parser MonotypeTemplate
mtGADT = do
  name <- upperIdentifier
  args <- some mtSimple
  return $ MTGADT name args

binOpParser :: String -> Parser (Expr SourcePos -> Expr SourcePos -> Expr SourcePos)
binOpParser x = do
  pos <- getSourcePos
  op <- symbol x
  return $ EBinOp pos (BinOp op)

consParser :: Parser (Expr SourcePos -> Expr SourcePos -> Expr SourcePos)
consParser = do
  pos <- getSourcePos
  (lexeme . try) (char ':' *> notFollowedBy (char ':'))
  return $ ECons pos

plusParser :: Parser (Expr SourcePos -> Expr SourcePos -> Expr SourcePos)
plusParser = do
  pos <- getSourcePos
  (lexeme . try) (char '+' *> notFollowedBy (char '+'))
  return $ EBinOp pos (BinOp "+")

infixFunParser :: Parser (Expr SourcePos -> Expr SourcePos -> Expr SourcePos)
infixFunParser = do
  pos <- getSourcePos
  op <- between (symbol "`") (symbol "`") identifier
  return $ EBinOp pos (BinOp op)

operators :: [[Operator Parser (Expr SourcePos)]]
operators =
  [[Prefix (flip EUnOp UnOpPlusFloat . fst <$> symbolWithPos "+."),
    Prefix (flip EUnOp UnOpMinusFloat . fst <$> symbolWithPos "-."),
    Prefix (flip EUnOp UnOpPlus . fst <$> symbolWithPos "+"),
    Prefix (flip EUnOp UnOpMinus . fst <$> symbolWithPos "-"),
    Prefix (flip EUnOp UnOpNot . fst <$> symbolWithPos "!") ],
   [InfixL (binOpParser "."),
    InfixL infixFunParser],
   [InfixL (binOpParser "*."),
    InfixL (binOpParser "/."),
    InfixL (binOpParser "*"),
    InfixL (binOpParser "/"),
    InfixL (binOpParser "%")],
   [InfixL (binOpParser "+."),
    InfixL (binOpParser "-."),
    InfixL plusParser,
    InfixL (binOpParser "-")],
   [InfixR consParser,
    InfixR (binOpParser "++")],
   [InfixN (binOpParser "=="),
    InfixN (binOpParser "!="),
    InfixN (binOpParser "<="),
    InfixN (binOpParser ">="),
    InfixN (binOpParser "<"),
    InfixN (binOpParser ">")],
   [InfixL (binOpParser "|>")],
   [InfixL (binOpParser "&&")],
   [InfixL (binOpParser "||")]]

expr :: Parser (Expr SourcePos)
expr = makeExprParser eTerm operators

eTerm :: Parser (Expr SourcePos)
eTerm =
  try eApp <|>
  eSimple <|>
  eIf <|>
  eLet <|>
  eLambda <|>
  eCase

eApp :: Parser (Expr SourcePos)
eApp = do
  e <- eSimple
  es <- many eSimple
  case (e, es) of
    (_, []) -> return e
    (EConstr p name args, _) -> return $ EConstr p name (args ++ es)
    (ESpine p e2 es2, _) -> return $ ESpine p e2 (es2 ++ es)
    _ -> return $ ESpine (getPos e) e es

eSimple :: Parser (Expr SourcePos)
eSimple =
  EUnit   <$> getSourcePos <*  symbol "()" <|>
  EBool   <$> getSourcePos <*> (rword "True" >> return True) <|>
  EBool   <$> getSourcePos <*> (rword "False" >> return False) <|>
  EFloat  <$> getSourcePos <*> try unsignedFloat <|>
  EInt    <$> getSourcePos <*> try (fromIntegral <$> unsignedInteger) <|>
  EChar   <$> getSourcePos <*> charLiteral <|>
  EString <$> getSourcePos <*> stringLiteral <|>
  EVar    <$> getSourcePos <*> identifier <|>
  EConstr <$> getSourcePos <*> upperIdentifier <*> pure [] <|>
  try eTuple <|>
  eVec <|>
  eAnnot

eTuple :: Parser (Expr SourcePos)
eTuple = parens (do
  pos <- getSourcePos
  es <- sepBy1 expr comma
  case es of
    [e] -> return e
    _ -> return $ ETuple pos es $ length es)

eIf :: Parser (Expr SourcePos)
eIf = do
  pos <- getSourcePos
  rword "if"
  e1 <- expr
  rword "then"
  e2 <- expr
  rword "else"
  e3 <- expr
  return $ EIf pos e1 e2 e3

eAnnot :: Parser (Expr SourcePos)
eAnnot = parens (do
  pos <- getSourcePos
  e <- expr
  void $ symbol "::"
  t <- typeParser
  return $ EAnnot pos e t)

eLambda :: Parser (Expr SourcePos)
eLambda = do
  pos <- getSourcePos
  void (symbol "\\" <|> symbol "λ")
  args <- some identifier
  void $ symbol "->"
  e <- expr
  return $ buildLambda pos args e

eCase :: Parser (Expr SourcePos)
eCase = do
  pos <- getSourcePos
  rword "case"
  e <- expr
  rword "of"
  bs <- some branch
  return $ ECase pos e bs

branch :: Parser (Branch SourcePos)
branch = do
  pos <- getSourcePos
  void $ symbol "|"
  pat <- patternParser
  void $ symbol "->"
  e <- expr
  return ([pat], e, pos)

buildLambda :: p -> [Var] -> Expr p -> Expr p
buildLambda _ [] e = e
buildLambda p (x : xs) e = ELambda p x $ buildLambda p xs e

eVec :: Parser (Expr SourcePos)
eVec = do
  pos <- getSourcePos
  es <- brackets (sepBy expr comma)
  return $ foldr (ECons pos) (ENil pos) es

eLet :: Parser (Expr SourcePos)
eLet = do
  pos <- getSourcePos
  rword "let"
  x <- identifier
  annot <- option Nothing (symbol "::" >> Just <$> typeParser)
  void $ symbol "="
  e1 <- expr
  rword "in"
  e2 <- expr
  case annot of
    Nothing -> return $ ELet pos x e1 e2
    Just t -> return $ ELet pos x (EAnnot (getPos e1) e1 t) e2


patternParser :: Parser (Pattern SourcePos)
patternParser = makeExprParser pTerm [[InfixR (PCons <$> getSourcePos <* symbol ":")]]

pTerm :: Parser (Pattern SourcePos)
pTerm =
  try pConstr <|>
  pSimple

pConstr :: Parser (Pattern SourcePos)
pConstr = do
  pos <- getSourcePos
  name <- upperIdentifier
  args <- some pSimple
  return $ PConstr pos name args

pSimple :: Parser (Pattern SourcePos)
pSimple =
  PWild   <$> getSourcePos <*  symbol "_" <|>
  PUnit   <$> getSourcePos <*  symbol "()" <|>
  PBool   <$> getSourcePos <*> (rword "True" >> return True) <|>
  PBool   <$> getSourcePos <*> (rword "False" >> return False) <|>
  PFloat  <$> getSourcePos <*> try float <|>
  PInt    <$> getSourcePos <*> (fromIntegral <$> integer) <|>
  PChar   <$> getSourcePos <*> charLiteral <|>
  PString <$> getSourcePos <*> stringLiteral <|>
  PVar    <$> getSourcePos <*> identifier <|>
  PConstr <$> getSourcePos <*> upperIdentifier <*> pure [] <|>
  pTuple <|>
  pVec

pTuple :: Parser (Pattern SourcePos)
pTuple = parens (do
  pos <- getSourcePos
  ps <- sepBy1 patternParser comma
  case ps of
    [e] -> return e
    _ -> return $ PTuple pos ps $ length ps)

pVec :: Parser (Pattern SourcePos)
pVec = do
  pos <- getSourcePos
  es <- brackets (sepBy patternParser comma)
  return $ foldr (PCons pos) (PNil pos) es

functionName :: Parser (SourcePos, String)
functionName = (,) <$> getSourcePos <*> (rword "def" >> identifier)

functionTypeAnnot :: Parser (ProgramBlock SourcePos)
functionTypeAnnot = do
  (pos, name) <-functionName
  void $ symbol "::"
  t <- typeParser
  return $ FunTypeAnnot pos name t

functionDefCase :: Parser (ProgramBlock SourcePos)
functionDefCase = do
  (pos, name) <-functionName
  args <- many pSimple
  void $ symbol "="
  e <- expr
  return $ FunDefCase pos name args e

constrDef :: Parser (ConstrDef SourcePos)
constrDef = do
  pos <- getSourcePos
  void $ symbol "|"
  name <- upperIdentifier
  void $ symbol "::"
  t <- typeTemplateParser
  return $ ConstrDef pos name t

gadtDef :: Parser (ProgramBlock SourcePos)
gadtDef = do
  pos <- getSourcePos
  rword "data"
  name <- upperIdentifier
  params <- many ((GADTDefParamMonotype <$> kind) <|> (GADTDefParamType <$> gadtParamIdentifier))
  constructors <- option [] (rword "where" >> some constrDef)
  return $ GADTDef pos name params constructors

programBlock :: Parser (ProgramBlock SourcePos)
programBlock =
  try functionDefCase <|>
  functionTypeAnnot <|>
  gadtDef

program :: Parser [ProgramBlock SourcePos]
program = many programBlock

parseProgram :: String -> String -> Either (ParseErrorBundle String Void) [ProgramBlock SourcePos]
parseProgram = parse (between sc eof program)
