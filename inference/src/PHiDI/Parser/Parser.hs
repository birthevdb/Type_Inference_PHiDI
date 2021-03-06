module PHiDI.Parser.Parser (parseModule, parseType) where

import           Control.Arrow                    (first, second)
import           Control.Monad.Combinators.Expr
import           Data.Functor                     (($>))
import           Data.Maybe                       (fromMaybe)
import           Data.Scientific                  (toRealFloat)
import           Data.Void
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer       as L
import           Unbound.Generics.LocallyNameless

import           PHiDI.Operators
import           PHiDI.Source.Syntax
import           PHiDI.Util


type Parser = Parsec Void String

parseModule :: String -> Either String Module
parseModule s =
 case runParser (whole prog) "" s of
   Left err -> Left $ errorBundlePretty err
   Right e  -> Right e

parseType :: String -> Either String Scheme
parseType s = case runParser pType "" s of
  Left err -> Left $ errorBundlePretty err
  Right e  -> Right e

-- | Top-level parsers (should consume all input)
whole :: Parser a -> Parser a
whole p = sc *> p <* eof

------------------------------------------------------------------------
-- Programs
------------------------------------------------------------------------

prog :: Parser Module
prog = do
 decls <- sepEndBy decl semi
 m     <- optional mainDecl
 let d  = fromMaybe (DefDecl (TmBind "main" [] [] Top Nothing False)) m
 return $ Module decls d

mainDecl :: Parser SDecl
mainDecl = do
 e <- expr
 return $ DefDecl (TmBind "main" [] [] e Nothing False)


decl :: Parser SDecl
decl = phidi

phidi :: Parser SDecl
phidi = DefDecl <$> tmBind

tmBind :: Parser TmBind
tmBind = do
  n <- lidentifier
  ts <- many ctyparam
  xs <- many param
  ret <- optional (colon *> pType)
  symbol "="
  e <- expr
  return $
    TmBind n (map (first s2n) ts) (map (first s2n) xs) e ret False

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

expr :: Parser Expr
expr = do
  p <- getSourcePos
  Pos p <$> makeExprParser term pOperators

term :: Parser Expr
term = postfixChain factor fapp

fapp :: Parser (Expr -> Expr)
fapp = do
  e <- factor
  return (`App` e)

factor :: Parser Expr
factor = postfixChain atom dotOperator

dotOperator :: Parser (Expr -> Expr)
dotOperator = do
  symbol "."
  k <- lidentifier
  return (`Proj` k)

atom :: Parser Expr
atom =
  choice
    [ pLambda
    , pLetrec
    , pIf
    , LitV <$> float
    , topVal
    , evar <$> lidentifier
    , poly
    , record
    , bconst
    , parens expr
    ]

poly :: Parser Expr
poly = do
  symbol "^"
  xs <- lidentifier
  return $ evarpoly xs

record :: Parser Expr
record = braces (mkRecds' <$> sepBy1 tmBind comma)

bconst :: Parser Expr
bconst =
  choice
    [ rword "true" $> BoolV True
    , rword "false" $> BoolV False
    ]

pLambda :: Parser Expr
pLambda = do
  symbol "\\"
  xs <- some (lidentifier <|> symbol "_")
  symbol "->"
  e <- expr
  return $ foldr elam (elam (last xs) e) (init xs)

pLetrec :: Parser Expr
pLetrec = do
  rword "let"
  symbol "^"
  n <- lidentifier
  colon
  t <- pType
  symbol "="
  e1 <- expr
  rword "in"
  e2 <- expr
  return $ eletrec n t e1 e2

pIf :: Parser Expr
pIf = do
  rword "if"
  a <- expr
  rword "then"
  b <- expr
  rword "else"
  c <- expr
  return $ If a b c


pOperators :: [[Operator Parser Expr]]
pOperators =
  [ [ InfixL (PrimOp (Arith Mul) <$ symbol "*")
    , InfixL (PrimOp (Arith Div) <$ symbol "/")
    ]
    , [ InfixL (PrimOp (Arith Add) <$ symbol "+")
    , InfixL (PrimOp (Arith Sub) <$ symbol "-")
    ]
  , [ InfixN (PrimOp (Comp Lt) <$ symbol "<")
    , InfixN (PrimOp (Comp Gt) <$ symbol ">")
    ]
  , [ InfixN (PrimOp (Comp Equ) <$ symbol "==")
    , InfixN (PrimOp (Comp Neq) <$ symbol "/=")
    ]
  , [InfixL (PrimOp (Logical LAnd) <$ symbol "&&")]
  , [InfixL (PrimOp (Logical LOr) <$ symbol "||")]
  , [InfixL (Merge <$ symbol ",,")]
  , [InfixN (App <$ symbol "^")]
  ]


------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------
pType :: Parser Scheme
pType = choice [pForall, conv stype, parens pType]

tOperators :: [[Operator Parser SType]]
tOperators =
  [ [InfixL (mkAnd <$ symbol "&")]
  , [InfixR (mkArr <$ symbol "->")]
  ]

stype :: Parser SType
stype = makeExprParser atype tOperators

conv :: Parser SType -> Parser Scheme
conv = fmap SType
-- conv ps = do
--   x <- ps
--   return $ SType x

atype :: Parser SType
atype =
  choice
    [tvar <$> uidentifier, recordType, tconst, parens stype]

pForall :: Parser Scheme
pForall = do
  rword "forall"
  xs <- some pCtyparam
  symbol "."
  t <- pType
  return $ foldr tforall (tforall (last xs) t) (init xs)

recordType :: Parser SType
recordType = braces (mkRecdsT <$> sepBy1 recordparam comma)

tconst :: Parser SType
tconst =
  choice
    [ rword "Int" $> mkNumT
    , rword "Bool" $> mkBoolT
    , rword "Top" $> mkTopT
    , rword "Bot" $> mkBotT
    ]

------------------------------------------------------------------------
-- Parameters
------------------------------------------------------------------------

-- [X, Y, Z]
typaramList :: Parser [(TyName, Kind)]
typaramList =
  brackets $ sepBy1 (uidentifier >>= \n -> return (s2n n, Star)) comma

-- (a, b, c)
pArgs :: Parser [Expr]
pArgs = parens $ sepBy1 expr comma

-- x : A
tparam :: Parser (Label, Scheme)
tparam = do
  l <- lidentifier <|> symbol "_"
  colon
  e <- pType
  return (l, e)

-- x : T
recordparam :: Parser (Label, SType)
recordparam = do
  l <- lidentifier <|> symbol "_"
  colon
  e <- atype
  return (l, e)

-- (x : A) or x
param :: Parser (String, Maybe Scheme)
param = choice
    [ (lidentifier <|> symbol "_") >>= \n -> return (n, Nothing)
    , parens $ second Just <$> tparam
    ]


-- x * A
constrainTy :: Parser (String, SType)
constrainTy = do
  n <- uidentifier
  symbol "*"
  t <- atype
  return (n, t)

-- (x * A) or X
pCtyparam :: Parser (String, SType)
pCtyparam =
  choice
    [ do n <- uidentifier
         return (n, mkTopT)
    , parens constrainTy
    ]

-- [x * A] or X
ctyparam :: Parser (String, SType)
ctyparam =
  choice
    [ do n <- uidentifier
         return (n, mkTopT)
    , brackets constrainTy
    ]

------------------------------------------------------------------------
-- Misc
------------------------------------------------------------------------

sc :: Parser ()
sc = L.space space1 lineCmnt blockCmnt
  where
    lineCmnt  = L.skipLineComment "--"
    blockCmnt = L.skipBlockComment "{-" "-}"


lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

float :: Parser Double
float = lexeme (toRealFloat <$> L.scientific)

topVal :: Parser Expr
topVal = symbol "()" >> return Top

stringLiteral :: Parser String
stringLiteral = lexeme $ char '"' >> manyTill L.charLiteral (char '"')

semi :: Parser String
semi = symbol ";"

colon :: Parser String
colon = symbol ":"

comma :: Parser String
comma = symbol ","

rword :: String -> Parser ()
rword w = string w *> notFollowedBy alphaNumChar *> sc

postfixChain :: Parser a -> Parser (a -> a) -> Parser a
postfixChain p op = do
  x <- p
  rest x
  where
    rest x =
      (do f <- op
          rest $ f x) <|>
      return x

rws :: [String] -- list of reserved words
rws =
  [ "if"
  , "then"
  , "else"
  , "let"
  , "letrec"
  , "in"
  , "type"
  , "forall"
  , "main"
  , "undefined"
  , "Int"
  , "Bool"
  , "true"
  , "false"
  , "Top"
  , "Bot"
  ]


identifier :: Parser Char -> Parser String
identifier s = (lexeme . try) (p >>= check)
  where
    p = (:) <$> s <*> many identChar
    check x =
      if x `elem` rws
        then fail $ "keyword " ++ show x ++ " cannot be an identifier"
        else return x

identChar :: Parser Char
identChar = alphaNumChar <|> oneOf "_#'%"

lidentifier :: Parser String
lidentifier = identifier lowerChar

uidentifier :: Parser String
uidentifier = identifier upperChar
