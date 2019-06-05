module SEDEL.Parser.Parser (parseModule) where

import           Control.Arrow (first, second)
import           Data.Functor (($>))
import           Data.Maybe (fromMaybe)
import           Data.Scientific (toRealFloat)
import           Data.Void
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import           Control.Monad.Combinators.Expr
import           Unbound.Generics.LocallyNameless

import           SEDEL.Common
import           SEDEL.Source.Syntax
import           SEDEL.Util


type Parser = Parsec Void String

parseModule :: String -> Either String Module
parseModule s =
 case runParser (whole prog) "" s of
   Left err -> Left $ errorBundlePretty err
   Right e -> Right e


-- | Top-level parsers (should consume all input)
whole :: Parser a -> Parser a
whole p = sc *> p <* eof

------------------------------------------------------------------------
-- Programs
------------------------------------------------------------------------

prog :: Parser Module
prog = do
 decls <- sepEndBy decl semi
 m <- optional mainDecl
 let d = fromMaybe (DefDecl (TmBind "main" [] [] Top Nothing False)) m
 return $ Module decls d

mainDecl :: Parser SDecl
mainDecl = do
 rword "main"
 symbol "="
 e <- expr
 return $ DefDecl (TmBind "main" [] [] e Nothing False)


decl :: Parser SDecl
decl = sedel

sedel :: Parser SDecl
sedel = DefDecl <$> tmBind

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
    , pLet
    , pIf
    , LitV <$> float
    , topVal
    , evar <$> lidentifier
    , record
    , bconst
    , parens expr
    ]

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

pLet :: Parser Expr
pLet = do
  rword "let"
  n <- lidentifier
  symbol "="
  e1 <- expr
  rword "in"
  e2 <- expr
  return $ elet n e1 e2

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
pType = choice [pForall, parens pType, atypescheme]

tOperators :: [[Operator Parser SType]]
tOperators =
  [ [InfixL (And <$ symbol "&")]
  , [InfixR (Arr <$ symbol "->")]
  ]

ascheme :: Parser Scheme
ascheme =
  choice [pForall, parens pType, atypescheme]

atype :: Parser SType
atype = makeExprParser stype tOperators

stype :: Parser SType
stype =
  choice [tvar <$> uidentifier, recordType, tconst, parens atype]

atypescheme :: Parser Scheme
atypescheme = atype >>= \x -> return $ SType x

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
    [ rword "Double" $> NumT
    , rword "Bool" $> BoolT
    , rword "Top" $> TopT
    , rword "Bot" $> BotT
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
param =
  choice
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
         return (n, TopT)
    , parens constrainTy
    ]

-- [x * A] or X
ctyparam :: Parser (String, SType)
ctyparam =
  choice
    [ do n <- uidentifier
         return (n, TopT)
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
  , "in"
  , "type"
  , "forall"
  , "main"
  , "undefined"
  , "Double"
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
