module Parser (parseType) where

import           Control.Monad.Combinators.Expr
import           Data.Functor                     (($>))
import           Data.Void
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer       as L
import           Unbound.Generics.LocallyNameless

import           Syntax


type Parser = Parsec Void String

parseType :: String -> Either String Type
parseType s = case runParser pType "" s of
  Left err -> Left $ errorBundlePretty err
  Right e  -> Right e

-------------------
-- PARSING TYPES --
-------------------

pType :: Parser Type
pType = makeExprParser atype tOperators

tOperators :: [[Operator Parser Type]]
tOperators =
  [ [InfixL (And <$ symbol "&")]
  , [InfixR (Arr <$ symbol "->")]
  ]

atype :: Parser Type
atype =
  choice
    [tvar <$> aidentifier, tuni <$> uidentifier, recordType, tconst, parens pType]

recordType :: Parser Type
recordType = braces (mkRecdsT <$> sepBy1 tparam comma)

tparam :: Parser (Label, Type)
tparam = do
  l <- lidentifier <|> symbol "_"
  colon
  e <- pType
  return (l, e)

tvar :: String -> Type
tvar = Var . s2n

tconst :: Parser Type
tconst =
  choice
    [ rword "Int" $> Nat
    , rword "Nat" $> Nat
    , rword "Bool" $> Bool
    , rword "Top" $> Top
    , rword "Bot" $> Bot
    ]

tuni :: String -> Type
tuni = Uni . s2n

identifier :: Parser Char -> Parser String
identifier s = (lexeme . try) (p >>= check)
  where
    p = (:) <$> s <*> many identChar
    check x =
      if x `elem` reservedwords
        then fail $ "keyword " ++ show x ++ " cannot be an identifier"
        else return x

lidentifier :: Parser String
lidentifier = identifier lowerChar

uidentifier :: Parser String
uidentifier = identifier (char 'u')

aidentifier :: Parser String
aidentifier = identifier upperChar

mkRecdsT :: [(Label, Type)] -> Type
mkRecdsT []         = Top
mkRecdsT ((l, e):r) = foldl (\t (l', e') -> And t (Rec l' e')) (Rec l e) r

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

colon :: Parser String
colon = symbol ":"

comma :: Parser String
comma = symbol ","

rword :: String -> Parser ()
rword w = string w *> notFollowedBy alphaNumChar *> sc

symbol :: String -> Parser String
symbol = L.symbol sc

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

identChar :: Parser Char
identChar = alphaNumChar <|> oneOf "_#'%"

reservedwords :: [String] -- list of reserved words
reservedwords =
  [ "Int"
  , "Bool"
  , "Nat"
  , "Top"
  , "Bot"
  ]

sc :: Parser ()
sc = L.space space1 lineCmnt blockCmnt
  where
    lineCmnt  = L.skipLineComment "--"
    blockCmnt = L.skipBlockComment "{-" "-}"
