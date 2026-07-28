-- | A tiny surface syntax for the lambda calculus, parsed with @parsec@.
--
-- Grammar (loosest to tightest binding):
--
-- > expr   ::= '\' ident+ '.' expr          -- lambda (body extends right)
-- >          | 'let' ident '=' expr 'in' expr
-- >          | add
-- > add    ::= app ('+' app)*               -- left-associative
-- > app    ::= atom atom*                   -- application by juxtaposition
-- > atom   ::= ident | int | '(' expr ')'
--
-- Application binds tighter than @+@, so @f x + 1@ is @(f x) + 1@; a lambda
-- body runs as far right as possible, so @\\x. x + 1@ is @\\x. (x + 1)@.
module Parser
  ( parseExpr,
  )
where

import Data.Text qualified as T
import Syntax (Expr (..))
import Text.Parsec
import Text.Parsec.Language (emptyDef)
import Text.Parsec.String (Parser)
import Text.Parsec.Token qualified as Tok

-- | Parse a single expression, or return a human-readable error.
parseExpr :: String -> Either String Expr
parseExpr input = case parse (Tok.whiteSpace lexer *> expr <* eof) "" input of
  Left err -> Left (show err)
  Right e -> Right e

-- ---------------------------------------------------------------------------
-- Lexer
-- ---------------------------------------------------------------------------

lexer :: Tok.TokenParser ()
lexer =
  Tok.makeTokenParser
    emptyDef
      { Tok.identStart = letter <|> char '_',
        Tok.identLetter = alphaNum <|> char '_',
        Tok.reservedNames = ["let", "in"],
        Tok.reservedOpNames = ["\\", ".", "+", "="]
      }

identifier :: Parser T.Text
identifier = T.pack <$> Tok.identifier lexer

reserved :: String -> Parser ()
reserved = Tok.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = Tok.reservedOp lexer

parens :: Parser a -> Parser a
parens = Tok.parens lexer

natural :: Parser Integer
natural = Tok.natural lexer

-- ---------------------------------------------------------------------------
-- Grammar
-- ---------------------------------------------------------------------------

expr :: Parser Expr
expr = lambda <|> letExpr <|> addExpr

-- @\x y. e@ is sugar for @\x. \y. e@.
lambda :: Parser Expr
lambda = do
  reservedOp "\\"
  vars <- many1 identifier
  reservedOp "."
  body <- expr
  pure (foldr Lam body vars)

-- @let x = rhs in body@ desugars to @(\x. body) rhs@.
letExpr :: Parser Expr
letExpr = do
  reserved "let"
  v <- identifier
  reservedOp "="
  rhs <- expr
  reserved "in"
  body <- expr
  pure (App (Lam v body) rhs)

addExpr :: Parser Expr
addExpr = chainl1 appExpr (reservedOp "+" >> pure Add)

appExpr :: Parser Expr
appExpr = foldl1 App <$> many1 atom

atom :: Parser Expr
atom =
  parens expr
    <|> (Var <$> identifier)
    <|> (IntLit <$> natural)
