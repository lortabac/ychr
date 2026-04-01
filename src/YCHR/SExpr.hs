{-# LANGUAGE OverloadedStrings #-}

-- | Generic s-expression type with printer and parser.
--
-- The s-expression grammar:
--
-- @
-- sexpr  = atom | int | string | list
-- atom   = [a-zA-Z_][a-zA-Z0-9_-]*
-- int    = [-]?[0-9]+
-- string = '"' (escape | [^"\\])* '"'
-- list   = '(' sexpr* ')'
-- @
--
-- Line comments start with @;@ and extend to end of line.
module YCHR.SExpr
  ( SExpr (..),
    printSExpr,
    parseSExpr,
  )
where

import Data.Char (isAlpha, isAlphaNum)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

-- | A generic s-expression.
data SExpr
  = -- | Unquoted identifier (e.g. @let@, @create-constraint@).
    SAtom Text
  | -- | Integer literal.
    SInt Int
  | -- | Double-quoted string literal.
    SString Text
  | -- | Parenthesised list of sub-expressions.
    SList [SExpr]
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Printer
-- ---------------------------------------------------------------------------

-- | Render an s-expression as 'Text'.  The output is single-line; use
-- 'printSExprPretty' (not yet implemented) for indented multi-line output.
printSExpr :: SExpr -> Text
printSExpr (SAtom t) = t
printSExpr (SInt n) = T.pack (show n)
printSExpr (SString t) = "\"" <> escapeString t <> "\""
printSExpr (SList xs) = "(" <> T.intercalate " " (map printSExpr xs) <> ")"

escapeString :: Text -> Text
escapeString = T.concatMap esc
  where
    esc '\\' = "\\\\"
    esc '"' = "\\\""
    esc '\n' = "\\n"
    esc '\t' = "\\t"
    esc c = T.singleton c

-- ---------------------------------------------------------------------------
-- Parser
-- ---------------------------------------------------------------------------

type Parser = Parsec Void Text

-- | Parse a single s-expression from 'Text'.
parseSExpr :: Text -> Either String SExpr
parseSExpr input = case parse (sc *> pSExpr <* eof) "<sexpr>" input of
  Left err -> Left (errorBundlePretty err)
  Right s -> Right s

-- | Parse a single s-expression, consuming trailing whitespace.
pSExpr :: Parser SExpr
pSExpr = choice [pList, pString, pAtomOrInt] <* sc

pList :: Parser SExpr
pList = SList <$> between (char '(' *> sc) (char ')') (many pSExpr)

pString :: Parser SExpr
pString = SString . T.pack <$> (char '"' *> manyTill L.charLiteral (char '"'))

pAtomOrInt :: Parser SExpr
pAtomOrInt = do
  tok <- takeWhile1P (Just "atom or integer") isAtomChar
  pure $ case readInt tok of
    Just n -> SInt n
    Nothing -> SAtom tok

readInt :: Text -> Maybe Int
readInt t = case T.uncons t of
  Just ('-', rest)
    | not (T.null rest), T.all isDigit rest -> Just (negate (read (T.unpack rest)))
  Just (c, _)
    | isDigit c, T.all isDigit t -> Just (read (T.unpack t))
  _ -> Nothing
  where
    isDigit c = c >= '0' && c <= '9'

isAtomChar :: Char -> Bool
isAtomChar c = isAlphaNum c || c == '_' || c == '-'

-- | Whitespace consumer (spaces + line comments starting with @;@).
sc :: Parser ()
sc = L.space space1 (L.skipLineComment ";") empty

-- | Check if the first character is valid for an atom start.
_isAtomStart :: Char -> Bool
_isAtomStart c = isAlpha c || c == '_'
