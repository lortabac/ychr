{-# LANGUAGE OverloadedStrings #-}

-- | Generic s-expression type with printer and parser.
--
-- The s-expression grammar:
--
-- @
-- sexpr  = atom | int | float | string | list
-- atom   = (alnum | [_.-])+   (any token that is not a number)
-- int    = [-]?[0-9]+
-- float  = [-]?[0-9]+\.[0-9]+([eE][-+]?[0-9]+)? | +nan.0 | +inf.0 | -inf.0
-- string = '"' (escape | [^"\\])* '"'
-- list   = '(' sexpr* ')'
-- @
--
-- Line comments start with @;@ and extend to end of line.
module YCHR.Internal.SExpr
  ( SExpr (..),
    printSExpr,
    parseSExpr,
    showFloat,
  )
where

import Data.Char (isAlphaNum)
import Data.Text (Text)
import Data.Text qualified as T
import Text.Parsec (Parsec, between, choice, eof, many, parse, try)
import Text.Parsec qualified as P
import Text.Parsec.Char (char, satisfy)
import Text.Parsec.Text ()
import Text.Read (readMaybe)
import YCHR.Internal.Parsing.Lexer
  ( charLiteral,
    skipLineComment,
    space,
    space1,
  )

-- | A generic s-expression.
data SExpr
  = -- | Unquoted identifier (e.g. @let@, @create-constraint@).
    SAtom Text
  | -- | Integer literal (arbitrary precision).
    SInt Integer
  | -- | Floating-point literal.
    SFloat Double
  | -- | Double-quoted string literal.
    SString Text
  | -- | Parenthesised list of sub-expressions.
    SList [SExpr]
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Printer
-- ---------------------------------------------------------------------------

-- | Render an s-expression as 'Text' on a single line.
printSExpr :: SExpr -> Text
printSExpr (SAtom t) = t
printSExpr (SInt n) = T.pack (show n)
printSExpr (SFloat n) = T.pack (showFloat n)
printSExpr (SString t) = "\"" <> escapeString t <> "\""
printSExpr (SList xs) = "(" <> T.intercalate " " (map printSExpr xs) <> ")"

-- | Print a float. NaN and infinities use Scheme's spelling
-- (@+nan.0@, @+inf.0@, @-inf.0@); everything else is 'show', which
-- always has a @.@ for a finite 'Double'.
showFloat :: Double -> String
showFloat x
  | isNaN x = "+nan.0"
  | isInfinite x = if x > 0 then "+inf.0" else "-inf.0"
  | otherwise = show x

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

type Parser = Parsec Text ()

-- | Parse a single s-expression from 'Text'.
parseSExpr :: Text -> Either String SExpr
parseSExpr input = case parse (sc *> pSExpr <* eof) "<sexpr>" input of
  Left err -> Left (show err)
  Right s -> Right s

-- | Parse a single s-expression, consuming trailing whitespace.
pSExpr :: Parser SExpr
pSExpr = choice [pList, pString, pSpecialFloat, pAtomOrInt] <* sc

-- | @+nan.0@, @+inf.0@ and @-inf.0@. Tried before 'pAtomOrInt' since
-- @-inf.0@ would otherwise read as an atom.
pSpecialFloat :: Parser SExpr
pSpecialFloat =
  choice
    [ try (P.string "+nan.0" *> notAtomChar) >> pure (SFloat (0 / 0)),
      try (P.string "+inf.0" *> notAtomChar) >> pure (SFloat (1 / 0)),
      try (P.string "-inf.0" *> notAtomChar) >> pure (SFloat (-1 / 0))
    ]
  where
    notAtomChar = P.notFollowedBy (satisfy isAtomChar)

pList :: Parser SExpr
pList = SList <$> between (char '(' *> sc) (char ')') (many pSExpr)

pString :: Parser SExpr
pString =
  SString . T.pack <$> (char '"' *> P.manyTill charLiteral (try (char '"')))

pAtomOrInt :: Parser SExpr
pAtomOrInt = do
  tok <- T.pack <$> P.many1 (satisfy isAtomChar)
  pure $ case readInt tok of
    Just n -> SInt n
    Nothing
      | T.any (== '.') tok, Just f <- readMaybe (T.unpack tok) -> SFloat f
      | otherwise -> SAtom tok

readInt :: Text -> Maybe Integer
readInt t = case T.uncons t of
  Just ('-', rest)
    | not (T.null rest), T.all isDigit rest -> Just (negate (read (T.unpack rest)))
  Just (c, _)
    | isDigit c, T.all isDigit t -> Just (read (T.unpack t))
  _ -> Nothing
  where
    isDigit c = c >= '0' && c <= '9'

-- | A token character. Includes @.@ to support float literals; tokens
-- containing @.@ are dispatched to 'SFloat' if they parse as a Double.
isAtomChar :: Char -> Bool
isAtomChar c = isAlphaNum c || c == '_' || c == '-' || c == '.'

-- | Whitespace consumer (spaces + line comments starting with @;@).
sc :: Parser ()
sc = space space1 (skipLineComment ";")
