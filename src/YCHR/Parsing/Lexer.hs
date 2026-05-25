{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Lexer helpers shared by 'YCHR.SExpr' and 'YCHR.PExpr'.
--
-- A small set of parsec combinators that mimic the parts of
-- 'Text.Megaparsec.Char.Lexer' the codebase used to depend on:
-- whitespace + line-comment consumer ('space'), 'lexeme', 'symbol',
-- integer 'decimal', and a permissive C-style 'charLiteral'.
module YCHR.Parsing.Lexer
  ( space,
    space1,
    lexeme,
    symbol,
    decimal,
    charLiteral,
    skipLineComment,
  )
where

import Data.Text (Text)
import Data.Text qualified as T
import Text.Parsec (ParsecT, Stream, (<|>))
import Text.Parsec qualified as P
import Text.Parsec.Char qualified as PC

-- | Whitespace + optional line-comment consumer. Mirrors
-- 'Text.Megaparsec.Char.Lexer.space'. The third argument (block
-- comments) is omitted because the YCHR grammars don't use them.
space :: (Stream s m Char) => ParsecT s u m () -> ParsecT s u m () -> ParsecT s u m ()
space ws lineCmt = P.skipMany (ws <|> lineCmt)

-- | One or more whitespace characters. Replaces
-- 'Text.Megaparsec.Char.space1'.
space1 :: (Stream s m Char) => ParsecT s u m ()
space1 = P.skipMany1 PC.space

-- | Run @p@, then consume trailing whitespace with @sc@.
lexeme :: (Stream s m Char) => ParsecT s u m () -> ParsecT s u m a -> ParsecT s u m a
lexeme sc p = p <* sc

-- | Parse a fixed text symbol and consume trailing whitespace.
symbol :: (Stream s m Char) => ParsecT s u m () -> Text -> ParsecT s u m Text
symbol sc s = lexeme sc (T.pack <$> PC.string (T.unpack s))

-- | Parse one or more decimal digits as an 'Integer' (arbitrary precision).
decimal :: (Stream s m Char) => ParsecT s u m Integer
decimal = read <$> P.many1 PC.digit

-- | Skip everything from a literal prefix to (but not including) the
-- end-of-line. Mirrors 'Text.Megaparsec.Char.Lexer.skipLineComment'.
skipLineComment :: (Stream s m Char) => Text -> ParsecT s u m ()
skipLineComment prefix = do
  _ <- PC.string (T.unpack prefix)
  _ <- P.manyTill PC.anyChar (P.lookAhead (P.eof <|> (() <$ PC.char '\n')))
  pure ()

-- | A permissive character literal that interprets a small set of
-- common escape sequences. Used inside double-quoted s-expression
-- strings; the caller is responsible for the surrounding quotes.
charLiteral :: (Stream s m Char) => ParsecT s u m Char
charLiteral = do
  c <- PC.anyChar
  case c of
    '\\' -> escape
    _ -> pure c
  where
    escape =
      P.choice
        [ '\n' <$ PC.char 'n',
          '\t' <$ PC.char 't',
          '\r' <$ PC.char 'r',
          '\\' <$ PC.char '\\',
          '"' <$ PC.char '"',
          '\'' <$ PC.char '\'',
          PC.anyChar
        ]
