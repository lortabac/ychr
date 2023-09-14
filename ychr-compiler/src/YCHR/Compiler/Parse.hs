{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}

module YCHR.Compiler.Parse (Parser, parseRule) where

import Control.Monad (void)
import qualified Control.Monad.Combinators.NonEmpty as NE
import Data.Char (GeneralCategory (..), generalCategory)
import Data.Functor (($>))
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import YCHR.Types.Common
import YCHR.Types.Parsed

type Parser = Parsec Void Text

parseRule :: Parser PsRule
parseRule = do
  n <- optional $ try parseRuleName
  h <- parseHead
  ruleChoiceSym <- parseRuleChoiceSym
  case ruleChoiceSym of
    RemoveSym -> do
      r <- parseRemove
      _ <- equivalenceSym
      g <- try parseGuard <|> pure emptyGuard
      b <- parseBody
      pure $ Simpagation n h r g b
    EquivalenceSym -> do
      g <- try parseGuard <|> pure emptyGuard
      b <- parseBody
      pure $ Simplification n h g b
    ImplicationSym -> do
      g <- try parseGuard <|> pure emptyGuard
      b <- parseBody
      pure $ Propagation n h g b

data RuleChoiceSym = RemoveSym | EquivalenceSym | ImplicationSym

parseRuleChoiceSym :: Parser RuleChoiceSym
parseRuleChoiceSym =
  (RemoveSym <$ removeSym)
    <|> (EquivalenceSym <$ equivalenceSym)
    <|> (ImplicationSym <$ implicationSym)
    <* sc

parseHead :: Parser PsHead
parseHead = Head <$> sepBy parseChrConstraint argSeparator <* sc

parseRemove :: Parser PsRemove
parseRemove = Remove <$> sepBy parseChrConstraint argSeparator <* sc

parseGuard :: Parser PsGuard
parseGuard = Guard <$> sepBy parseConstraint argSeparator <* guardSym

parseBody :: Parser PsBody
parseBody = Body <$> NE.sepBy1 parseConstraint argSeparator <* sc <* ruleEndSym <* sc

parseConstraint :: Parser PsConstraint
parseConstraint =
  (symbol "true" $> TrueConstr)
    <|> fmap ChrConstr parseChrConstraint
    <|> fmap HostConstr parseHostConstraint
    <* sc

parseHostConstraint :: Parser PsHostConstraint
parseHostConstraint = HostConstraint <$> hostConstrFunction <*> parseArguments

hostConstrFunction :: Parser Text
hostConstrFunction = hostConstrSuffix *> hostConstrIdentifier

parseChrConstraint :: Parser PsChrConstraint
parseChrConstraint = ChrConstraint <$> parsePsName <*> parseArguments <* sc

parseArguments :: Parser [PsTerm]
parseArguments = try (parens (sepBy parseTerm argSeparator)) <|> pure []

argSeparator :: Parser ()
argSeparator = void $ symbol ","

parseRuleName :: Parser RuleName
parseRuleName = fmap RuleName genericAlnumIdentifier <* sc <* nameSym <* sc

parsePsName :: Parser PsName
parsePsName =
  try (fmap PsQualifiedName parseQualifiedName)
    <|> fmap PsName parseFunctor

parseQualifiedName :: Parser QualifiedName
parseQualifiedName = do
  modName <- parseFunctor
  _ <- char ':'
  func <- parseFunctor
  pure $ QualifiedName modName func

parseFunctor :: Parser Text
parseFunctor = T.cons <$> nameHead <*> identifierTail

parseVariable :: Parser Variable
parseVariable =
  fmap Variable $
    T.cons <$> variableHead <*> identifierTail

hostConstrIdentifier :: Parser Text
hostConstrIdentifier = takeWhile1P Nothing (\c -> isIdentifierChar c && c == '.')

nameHead :: Parser Char
nameHead = lowerChar

variableHead :: Parser Char
variableHead = upperChar <|> char 'c'

identifierTail :: Parser Text
identifierTail = takeWhileP Nothing isIdentifierChar

genericAlnumIdentifier :: Parser Text
genericAlnumIdentifier = takeWhile1P Nothing isIdentifierChar

isIdentifierChar :: Char -> Bool
isIdentifierChar c =
  (cat == LowercaseLetter)
    || (cat == UppercaseLetter)
    || (cat == DecimalNumber)
    || (c == '_')
  where
    cat = generalCategory c

parseTerm :: Parser PsTerm
parseTerm =
  fmap Var parseVariable
    <|> fmap Int integer
    <|> fmap String stringLiteral

nameSym :: Parser ()
nameSym = void $ symbol "@"

removeSym :: Parser ()
removeSym = void $ symbol "\\"

implicationSym :: Parser ()
implicationSym = void $ symbol "==>"

equivalenceSym :: Parser ()
equivalenceSym = void $ symbol "<=>"

guardSym :: Parser ()
guardSym = void $ symbol "|"

hostConstrSuffix :: Parser ()
hostConstrSuffix = void $ char '#'

ruleEndSym :: Parser ()
ruleEndSym = void $ symbol "."

sc :: Parser ()
sc =
  L.space
    space1
    (L.skipLineComment "%")
    (L.skipBlockComment "/*" "*/")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

integer :: Parser Integer
integer = option id sign <*> lexeme L.decimal
  where
    sign = (id <$ char '+') <|> (negate <$ char '-')

stringLiteral :: Parser Text
stringLiteral = fmap T.pack (char '\"' *> manyTill L.charLiteral (char '\"')) <* sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")
