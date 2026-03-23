-- | Parser for the CHR surface language.
--
-- Parses Prolog-compatible CHR syntax into a 'Module' value.
--
-- Supported syntax:
--
-- @
-- % Line comments
--
-- :- module(order, []).      -- Export list is parsed but ignored.
--                            -- Exports are not yet implemented;
--                            -- all constraints are implicitly public.
-- :- use_module(stdlib).
--
-- :- chr_constraint leq\/2.
-- :- chr_constraint fib\/2, upto\/1.
--
-- refl \@ leq(X, X) \<=> true.
-- leq(X, X) \<=> true.
-- trans \@ leq(X, Y), leq(Y, Z) ==> leq(X, Z).
-- a \@ kept \\ removed \<=> guard | body.
-- @
module YCHR.Parser
  ( parseModule,
  )
where

import Control.Monad (void)
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L
import YCHR.Parsed
import YCHR.Types

-- | Parser type: 'String' input, no custom error components.
type Parser = Parsec Void String

-- | Parse a CHR module from source text.
--
-- The first argument is the source file name (used in error messages only).
parseModule ::
  String ->
  String ->
  Either (ParseErrorBundle String Void) Module
parseModule = parse (sc *> moduleP <* eof)

-- ---------------------------------------------------------------------------
-- Space consumer and lexeme helpers
-- ---------------------------------------------------------------------------

-- | Consume whitespace and @%@ line comments.
sc :: Parser ()
sc = L.space space1 (L.skipLineComment "%") empty

-- | Wrap a parser to consume trailing whitespace.
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

-- | Parse a fixed string and consume trailing whitespace.
symbol :: String -> Parser String
symbol = L.symbol sc

-- | Parse something enclosed in parentheses.
parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- | Parse something enclosed in square brackets.
brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

-- | Parse a comma separator.
comma :: Parser ()
comma = void (symbol ",")

-- ---------------------------------------------------------------------------
-- Atoms, variables, wildcards, integers
-- ---------------------------------------------------------------------------

-- | Parse an atom: a lowercase identifier or a single-quoted string.
--
-- Single-quoted atoms support:
--
-- * @''@ — ISO Prolog standard escape for an embedded single quote
-- * @\'@ — SWI-Prolog backslash escape for an embedded single quote
-- * @\\\\@ — backslash
-- * @\\n@, @\\t@ — newline and tab
-- * @\\x@ — fallback: keep @x@ literally
-- * Any other character — taken literally
atomP :: Parser String
atomP = lexeme (unquotedP <|> quotedP)
  where
    unquotedP = (:) <$> lowerChar <*> many (alphaNumChar <|> char '_')
    quotedP = char '\'' *> go
      where
        go =
          choice
            [ do
                _ <- char '\''
                choice
                  [ char '\'' *> (('\'' :) <$> go), -- '' → embedded '
                    pure [] -- lone ' → end of atom
                  ],
              do
                _ <- char '\\'
                c <- escapeChar
                (c :) <$> go,
              do
                c <- satisfy (\c -> c /= '\'' && c /= '\\')
                (c :) <$> go
            ]
        escapeChar =
          choice
            [ '\'' <$ char '\'', -- \' → '
              '\\' <$ char '\\', -- \\ → \
              '\n' <$ char 'n', -- \n → newline
              '\t' <$ char 't', -- \t → tab
              anySingle -- \x → x (fallback)
            ]

-- | Parse a variable (uppercase identifier) as 'VarTerm'.
varP :: Parser Term
varP = lexeme $ do
  c <- upperChar
  rest <- many (alphaNumChar <|> char '_')
  pure (VarTerm (c : rest))

-- | Parse a wildcard: bare @_@ not followed by a word character.
wildcardP :: Parser Term
wildcardP = lexeme $ do
  _ <- char '_'
  notFollowedBy (alphaNumChar <|> char '_')
  pure Wildcard

-- | Parse a non-negative decimal integer as 'IntTerm'.
intP :: Parser Term
intP = lexeme (IntTerm <$> L.decimal)

-- ---------------------------------------------------------------------------
-- Terms
-- ---------------------------------------------------------------------------

-- | Parse a term: compound, wildcard, variable, integer, or bare atom.
termP :: Parser Term
termP =
  choice
    [ wildcardP,
      varP,
      try intP,
      atomOrCompoundP
    ]

-- | Parse an atom optionally followed by a parenthesised argument list.
-- Produces 'CompoundTerm' if arguments are present, 'AtomTerm' otherwise.
atomOrCompoundP :: Parser Term
atomOrCompoundP = do
  name <- atomP
  maybeOpen <- optional (symbol "(")
  case maybeOpen of
    Nothing -> pure (AtomTerm name)
    Just _ -> do
      args <- termP `sepBy` comma
      _ <- symbol ")"
      pure (CompoundTerm (Unqualified name) args)

-- ---------------------------------------------------------------------------
-- Constraints (as they appear in rule heads)
-- ---------------------------------------------------------------------------

-- | Parse a constraint occurrence: @name@ or @name(arg, ...)@.
constraintP :: Parser Constraint
constraintP = do
  name <- atomP
  args <- option [] (parens (termP `sepBy` comma))
  pure (Constraint (Unqualified name) args)

-- ---------------------------------------------------------------------------
-- Rule head
-- ---------------------------------------------------------------------------

-- | Parse a rule head, consuming the neck symbol (@<=>@ or @==>@).
-- Produces a 'Head' value.
headP :: Parser Head
headP = do
  left <- constraintP `sepBy1` comma
  choice
    [ do
        _ <- symbol "\\"
        right <- constraintP `sepBy1` comma
        _ <- symbol "<=>"
        pure (Simpagation left right),
      symbol "<=>" *> pure (Simplification left),
      symbol "==>" *> pure (Propagation left)
    ]

-- ---------------------------------------------------------------------------
-- Guard and body
-- ---------------------------------------------------------------------------

-- | Parse the guard and body of a rule.
--
-- If @|@ is present, the terms before it form the guard and the terms after
-- form the body. If @|@ is absent, the guard is empty and all terms are the
-- body.
guardBodyP :: Parser ([Term], [Term])
guardBodyP = do
  ts <- termP `sepBy1` comma
  choice
    [ do
        _ <- symbol "|"
        body <- termP `sepBy1` comma
        pure (ts, body),
      pure ([], ts)
    ]

-- ---------------------------------------------------------------------------
-- Rules
-- ---------------------------------------------------------------------------

-- | Parse a single CHR rule.
ruleP :: Parser Rule
ruleP = do
  name <- optional (try (atomP <* symbol "@"))
  head_ <- headP
  (guard_, body) <- guardBodyP
  _ <- symbol "."
  pure (Rule name head_ guard_ body)

-- ---------------------------------------------------------------------------
-- Directives
-- ---------------------------------------------------------------------------

data Directive
  = DirModule String
  | DirImport String
  | DirConstraintDecl [Declaration]
  | DirOther

-- | Parse a Prolog-style directive (@:- ...@).
directiveP :: Parser Directive
directiveP = do
  _ <- symbol ":-"
  keyword <- atomP
  case keyword of
    "module" -> do
      name <- parens moduleArgsP
      _ <- symbol "."
      pure (DirModule name)
    "use_module" -> do
      name <- parens atomP
      _ <- symbol "."
      pure (DirImport name)
    "chr_constraint" -> do
      decls <- constraintDeclP `sepBy1` comma
      _ <- symbol "."
      pure (DirConstraintDecl decls)
    _ -> do
      -- Unknown directive: skip until the terminating dot.
      _ <- manyTill anySingle (char '.')
      sc
      pure DirOther

-- | Parse the arguments of a @module@ directive.
-- The export list (second argument) is parsed and discarded; exports are not
-- yet implemented and all constraints are implicitly public.
moduleArgsP :: Parser String
moduleArgsP = do
  name <- atomP
  _ <- comma
  _ <- brackets (many (satisfy (/= ']')))
  pure name

-- | Parse a single constraint declaration: @name\/arity@.
constraintDeclP :: Parser Declaration
constraintDeclP = do
  name <- atomP
  _ <- symbol "/"
  arity <- lexeme L.decimal
  pure (ConstraintDecl name arity)

-- ---------------------------------------------------------------------------
-- Module
-- ---------------------------------------------------------------------------

-- | Parse a complete CHR module.
moduleP :: Parser Module
moduleP = do
  items <- many (choice [Left <$> try directiveP, Right <$> ruleP])
  let dirs = [d | Left d <- items]
      rules = [r | Right r <- items]
      modName_ = case [n | DirModule n <- dirs] of
        (n : _) -> n
        [] -> ""
      modImports_ = [n | DirImport n <- dirs]
      modDecls_ = concat [ds | DirConstraintDecl ds <- dirs]
  pure (Module modName_ modImports_ modDecls_ rules)
