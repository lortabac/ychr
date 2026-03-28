{-# LANGUAGE OverloadedStrings #-}

-- | Parser for the CHR surface language.
--
-- Parses Prolog-compatible CHR syntax into a 'Module' value.
--
-- Supported syntax:
--
-- @
-- % Line comments
--
-- :- module(order, [leq\/2]). -- Export list specifies visible constraints.
-- :- use_module(stdlib).
--
-- :- chr_constraint leq\/2.
-- :- chr_constraint fib\/2, upto\/1.
--
-- refl \@ leq(X, X) \<=> true.
-- leq(X, X) \<=> true.
-- trans \@ leq(X, Y), leq(Y, Z) ==> leq(X, Z).
-- a \@ kept \\ removed \<=> guard | body.
--
-- [H|T]     -- list with head H and tail T
-- [a, b, c] -- list literal (sugar for '.'(a,'.'(b,'.'(c,'[]'))))
-- @
module YCHR.Parser
  ( parseModule,
    parseConstraint,
    parseQuery,
    parseTerm,
    parseRule,
  )
where

import Control.Monad (void)
import Control.Monad.Combinators.Expr (Operator (..), makeExprParser)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L
import YCHR.Parsed
import YCHR.Types

-- | Convert a megaparsec 'SourcePos' to a 'SourceLoc'.
sourceLocFromPos :: SourcePos -> SourceLoc
sourceLocFromPos sp =
  SourceLoc
    { file = sourceName sp,
      line = unPos (sourceLine sp),
      col = unPos (sourceColumn sp)
    }

-- | Wrap a parser's result with the source location of its first character.
withLoc :: Parser a -> Parser (Ann a)
withLoc p = do
  sp <- getSourcePos
  x <- p
  pure (Ann x (sourceLocFromPos sp))

-- | Parser type: 'Text' input, no custom error components.
type Parser = Parsec Void Text

-- | Parse a CHR module from source text.
--
-- The first argument is the source file name (used in error messages only).
parseModule ::
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) Module
parseModule = parse (sc *> moduleP <* eof)

-- | Parse a single constraint from surface-language 'Text'.
--
-- The source name (first argument) is used in error messages only.
-- Example: @parseConstraint "\<query\>" "leq(X, Y)"@.
parseConstraint ::
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) Constraint
parseConstraint = parse (sc *> constraintP <* eof)

-- | Parse a single term from surface-language 'Text'.
--
-- The source name (first argument) is used in error messages only.
-- Example: @parseTerm "\<query\>" "f(X, 42)"@.
parseTerm ::
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) Term
parseTerm = parse (sc *> termP <* eof)

-- | Parse a query: a comma-separated list of goals terminated by a dot.
--
-- The source name (first argument) is used in error messages only.
-- Example: @parseQuery "\<query\>" "fib(10, X), Y is X + 1."@.
parseQuery ::
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) [Term]
parseQuery = parse (sc *> termP `sepBy1` comma <* symbol "." <* eof)

-- | Parse a single CHR rule from surface-language 'Text'.
--
-- The source name (first argument) is used in error messages only.
parseRule ::
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) Rule
parseRule = parse (sc *> ruleP <* eof)

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
symbol :: Text -> Parser Text
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

-- | Reserved words that cannot be used as unquoted atoms (they are operators).
reservedWords :: [Text]
reservedWords = ["is"]

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
atomP :: Parser Text
atomP = lexeme (unquotedP <|> quotedP)
  where
    unquotedP = do
      name <- (:) <$> lowerChar <*> many (alphaNumChar <|> char '_')
      let t = T.pack name
      if t `elem` reservedWords
        then fail ("reserved word: " ++ name)
        else pure t
    quotedP = T.pack <$> (char '\'' *> go)
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
  pure (VarTerm (T.pack (c : rest)))

-- | Parse a wildcard: bare @_@ not followed by a word character.
wildcardP :: Parser Term
wildcardP = lexeme $ do
  _ <- char '_'
  notFollowedBy (alphaNumChar <|> char '_')
  pure Wildcard

-- | Parse a decimal integer (optionally negative, no space between sign and
-- digits) as 'IntTerm'.
intP :: Parser Term
intP = lexeme $ do
  sign <- optional (char '-')
  n <- L.decimal
  pure (IntTerm (maybe n (const (negate n)) sign))

-- ---------------------------------------------------------------------------
-- Operator tokens
-- ---------------------------------------------------------------------------

-- | Parse a word operator (e.g. @is@, @div@, @mod@).
-- Fails if the keyword is immediately followed by an alphanumeric character or @_@.
wordOp :: Text -> Parser Text
wordOp w = lexeme $ try $ do
  _ <- string w
  notFollowedBy (alphaNumChar <|> char '_')
  pure w

-- | Parse a symbol operator (e.g. @=<@, @==@, @+@).
-- Reads the longest run of symbol characters and checks for an exact match,
-- backtracking if the run does not equal the expected operator.
symbolOp :: Text -> Parser Text
symbolOp op = lexeme $ try $ do
  s <- T.pack <$> some (oneOf (":=<>+-*/" :: String))
  if s == op
    then pure s
    else fail ("expected operator " ++ show op)

-- ---------------------------------------------------------------------------
-- Terms
-- ---------------------------------------------------------------------------

-- | Parse a double-quoted string literal as 'TextTerm'.
--
-- Supports the same escape sequences as single-quoted atoms:
--
-- * @\\\"@ — embedded double quote
-- * @\\\\@ — backslash
-- * @\\n@, @\\t@ — newline and tab
-- * @\\x@ — fallback: keep @x@ literally
stringP :: Parser Term
stringP = lexeme $ TextTerm . T.pack <$> (char '"' *> go)
  where
    go =
      choice
        [ do
            _ <- char '"'
            pure [], -- closing quote
          do
            _ <- char '\\'
            c <- escapeCharDQ
            (c :) <$> go,
          do
            c <- satisfy (\c -> c /= '"' && c /= '\\')
            (c :) <$> go
        ]
    escapeCharDQ =
      choice
        [ '"' <$ char '"', -- \" → "
          '\\' <$ char '\\', -- \\ → \
          '\n' <$ char 'n', -- \n → newline
          '\t' <$ char 't', -- \t → tab
          anySingle -- \x → x (fallback)
        ]

-- | Parse a list term using Prolog list notation.
-- Desugars to nested @'.'(H, T)@ terms, with @'[]'@ for the empty list.
--
-- * @[]@        → @'[]'@
-- * @[a, b, c]@ → @'.'(a, '.'(b, '.'(c, '[]')))@
-- * @[H|T]@     → @'.'(H, T)@
-- * @[a, b|T]@  → @'.'(a, '.'(b, T))@
listTermP :: Parser Term
listTermP = between (symbol "[") (symbol "]") listBody
  where
    listBody = do
      elems <- termP `sepBy` comma
      tail_ <- option (AtomTerm "[]") (symbol "|" *> termP)
      pure (foldr (\h t -> CompoundTerm (Unqualified ".") [h, t]) tail_ elems)

-- | Parse an atomic (non-operator) term.
atomicTermP :: Parser Term
atomicTermP =
  choice
    [ wildcardP,
      varP,
      try intP,
      stringP,
      listTermP,
      try (parens termP),
      atomOrCompoundP
    ]

-- | Operator table from lowest to highest precedence.
operatorTable :: [[Operator Parser Term]]
operatorTable =
  [ [ InfixN (binOp "is" <$ wordOp "is"),
      InfixN (binOp "=" <$ symbolOp "=")
    ]
  ]
  where
    binOp op l r = CompoundTerm (Unqualified op) [l, r]

-- | Parse a term, including infix operator expressions.
termP :: Parser Term
termP = makeExprParser atomicTermP operatorTable

-- | Parse an atom optionally followed by a parenthesised argument list.
-- Produces 'CompoundTerm' if arguments are present, 'AtomTerm' otherwise.
-- Supports qualified names: @module:name(args)@.
atomOrCompoundP :: Parser Term
atomOrCompoundP = do
  name <- try qualifiedNameP <|> (Unqualified <$> atomP)
  maybeOpen <- optional (symbol "(")
  case maybeOpen of
    Nothing -> case name of
      Unqualified n -> pure (AtomTerm n)
      Qualified _ _ -> pure (CompoundTerm name [])
    Just _ -> do
      args <- termP `sepBy` comma
      _ <- symbol ")"
      pure (CompoundTerm name args)
  where
    qualifiedNameP = do
      m <- atomP
      _ <- symbol ":"
      n <- atomP
      pure (Qualified m n)

-- ---------------------------------------------------------------------------
-- Constraints (as they appear in rule heads)
-- ---------------------------------------------------------------------------

-- | Parse a constraint occurrence: @name@, @name(arg, ...)@, or
-- @module:name(arg, ...)@.
constraintP :: Parser Constraint
constraintP = do
  name <- try qualifiedNameP <|> (Unqualified <$> atomP)
  args <- option [] (parens (termP `sepBy` comma))
  pure (Constraint name args)
  where
    qualifiedNameP = do
      m <- atomP
      _ <- symbol ":"
      n <- atomP
      pure (Qualified m n)

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
guardBodyP :: Parser (Ann [Term], Ann [Term])
guardBodyP = do
  startPos <- getSourcePos
  ts <- termP `sepBy1` comma
  choice
    [ do
        _ <- symbol "|"
        bodyPos <- getSourcePos
        body <- termP `sepBy1` comma
        pure (Ann ts (sourceLocFromPos startPos), Ann body (sourceLocFromPos bodyPos)),
      pure (Ann [] (sourceLocFromPos startPos), Ann ts (sourceLocFromPos startPos))
    ]

-- ---------------------------------------------------------------------------
-- Rules
-- ---------------------------------------------------------------------------

-- | Parse a single CHR rule.
ruleP :: Parser Rule
ruleP = do
  name <- optional (try (withLoc (atomP <* symbol "@")))
  head_ <- withLoc headP
  (guard_, body) <- guardBodyP
  _ <- symbol "."
  pure (Rule name head_ guard_ body)

-- ---------------------------------------------------------------------------
-- Directives
-- ---------------------------------------------------------------------------

data Directive
  = DirModule Text [Declaration]
  | DirImport (Ann Import)
  | DirConstraintDecl [Ann Declaration]
  | DirOther

-- | Parse a Prolog-style directive (@:- ...@).
directiveP :: Parser Directive
directiveP = do
  _ <- symbol ":-"
  keyword <- atomP
  case keyword of
    "module" -> do
      (name, exports) <- parens moduleArgsP
      _ <- symbol "."
      pure (DirModule name exports)
    "use_module" -> do
      imp <- parens importP
      _ <- symbol "."
      pure (DirImport imp)
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
-- Returns the module name and its export list (unannotated).
moduleArgsP :: Parser (Text, [Declaration])
moduleArgsP = do
  name <- atomP
  _ <- comma
  exports <- brackets (map (.node) <$> constraintDeclP `sepBy` comma)
  pure (name, exports)

-- | Parse a single constraint declaration: @name\/arity@.
constraintDeclP :: Parser (Ann Declaration)
constraintDeclP = withLoc $ do
  name <- atomP
  _ <- symbol "/"
  arity <- lexeme L.decimal
  pure (ConstraintDecl name arity)

-- | Parse an import specifier: either @library(name)@ or a plain module name.
importP :: Parser (Ann Import)
importP = withLoc (try libraryP <|> (ModuleImport <$> atomP))
  where
    libraryP = do
      _ <- symbol "library"
      LibraryImport <$> parens atomP

-- ---------------------------------------------------------------------------
-- Module
-- ---------------------------------------------------------------------------

-- | Parse a complete CHR module.
moduleP :: Parser Module
moduleP = do
  items <- many (choice [Left <$> try directiveP, Right <$> ruleP])
  let dirs = [d | Left d <- items]
      rules = [r | Right r <- items]
      (modName_, modExports_) = case [(n, e) | DirModule n e <- dirs] of
        ((n, e) : _) -> (n, Just e)
        [] -> (T.empty, Nothing)
      modImports_ = [n | DirImport n <- dirs]
      modDecls_ = concat [ds | DirConstraintDecl ds <- dirs]
  pure (Module modName_ modImports_ modDecls_ rules modExports_)
