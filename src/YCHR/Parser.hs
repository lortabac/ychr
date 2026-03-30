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
    parseModuleWith,
    parseModules,
    parseConstraint,
    parseQuery,
    parseQueryWith,
    parseTerm,
    parseTermWith,
    parseRule,
    OpTable,
    builtinOps,
    mergeOps,
    collectOperatorDecls,
    extractOpDecls,
  )
where

import Control.Monad (void, when)
import Control.Monad.Combinators.Expr (Operator (..), makeExprParser)
import Control.Monad.Trans.Reader (ReaderT, ask, runReaderT)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L
import YCHR.Parsed
import YCHR.Types

-- ---------------------------------------------------------------------------
-- Operator table
-- ---------------------------------------------------------------------------

-- | Operator table: maps fixity level to a list of operators at that level.
data OpTable = OpTable
  { opsByFixity :: IntMap [(OpType, Text)],
    -- | Precomputed set of word (non-symbolic) operator names, for reserving
    -- them in 'atomP'.
    wordOpSet :: Set Text
  }
  deriving (Show)

-- | Built-in operators at their standard Prolog fixity levels.
builtinOps :: OpTable
builtinOps = mkOpTable [(700, [(InfixN_, "is"), (InfixN_, "=")])]

-- | Build an 'OpTable' from a list of (fixity, operators) pairs.
mkOpTable :: [(Int, [(OpType, Text)])] -> OpTable
mkOpTable entries =
  OpTable
    { opsByFixity = IntMap.fromListWith (++) entries,
      wordOpSet =
        Set.fromList
          [ name
          | (_, ops) <- entries,
            (_, name) <- ops,
            not (isSymbolic name)
          ]
    }

-- | Merge user-defined operators into an existing table.
-- Returns 'Left' with the conflicting operator name if a naming conflict is
-- found (same operator name at a different fixity or type).
mergeOps :: OpTable -> [OpDecl] -> Either Text OpTable
mergeOps base decls = do
  -- Check for conflicts: same name with different fixity or type
  let existing =
        [ (name, (fix, ty))
        | (fix, ops) <- IntMap.toList base.opsByFixity,
          (ty, name) <- ops
        ]
      newOps = [(d.opName, (d.fixity, d.opType)) | d <- decls]
      allOps = existing ++ newOps
      -- Group by name, check all entries for a name are identical
      grouped = foldr (\(n, ft) acc -> IntMap.alter (addToGroup n ft) (hashName n) acc) IntMap.empty allOps
  checkConflicts (IntMap.elems grouped)
  let userEntries =
        [ (d.fixity, [(d.opType, d.opName)])
        | d <- decls
        ]
  pure
    OpTable
      { opsByFixity = IntMap.unionWith (++) base.opsByFixity (IntMap.fromListWith (++) userEntries),
        wordOpSet =
          Set.union
            base.wordOpSet
            (Set.fromList [d.opName | d <- decls, not (isSymbolic d.opName)])
      }
  where
    hashName :: Text -> Int
    hashName = T.foldl' (\acc c -> acc * 31 + fromEnum c) 0

    addToGroup :: Text -> (Int, OpType) -> Maybe [(Text, (Int, OpType))] -> Maybe [(Text, (Int, OpType))]
    addToGroup n ft Nothing = Just [(n, ft)]
    addToGroup n ft (Just xs) = Just ((n, ft) : xs)

    checkConflicts :: [[(Text, (Int, OpType))]] -> Either Text ()
    checkConflicts [] = pure ()
    checkConflicts (group : rest) = do
      -- Within each hash bucket, check names that match
      let byName = foldr (\(n, ft) acc -> insertWith n ft acc) [] group
      mapM_ checkNameGroup byName
      checkConflicts rest

    insertWith :: Text -> (Int, OpType) -> [(Text, [(Int, OpType)])] -> [(Text, [(Int, OpType)])]
    insertWith n ft [] = [(n, [ft])]
    insertWith n ft ((n', fts) : rest)
      | n == n' = (n', ft : fts) : rest
      | otherwise = (n', fts) : insertWith n ft rest

    checkNameGroup :: (Text, [(Int, OpType)]) -> Either Text ()
    checkNameGroup (_, []) = pure ()
    checkNameGroup (_, [_]) = pure ()
    checkNameGroup (name, (ft : fts))
      | all (== ft) fts = pure ()
      | otherwise = Left name

-- | Check whether a name consists entirely of symbol characters.
isSymbolic :: Text -> Bool
isSymbolic = T.all (`elem` symbolChars)

-- | Characters that can appear in symbol operators.
symbolChars :: [Char]
symbolChars = ":=<>+-*/#@^~!&?"

-- | Convert an 'OpTable' to the format expected by 'makeExprParser'.
-- @makeExprParser@ expects groups in descending precedence (tightest first).
-- In Prolog, lower fixity number = higher precedence (tighter binding),
-- so we sort fixity keys in ascending order.
buildExprOpTable :: OpTable -> [[Operator Parser Term]]
buildExprOpTable table =
  [ concatMap toMegaparsecOp ops
  | (_, ops) <- IntMap.toAscList table.opsByFixity
  ]
  where
    toMegaparsecOp :: (OpType, Text) -> [Operator Parser Term]
    toMegaparsecOp (InfixL_, name) = [InfixL (binOp name <$ opParser name)]
    toMegaparsecOp (InfixR_, name) = [InfixR (binOp name <$ opParser name)]
    toMegaparsecOp (InfixN_, name) = [InfixN (binOp name <$ opParser name)]
    toMegaparsecOp (Prefix_, name) = [Prefix (unOp name <$ opParser name)]
    toMegaparsecOp (Postfix_, name) = [Postfix (unOp name <$ opParser name)]

    binOp op l r = CompoundTerm (Unqualified op) [l, r]
    unOp op x = CompoundTerm (Unqualified op) [x]

    opParser name
      | isSymbolic name = symbolOp name
      | otherwise = wordOp name

-- ---------------------------------------------------------------------------
-- Parser type and runners
-- ---------------------------------------------------------------------------

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

-- | Parser type: 'Text' input with an 'OpTable' reader environment.
type Parser = ReaderT OpTable (Parsec Void Text)

-- | Run a 'Parser' with a given 'OpTable'.
runP :: OpTable -> Parser a -> String -> Text -> Either (ParseErrorBundle Text Void) a
runP table p = parse (runReaderT p table)

-- | Parse a CHR module from source text using the built-in operator table.
--
-- The first argument is the source file name (used in error messages only).
parseModule ::
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) Module
parseModule = parseModuleWith builtinOps

-- | Parse a CHR module from source text using a custom operator table.
parseModuleWith ::
  OpTable ->
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) Module
parseModuleWith table = runP table (sc *> moduleP <* eof)

-- | Parse multiple modules using a two-pass approach:
--
-- 1. Collect operator declarations from all module directives.
-- 2. Merge with built-in operators (error on naming conflicts).
-- 3. Full-parse all modules with the merged operator table.
parseModules ::
  [(String, Text)] ->
  Either (String, ParseErrorBundle Text Void) (OpTable, [Module])
parseModules inputs = do
  -- Pass 1: collect operator declarations from all modules
  allOps <-
    concat
      <$> traverse
        (\(fp, src) -> first' (fp,) (collectOperatorDecls fp src))
        inputs
  -- Merge with builtins
  table <- case mergeOps builtinOps allOps of
    Left conflict ->
      Left
        ( "<operators>",
          -- Produce a dummy ParseErrorBundle — the caller should handle this
          -- differently, but we keep the type uniform for now.
          error ("Operator naming conflict: " ++ T.unpack conflict)
        )
    Right t -> Right t
  -- Pass 2: full parse with merged table
  mods <-
    traverse
      (\(fp, src) -> first' (fp,) (parseModuleWith table fp src))
      inputs
  pure (table, mods)
  where
    first' f (Left e) = Left (f e)
    first' _ (Right x) = Right x

-- | Parse a single constraint from surface-language 'Text'.
--
-- The source name (first argument) is used in error messages only.
-- Example: @parseConstraint "\<query\>" "leq(X, Y)"@.
parseConstraint ::
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) Constraint
parseConstraint = runP builtinOps (sc *> constraintP <* eof)

-- | Parse a single term from surface-language 'Text'.
--
-- The source name (first argument) is used in error messages only.
-- Example: @parseTerm "\<query\>" "f(X, 42)"@.
parseTerm ::
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) Term
parseTerm = parseTermWith builtinOps

-- | Parse a single term with a custom operator table.
parseTermWith ::
  OpTable ->
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) Term
parseTermWith table = runP table (sc *> termP <* eof)

-- | Parse a query: a comma-separated list of goals terminated by a dot.
--
-- The source name (first argument) is used in error messages only.
-- Example: @parseQuery "\<query\>" "fib(10, X), Y is X + 1."@.
parseQuery ::
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) [Term]
parseQuery = parseQueryWith builtinOps

-- | Parse a query with a custom operator table.
parseQueryWith ::
  OpTable ->
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) [Term]
parseQueryWith table = runP table (sc *> termP `sepBy1` comma <* symbol "." <* eof)

-- | Parse a single CHR rule from surface-language 'Text'.
--
-- The source name (first argument) is used in error messages only.
parseRule ::
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) Rule
parseRule = runP builtinOps (sc *> ruleP <* eof)

-- ---------------------------------------------------------------------------
-- Space consumer and lexeme helpers
-- ---------------------------------------------------------------------------

-- | Consume whitespace and @%@ line comments.
sc :: (MonadParsec Void Text m) => m ()
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
      wordOps <- (.wordOpSet) <$> ask
      if t `elem` reservedWords || Set.member t wordOps
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
  s <- T.pack <$> some (oneOf symbolChars)
  if s == op
    then pure s
    else fail ("expected operator " ++ show op)

-- | Parse a sequence of symbol characters as an atom name (for operator names
-- like @\<\>@ or @\<\<\>\>@).
symbolAtomP :: Parser Text
symbolAtomP = lexeme $ T.pack <$> some (oneOf symbolChars)

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

-- | Parse a term, including infix operator expressions.
termP :: Parser Term
termP = do
  table <- ask
  makeExprParser atomicTermP (buildExprOpTable table)

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
  | DirFunctionDecl [Ann Declaration]
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
    "function" -> do
      decls <- functionDeclP `sepBy1` comma
      _ <- symbol "."
      pure (DirFunctionDecl decls)
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
  exports <- brackets (exportItemP `sepBy` comma)
  pure (name, exports)

-- | Parse a single export item: either @name\/arity@ or @op(fixity, type, name)@.
exportItemP :: Parser Declaration
exportItemP = try opDeclP <|> ((.node) <$> constraintDeclP)

-- | Parse an operator declaration: @op(fixity, type, name)@.
opDeclP :: Parser Declaration
opDeclP = do
  _ <- symbol "op"
  _ <- symbol "("
  fix <- lexeme L.decimal
  when (fix < 1 || fix > 1199) $
    fail ("operator fixity must be between 1 and 1199, got: " ++ show fix)
  _ <- comma
  ty <- opTypeP
  _ <- comma
  name <- try atomP <|> identP <|> symbolAtomP
  _ <- symbol ")"
  pure (OperatorDecl (OpDecl fix ty name))
  where
    -- \| Parse any lowercase identifier without rejecting word operators.
    identP = lexeme $ T.pack <$> ((:) <$> lowerChar <*> many (alphaNumChar <|> char '_'))

-- | Parse an operator type specifier.
opTypeP :: Parser OpType
opTypeP =
  lexeme $
    choice
      [ InfixL_ <$ try (string "yfx" <* notFollowedBy alphaNumChar),
        InfixR_ <$ try (string "xfy" <* notFollowedBy alphaNumChar),
        InfixN_ <$ try (string "xfx" <* notFollowedBy alphaNumChar),
        Prefix_ <$ try (string "fx" <* notFollowedBy alphaNumChar),
        Postfix_ <$ try (string "xf" <* notFollowedBy alphaNumChar)
      ]

-- | Parse a single constraint declaration: @name\/arity@.
constraintDeclP :: Parser (Ann Declaration)
constraintDeclP = withLoc $ do
  name <- atomP
  _ <- symbol "/"
  arity <- lexeme L.decimal
  pure (ConstraintDecl name arity)

-- | Parse a single function declaration: @name\/arity@.
functionDeclP :: Parser (Ann Declaration)
functionDeclP = withLoc $ do
  name <- atomP
  _ <- symbol "/"
  arity <- lexeme L.decimal
  pure (FunctionDecl name arity)

-- | Parse a function equation.
--
-- Supports both prefix and infix notation:
--
-- * Prefix: @name(pats) -> rhs.@ or @name(pats) | guard -> rhs.@
-- * Infix:  @X + Y -> rhs.@ or @X + Y | guard -> rhs.@
-- * Prefix op: @- X -> rhs.@
functionEquationP :: Parser (Ann FunctionEquation)
functionEquationP = withLoc (try prefixEq <|> operatorEq)
  where
    prefixEq = do
      name <- atomP
      args <- parens (termP `sepBy` comma)
      (guard_, rhs) <- guardRhsP
      _ <- symbol "."
      pure (FunctionEquation name args guard_ rhs)
    operatorEq = do
      lhs <- termP
      case lhs of
        CompoundTerm (Unqualified name) args -> do
          (guard_, rhs) <- guardRhsP
          _ <- symbol "."
          pure (FunctionEquation name args guard_ rhs)
        _ -> fail "expected function equation"
    guardRhsP = do
      startPos <- getSourcePos
      choice
        [ do
            _ <- symbol "|"
            gs <- termP `sepBy1` comma
            _ <- symbol "->"
            rhsPos <- getSourcePos
            rhs <- termP
            pure (Ann gs (sourceLocFromPos startPos), Ann rhs (sourceLocFromPos rhsPos)),
          do
            _ <- symbol "->"
            rhsPos <- getSourcePos
            rhs <- termP
            pure (Ann [] (sourceLocFromPos startPos), Ann rhs (sourceLocFromPos rhsPos))
        ]

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

data ModuleItem
  = ItemDirective Directive
  | ItemRule Rule
  | ItemEquation (Ann FunctionEquation)

-- | Parse a complete CHR module.
moduleP :: Parser Module
moduleP = do
  items <-
    many
      ( choice
          [ ItemDirective <$> try directiveP,
            ItemEquation <$> try functionEquationP,
            ItemRule <$> ruleP
          ]
      )
  let dirs = [d | ItemDirective d <- items]
      rules = [r | ItemRule r <- items]
      eqs = [e | ItemEquation e <- items]
      (modName_, modExports_) = case [(n, e) | DirModule n e <- dirs] of
        ((n, e) : _) -> (n, Just e)
        [] -> (T.empty, Nothing)
      modImports_ = [n | DirImport n <- dirs]
      modDecls_ =
        concat [ds | DirConstraintDecl ds <- dirs]
          ++ concat [ds | DirFunctionDecl ds <- dirs]
  pure (Module modName_ modImports_ modDecls_ rules eqs modExports_)

-- ---------------------------------------------------------------------------
-- First-pass operator collector
-- ---------------------------------------------------------------------------

-- | Plain parser type for the first-pass collector (no ReaderT needed).
type Parser' = Parsec Void Text

-- | Collect operator declarations from a module's @:- module(...)@ directive.
--
-- Since the module directive is always at the top of the file, this parser
-- consumes leading whitespace, attempts to parse a @:- module(Name, [...]).@
-- directive, extracts any @op(...)@ entries from the export list, and returns
-- them. If no module directive is found, returns @[]@.
collectOperatorDecls :: String -> Text -> Either (ParseErrorBundle Text Void) [OpDecl]
collectOperatorDecls = parse (sc' *> collectP)
  where
    sc' :: Parser' ()
    sc' = L.space space1 (L.skipLineComment "%") empty

    lexeme' :: Parser' a -> Parser' a
    lexeme' = L.lexeme sc'

    symbol' :: Text -> Parser' Text
    symbol' = L.symbol sc'

    atomP' :: Parser' Text
    atomP' = lexeme' (unquotedP <|> quotedP)
      where
        unquotedP = do
          name <- (:) <$> lowerChar <*> many (alphaNumChar <|> char '_')
          pure (T.pack name)
        quotedP = T.pack <$> (char '\'' *> go)
          where
            go =
              choice
                [ do
                    _ <- char '\''
                    choice
                      [ char '\'' *> (('\'' :) <$> go),
                        pure []
                      ],
                  do
                    _ <- char '\\'
                    c <- anySingle
                    (c :) <$> go,
                  do
                    c <- satisfy (\c -> c /= '\'' && c /= '\\')
                    (c :) <$> go
                ]

    symbolAtomP' :: Parser' Text
    symbolAtomP' = lexeme' $ T.pack <$> some (oneOf symbolChars)

    commaP :: Parser' ()
    commaP = void (symbol' ",")

    opTypeP' :: Parser' OpType
    opTypeP' =
      lexeme' $
        choice
          [ InfixL_ <$ try (string "yfx" <* notFollowedBy alphaNumChar),
            InfixR_ <$ try (string "xfy" <* notFollowedBy alphaNumChar),
            InfixN_ <$ try (string "xfx" <* notFollowedBy alphaNumChar),
            Prefix_ <$ try (string "fx" <* notFollowedBy alphaNumChar),
            Postfix_ <$ try (string "xf" <* notFollowedBy alphaNumChar)
          ]

    -- Parse a single export item: either op(...) returning Just, or name/arity returning Nothing.
    exportItemP' :: Parser' (Maybe OpDecl)
    exportItemP' = try opDeclP' <|> (Nothing <$ declP')
      where
        opDeclP' = do
          _ <- symbol' "op"
          _ <- symbol' "("
          fix <- lexeme' L.decimal
          when (fix < 1 || fix > 1199) $
            fail ("operator fixity must be between 1 and 1199, got: " ++ show fix)
          _ <- commaP
          ty <- opTypeP'
          _ <- commaP
          name <- atomP' <|> symbolAtomP'
          _ <- symbol' ")"
          pure (Just (OpDecl fix ty name))
        declP' = do
          _ <- atomP'
          _ <- symbol' "/"
          _ <- lexeme' (L.decimal :: Parser' Int)
          pure ()

    collectP :: Parser' [OpDecl]
    collectP =
      option [] $ try $ do
        _ <- symbol' ":-"
        _ <- symbol' "module"
        _ <- symbol' "("
        _ <- atomP' -- module name
        _ <- commaP
        _ <- symbol' "["
        items <- exportItemP' `sepBy` commaP
        _ <- symbol' "]"
        _ <- symbol' ")"
        _ <- symbol' "."
        pure [op | Just op <- items]

-- | Extract operator declarations from an already-parsed module's export list.
extractOpDecls :: Module -> [OpDecl]
extractOpDecls m = case m.exports of
  Nothing -> []
  Just exports -> [op | OperatorDecl op <- exports]
