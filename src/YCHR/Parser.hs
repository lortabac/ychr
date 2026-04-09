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
    parseConstraint,
    parseQuery,
    parseQueryWith,
    parseTerm,
    parseTermWith,
    parseRule,
    OpTable,
    builtinOps,
    mergeOps,
    opTableEntries,
    collectOperatorDecls,
    extractOpDecls,
  )
where

import Control.Monad (foldM, void, when)
import Control.Monad.Combinators.Expr (Operator (..), makeExprParser)
import Control.Monad.Trans.Reader (ReaderT, ask, runReaderT)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict qualified as Map
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
    -- them in 'atomP'.  See Note [Two atom rejection mechanisms].
    wordOpSet :: Set Text
  }
  deriving (Show)

-- | Built-in operators at their standard Prolog fixity levels.
builtinOps :: OpTable
builtinOps =
  mkOpTable
    [ (400, [(InfixN_, "/")]),
      (700, [(InfixN_, "is"), (InfixN_, "=")]),
      (1100, [(InfixN_, "\\")]),
      (1180, [(InfixN_, "<=>"), (InfixN_, "==>")]),
      (1200, [(Prefix_, ":-")])
    ]

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
  checkConflicts
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
    checkConflicts :: Either Text ()
    checkConflicts =
      let existing =
            [ (name, (fix, ty))
            | (fix, ops) <- IntMap.toList base.opsByFixity,
              (ty, name) <- ops
            ]
          newOps = [(d.opName, (d.fixity, d.opType)) | d <- decls]
          -- Build a map from operator name to its (fixity, type).  If two
          -- entries for the same name disagree, report a conflict.
          insert (n, ft) acc = case Map.lookup n acc of
            Nothing -> Right (Map.insert n ft acc)
            Just ft' | ft == ft' -> Right acc
            Just _ -> Left n
       in foldM (flip insert) Map.empty (existing ++ newOps) *> pure ()

-- | Check whether a name consists entirely of symbol characters.
isSymbolic :: Text -> Bool
isSymbolic = T.all (`elem` symbolChars)

-- | Characters that can appear in symbol operators.
symbolChars :: [Char]
symbolChars = ":=<>+-*/#@^~!&?"

-- | List all operator entries in an 'OpTable' as @(fixity, type, name)@
-- triples. The order is unspecified.
opTableEntries :: OpTable -> [(Int, OpType, Text)]
opTableEntries table =
  [ (fix, ty, name)
  | (fix, ops) <- IntMap.toList table.opsByFixity,
    (ty, name) <- ops
  ]

-- | Convert an 'OpTable' to the format expected by 'makeExprParser'.
-- See Note [Prolog fixity vs makeExprParser precedence].
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
-- See Note [Two atom rejection mechanisms].
reservedWords :: [Text]
reservedWords = ["is", "fun"]

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
        else
          if "__" `T.isInfixOf` t
            then fail "double underscore (__) is not allowed in atoms"
            else pure t
    quotedP = do
      t <- T.pack <$> (char '\'' *> go)
      if "__" `T.isInfixOf` t
        then fail "double underscore (__) is not allowed in atoms"
        else pure t
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
-- See Note [Longest-match symbol operators].
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

-- | Parse a lambda expression: @fun(X, Y) -> body@.
--
-- Produces @CompoundTerm (Unqualified "->") [CompoundTerm (Unqualified "fun") params, body]@.
lambdaP :: Parser Term
lambdaP = do
  _ <- wordOp "fun"
  params <- parens (varP `sepBy1` comma)
  _ <- symbol "->"
  body <- termP
  pure (CompoundTerm (Unqualified "->") [CompoundTerm (Unqualified "fun") params, body])

-- | Parse an atomic (non-operator) term.
atomicTermP :: Parser Term
atomicTermP =
  choice
    [ try lambdaP,
      wildcardP,
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
--
-- A qualified name without arguments (e.g. @order:leq@) still produces a
-- @'CompoundTerm' (Qualified ...) []@ rather than an 'AtomTerm', because
-- 'AtomTerm' does not carry a 'Name' — only a plain 'Text'.
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
  | DirTypeDecl [Ann TypeDefinition]
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
    "chr_type" -> do
      td <- typeDefinitionP
      _ <- symbol "."
      pure (DirTypeDecl [td])
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

-- | Parse a single export item: @name\/arity@, @op(fixity, type, name)@, or @type(name\/arity)@.
exportItemP :: Parser Declaration
exportItemP = try opDeclP <|> try typeExportP <|> ((.node) <$> constraintDeclP)

-- | Parse a type export declaration: @type(name\/arity)@.
typeExportP :: Parser Declaration
typeExportP = do
  _ <- symbol "type"
  _ <- symbol "("
  name <- atomP
  _ <- symbol "/"
  a <- lexeme L.decimal
  _ <- symbol ")"
  pure (TypeExportDecl name a)

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

-- | Parse a single constraint declaration: @name\/arity@ or @name(type, ...)@.
constraintDeclP :: Parser (Ann Declaration)
constraintDeclP = withLoc $ do
  name <- atomP
  try (typedConstraint name) <|> untypedConstraint name
  where
    typedConstraint name = do
      args <- parens (typeExprP `sepBy` comma)
      pure (ConstraintDecl name (length args) (Just args))
    untypedConstraint name = do
      _ <- symbol "/"
      arity <- lexeme L.decimal
      pure (ConstraintDecl name arity Nothing)

-- | Parse a single function declaration: @name\/arity@ or @name(type, ...) -> type@.
functionDeclP :: Parser (Ann Declaration)
functionDeclP = withLoc $ do
  name <- atomP
  try (typedFunction name) <|> untypedFunction name
  where
    typedFunction name = do
      args <- parens (typeExprP `sepBy` comma)
      _ <- symbol "->"
      ret <- typeExprP
      pure (FunctionDecl name (length args) (Just args) (Just ret))
    untypedFunction name = do
      _ <- symbol "/"
      arity <- lexeme L.decimal
      pure (FunctionDecl name arity Nothing Nothing)

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

-- ---------------------------------------------------------------------------
-- Type declarations
-- ---------------------------------------------------------------------------

-- | Parse a type definition: @name(Vars) ---> con1 ; con2 ; ...@
typeDefinitionP :: Parser (Ann TypeDefinition)
typeDefinitionP = withLoc $ do
  tname <- atomP
  tvars <- option [] (parens (typeVarNameP `sepBy1` comma))
  _ <- symbol "--->"
  cons <- dataConstructorP `sepBy1` symbol ";"
  pure (TypeDefinition (Unqualified tname) tvars cons)

-- | Parse an uppercase type variable name (just the text, not a TypeExpr).
typeVarNameP :: Parser Text
typeVarNameP = lexeme $ do
  c <- upperChar
  rest <- many (alphaNumChar <|> char '_')
  pure (T.pack (c : rest))

-- | Parse a data constructor: bare atom, @name(args)@, @[]@, or @[H|T]@.
dataConstructorP :: Parser DataConstructor
dataConstructorP =
  choice
    [ try listConsP,
      emptyListConsP,
      namedConsP
    ]
  where
    namedConsP = do
      cname <- atomP
      args <- option [] (parens (typeExprP `sepBy1` comma))
      pure (DataConstructor (Unqualified cname) args)
    emptyListConsP = do
      _ <- symbol "["
      _ <- symbol "]"
      pure (DataConstructor (Unqualified "[]") [])
    listConsP = do
      _ <- symbol "["
      elems <- typeExprP `sepBy1` comma
      _ <- symbol "|"
      tl <- typeExprP
      _ <- symbol "]"
      pure (DataConstructor (Unqualified ".") (elems ++ [tl]))

-- | Parse a type expression: variable, type constructor, or list sugar.
typeExprP :: Parser TypeExpr
typeExprP =
  choice
    [ try listTypeConsP,
      emptyListTypeP,
      typeVarP,
      typeConP
    ]
  where
    typeVarP = TypeVar <$> typeVarNameP
    typeConP = do
      tname <- atomP
      args <- option [] (parens (typeExprP `sepBy1` comma))
      pure (TypeCon (Unqualified tname) args)
    emptyListTypeP = do
      _ <- symbol "["
      _ <- symbol "]"
      pure (TypeCon (Unqualified "[]") [])
    listTypeConsP = do
      _ <- symbol "["
      elems <- typeExprP `sepBy1` comma
      _ <- symbol "|"
      tl <- typeExprP
      _ <- symbol "]"
      pure (TypeCon (Unqualified ".") (elems ++ [tl]))

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
--
-- If multiple @:- module(...)@ directives appear, only the first is used.
-- Unknown directives are silently skipped.
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
        [] -> ("<no_module>", Nothing)
      modImports_ = [n | DirImport n <- dirs]
      modDecls_ =
        concat [ds | DirConstraintDecl ds <- dirs]
          ++ concat [ds | DirFunctionDecl ds <- dirs]
      modTypeDecls_ = concat [ds | DirTypeDecl ds <- dirs]
  pure (Module modName_ modImports_ modDecls_ modTypeDecls_ rules eqs modExports_)

-- ---------------------------------------------------------------------------
-- First-pass operator collector
-- ---------------------------------------------------------------------------

-- | Plain parser type for the first-pass collector.
-- See Note [First-pass operator collector].
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
    exportItemP' = try opDeclP' <|> try (Nothing <$ typeExportP') <|> (Nothing <$ declP')
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
        typeExportP' = do
          _ <- symbol' "type"
          _ <- symbol' "("
          _ <- atomP'
          _ <- symbol' "/"
          _ <- lexeme' (L.decimal :: Parser' Int)
          symbol' ")"
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

-- ---------------------------------------------------------------------------
-- Notes
-- ---------------------------------------------------------------------------

-- Note [Two atom rejection mechanisms]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- 'atomP' rejects unquoted atoms via two mechanisms:
--
-- 1. 'reservedWords': a static list of words that are always reserved (e.g.
--    "is").  These are built-in operators whose keywords must never parse as
--    atoms regardless of the operator table.
--
-- 2. 'wordOpSet': the set of non-symbolic operator names from the current
--    'OpTable'.  This is dynamically populated from user-defined operator
--    declarations.  For example, if the user declares @op(700, xfx, div)@,
--    then "div" will be rejected as an atom.
--
-- The two mechanisms are complementary: 'reservedWords' covers the built-in
-- operators that must be rejected even when the 'OpTable' is empty (e.g.
-- during first-pass collection), and 'wordOpSet' covers user-defined word
-- operators that only exist after the operator table is populated.

-- Note [Longest-match symbol operators]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- 'symbolOp' parses symbol operators by reading the longest run of symbol
-- characters and then checking whether the result matches the expected
-- operator.  This avoids prefix ambiguity: without longest-match, parsing
-- @=<@ could succeed on just @=@ and leave @<@ unconsumed.  By reading
-- greedily and comparing, we ensure that @=@ only matches when not followed
-- by more symbol characters (e.g. it won't match the @=@ in @=<@).

-- Note [Prolog fixity vs makeExprParser precedence]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- In Prolog, a /lower/ fixity number means /higher/ precedence (tighter
-- binding).  For example, @*@ at fixity 400 binds tighter than @+@ at 500.
-- 'makeExprParser' from @parser-combinators@ expects operator groups in
-- /descending/ precedence order (tightest first).  Since 'IntMap.toAscList'
-- returns keys in ascending numeric order, and ascending fixity numbers
-- correspond to descending precedence, the two conventions align without
-- any reversal.

-- Note [First-pass operator collector]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- 'collectOperatorDecls' duplicates several lexer/parser primitives (atom
-- parsing, operator type parsing, etc.) using the plain 'Parser'' type
-- instead of the 'ReaderT OpTable' 'Parser' type.  This is intentional:
-- the first pass runs /before/ the operator table is known, so it cannot
-- use 'Parser' (which requires an 'OpTable' in its reader environment).
-- It only needs to extract @op(...)@ entries from the module directive's
-- export list, so the duplicated parsers are simpler (e.g. 'atomP'' does
-- not reject word operators, since the operator table doesn't exist yet).
