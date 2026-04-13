{-# LANGUAGE OverloadedStrings #-}

-- | Generic Prolog-like term parser.
--
-- Parses source text into a flat list of dot-terminated, source-annotated
-- terms. Operators are handled via a configurable operator table.
--
-- This module is self-contained: it defines its own 'PExpr' and 'OpTable'
-- types independently of 'YCHR.Parser'.
--
-- @
-- % Line comments
-- f(X, Y).
-- X + Y * Z.
-- [a, b | T].
-- @
module YCHR.PExpr
  ( -- * Prolog expressions
    PExpr (..),

    -- * Operator table
    OpTable (..),
    OpType (..),
    mkOpTable,
    mergeOps,
    opTableEntries,
    isInfix,
    isPrefix,
    isPostfix,

    -- * Precedence constants
    maxPrec,
    maxArgPrec,

    -- * Parsing
    parseTerms,
    parseTerm,
    parseTermNoDot,
    parseFirstTerm,

    -- * Pretty-printing
    prettyPExpr,
  )
where

import Control.Monad (foldM, void)
import Data.Char (isAlphaNum, isLower)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Language.Haskell.TH.Syntax (Lift)
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L
import YCHR.Loc

-- ---------------------------------------------------------------------------
-- Terms
-- ---------------------------------------------------------------------------

-- | A Prolog-like term.
data PExpr
  = -- | Uppercase variable (e.g. @X@, @Foo@).
    Var Text
  | -- | Integer literal.
    Int Int
  | -- | Atom (lowercase identifier or single-quoted string).
    Atom Text
  | -- | Double-quoted string literal.
    Str Text
  | -- | Compound term: functor and annotated arguments.
    -- Operator expressions are also compounds (e.g. @X + Y@ is
    -- @Compound "+" [X, Y]@).
    Compound Text [Ann PExpr]
  | -- | Anonymous variable (@_@).
    Wildcard
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Operator table
-- ---------------------------------------------------------------------------

-- | Operator associativity and fixity kind, using Prolog specifier notation.
--
-- Infix operators: @xfx@ (non-associative), @xfy@ (right-associative),
-- @yfx@ (left-associative).
-- Prefix operators: @fx@ (non-chaining), @fy@ (chaining).
-- Postfix operators: @xf@ (non-chaining), @yf@ (chaining).
--
-- An @x@ position requires the argument to have strictly lower fixity
-- (tighter binding) than the operator.  A @y@ position allows equal fixity.
data OpType
  = Xfx
  | Xfy
  | Yfx
  | Fx
  | Fy
  | Xf
  | Yf
  deriving (Show, Eq, Lift)

-- | Is the operator an infix operator?
isInfix :: OpType -> Bool
isInfix Xfx = True
isInfix Xfy = True
isInfix Yfx = True
isInfix _ = False

-- | Is the operator a prefix operator?
isPrefix :: OpType -> Bool
isPrefix Fx = True
isPrefix Fy = True
isPrefix _ = False

-- | Is the operator a postfix operator?
isPostfix :: OpType -> Bool
isPostfix Xf = True
isPostfix Yf = True
isPostfix _ = False

-- | Operator table: maps fixity level to a list of operators at that level.
--
-- Lower fixity number means higher precedence (tighter binding), following
-- the Prolog convention.
--
-- Dual-role operators (e.g. @-@ as both @fy 200@ and @yfx 500@) are
-- supported: the prefix entry goes in 'prefixByName' and the infix entry
-- in 'infixByName'.
data OpTable = OpTable
  { opsByFixity :: IntMap [(OpType, Text)],
    -- | Precomputed set of non-symbolic operator names, used to reject
    -- them as atoms.
    wordOpSet :: Set Text,
    -- | Prefix operators indexed by name.
    prefixByName :: Map Text (Int, OpType),
    -- | Infix and postfix operators indexed by name.
    infixByName :: Map Text (Int, OpType)
  }
  deriving (Show)

-- | Build an 'OpTable' from a list of @(fixity, operators)@ pairs.
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
          ],
      prefixByName =
        Map.fromList
          [ (name, (fix, ty))
          | (fix, ops) <- entries,
            (ty, name) <- ops,
            isPrefix ty
          ],
      infixByName =
        Map.fromList
          [ (name, (fix, ty))
          | (fix, ops) <- entries,
            (ty, name) <- ops,
            isInfix ty || isPostfix ty
          ]
    }

-- | Merge additional operators into an existing table.
-- Returns @Left name@ if an operator conflicts (same name, same category
-- but different fixity or type).  Dual-role operators (prefix + infix)
-- are allowed.
mergeOps :: OpTable -> [(Int, OpType, Text)] -> Either Text OpTable
mergeOps base decls = do
  checkConflicts
  let userEntries =
        [ (fix, [(ty, name)])
        | (fix, ty, name) <- decls
        ]
  pure
    OpTable
      { opsByFixity =
          IntMap.unionWith (++) base.opsByFixity (IntMap.fromListWith (++) userEntries),
        wordOpSet =
          Set.union
            base.wordOpSet
            (Set.fromList [name | (_, _, name) <- decls, not (isSymbolic name)]),
        prefixByName =
          Map.union
            base.prefixByName
            (Map.fromList [(name, (fix, ty)) | (fix, ty, name) <- decls, isPrefix ty]),
        infixByName =
          Map.union
            base.infixByName
            ( Map.fromList
                [(name, (fix, ty)) | (fix, ty, name) <- decls, isInfix ty || isPostfix ty]
            )
      }
  where
    checkConflicts :: Either Text ()
    checkConflicts =
      let -- Check prefix ops for conflicts
          existingPrefix = Map.toList base.prefixByName
          newPrefix = [(name, (fix, ty)) | (fix, ty, name) <- decls, isPrefix ty]
          -- Check infix/postfix ops for conflicts
          existingInfix = Map.toList base.infixByName
          newInfix =
            [(name, (fix, ty)) | (fix, ty, name) <- decls, isInfix ty || isPostfix ty]
          insert (n, ft) acc = case Map.lookup n acc of
            Nothing -> Right (Map.insert n ft acc)
            Just ft' | ft == ft' -> Right acc
            Just _ -> Left n
       in foldM (flip insert) Map.empty (existingPrefix ++ newPrefix)
            *> foldM (flip insert) Map.empty (existingInfix ++ newInfix)
            *> pure ()

-- | List all operator entries as @(fixity, type, name)@ triples.
opTableEntries :: OpTable -> [(Int, OpType, Text)]
opTableEntries table =
  [ (fix, ty, name)
  | (fix, ops) <- IntMap.toList table.opsByFixity,
    (ty, name) <- ops
  ]

-- ---------------------------------------------------------------------------
-- Precedence constants
-- ---------------------------------------------------------------------------

-- | Maximum operator precedence (Prolog standard: 1200).
maxPrec :: Int
maxPrec = 1200

-- | Maximum precedence for compound-term arguments (999).
-- Operators at fixity 1000 or above (like @,@) act as separators inside
-- @f(...)@ and @[...]@ because they exceed this limit.
maxArgPrec :: Int
maxArgPrec = 999

-- ---------------------------------------------------------------------------
-- Internal helpers
-- ---------------------------------------------------------------------------

-- | Check whether a name consists entirely of symbol characters.
isSymbolic :: Text -> Bool
isSymbolic = T.all (`elem` symbolChars)

-- | Characters that can appear in symbol operators.
symbolChars :: [Char]
symbolChars = "\\:=<>+-*/#@^~!&?"

-- ---------------------------------------------------------------------------
-- Parser type
-- ---------------------------------------------------------------------------

type Parser = Parsec Void Text

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

-- | Parse a comma separator.
comma :: Parser ()
comma = void (symbol ",")

-- ---------------------------------------------------------------------------
-- Source locations
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

-- ---------------------------------------------------------------------------
-- Atoms, variables, wildcards, integers
-- ---------------------------------------------------------------------------

-- | Parse an atom: a lowercase identifier or a single-quoted string.
--
-- Rejects identifiers that are prefix word operators (e.g.
-- @chr_constraint@, @dynamic@) so that the Pratt parser can handle
-- them.  Infix-only word operators (e.g. @div@, @mod@, @is@) are
-- allowed as atoms, following standard Prolog behaviour.
atomP :: OpTable -> Parser Text
atomP table = lexeme (unquotedP <|> quotedAtomP)
  where
    unquotedP = do
      t <- identifierP
      -- Reject only word operators that are prefix operators.
      -- Infix-only word operators (like div, mod) are valid atoms.
      if Set.member t table.wordOpSet && Map.member t table.prefixByName
        then fail ("reserved word: " ++ T.unpack t)
        else pure t

-- | Parse an unquoted lowercase identifier.  Does not reject word operators
-- or double underscores — callers are responsible for validation.
identifierP :: Parser Text
identifierP = do
  name <- (:) <$> lowerChar <*> many (alphaNumChar <|> char '_')
  let t = T.pack name
  if "__" `T.isInfixOf` t
    then fail "double underscore (__) is not allowed in atoms"
    else pure t

-- | Parse a single-quoted atom (e.g. @\'hello world\'@).
quotedAtomP :: Parser Text
quotedAtomP = do
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
              [ char '\'' *> (('\'' :) <$> go),
                pure []
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
        [ '\'' <$ char '\'',
          '\\' <$ char '\\',
          '\n' <$ char 'n',
          '\t' <$ char 't',
          anySingle
        ]

-- | Parse a variable (uppercase identifier).
varP :: Parser PExpr
varP = lexeme $ do
  c <- upperChar
  rest <- many (alphaNumChar <|> char '_')
  pure (Var (T.pack (c : rest)))

-- | Parse a wildcard: bare @_@ not followed by a word character.
wildcardP :: Parser PExpr
wildcardP = lexeme $ do
  _ <- char '_'
  notFollowedBy (alphaNumChar <|> char '_')
  pure Wildcard

-- | Parse a decimal integer (optionally negative).
intP :: Parser PExpr
intP = lexeme $ do
  sign <- optional (char '-')
  n <- L.decimal
  pure (Int (maybe n (const (negate n)) sign))

-- ---------------------------------------------------------------------------
-- Operator tokens
-- ---------------------------------------------------------------------------

-- | Try to parse any operator token.  Tries symbol operators (greedy
-- longest-match), then single-character operators (@,@ and @|@), then
-- word operators.
anyOpToken :: OpTable -> Parser Text
anyOpToken table = lexeme (trySymbol <|> trySingleChar <|> tryWord)
  where
    trySymbol = try $ do
      s <- T.pack <$> some (oneOf symbolChars)
      if Map.member s table.prefixByName || Map.member s table.infixByName
        then pure s
        else fail ("unknown operator: " ++ T.unpack s)
    trySingleChar = try $ do
      c <- oneOf (",|;" :: [Char])
      let name = T.singleton c
      if Map.member name table.prefixByName || Map.member name table.infixByName
        then pure name
        else fail ("not an operator: " ++ [c])
    tryWord = try $ do
      w <- T.pack <$> ((:) <$> lowerChar <*> many (alphaNumChar <|> char '_'))
      if Set.member w table.wordOpSet
        then w <$ notFollowedBy (alphaNumChar <|> char '_')
        else fail ("not a word operator: " ++ T.unpack w)

-- ---------------------------------------------------------------------------
-- Terms
-- ---------------------------------------------------------------------------

-- | Parse a double-quoted string literal.
stringP :: Parser PExpr
stringP = lexeme $ Str . T.pack <$> (char '"' *> go)
  where
    go =
      choice
        [ do
            _ <- char '"'
            pure [],
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
        [ '"' <$ char '"',
          '\\' <$ char '\\',
          '\n' <$ char 'n',
          '\t' <$ char 't',
          anySingle
        ]

-- | Parse a list term using Prolog list notation.
-- Desugars to nested @Compound "." [H, T]@ terms, with @Atom "[]"@ for
-- the empty list.
listTermP :: OpTable -> Parser PExpr
listTermP table = between (symbol "[") (symbol "]") listBody
  where
    listBody = do
      elems <- withLoc (termP table maxArgPrec) `sepBy` comma
      tail_ <- option (noAnn (Atom "[]")) (symbol "|" *> withLoc (termP table maxArgPrec))
      pure (foldr (\h t -> Compound "." [h, noAnn t]) (tail_.node) elems)

-- | Parse a lambda expression: @fun(X, Y) -> body end@.
--
-- Produces @Compound "->" [Compound "fun" [X, Y], body]@.
-- The @end@ keyword delimits the body, making the entire lambda an
-- atomic term that works inside compound-term arguments without
-- parentheses.  The body is parsed at 'maxPrec', so any operators
-- (including @,@ and @|@) may appear inside.
--
-- This is syntactic sugar: @fun(X) -> X + 1 end@ desugars to the
-- same representation as @\'->'(fun(X), X + 1)@.
lambdaP :: OpTable -> Parser PExpr
lambdaP table = try $ do
  _ <- lexeme (string "fun" <* notFollowedBy (alphaNumChar <|> char '_'))
  params <- parens (withLoc (termP table maxArgPrec) `sepBy` comma)
  _ <- symbol "->"
  body <- withLoc (termP table maxPrec)
  _ <- lexeme (string "end" <* notFollowedBy (alphaNumChar <|> char '_'))
  pure (Compound "->" [noAnn (Compound "fun" params), body])

-- | Parse an atomic (non-operator) term.
atomicTermP :: OpTable -> Parser (Ann PExpr)
atomicTermP table =
  withLoc $
    choice
      [ wildcardP,
        varP,
        try intP,
        stringP,
        listTermP table,
        lambdaP table,
        try (parens (termP table maxPrec)),
        atomOrCompoundP table
      ]

-- | Parse a term with a maximum allowed fixity.
--
-- Only operators with fixity @<= maxFix@ are consumed.  This is the
-- mechanism that makes @,@ (fixity 1000) act as a separator inside
-- compound-term arguments (parsed at 'maxArgPrec' = 999) while being
-- a real operator at the top level (parsed at 'maxPrec' = 1200).
termP :: OpTable -> Int -> Parser PExpr
termP table maxFix = do
  (lhs, lhsFix) <- nudP table maxFix
  (.node) <$> ledLoop table maxFix lhs lhsFix

-- | Parse a prefix expression or atomic term.
-- Returns @(term, effectiveFixity)@; atomic terms have fixity 0.
nudP :: OpTable -> Int -> Parser (Ann PExpr, Int)
nudP table maxFix = try atomicTerm <|> prefixOp
  where
    atomicTerm = (,0) <$> atomicTermP table
    prefixOp = try $ do
      sp <- getSourcePos
      name <- anyOpToken table
      case Map.lookup name table.prefixByName of
        Just (fix, ty) | fix <= maxFix -> do
          let operandMax = case ty of
                Fy -> fix -- y position: operand may have equal fixity
                _ -> fix - 1 -- x position (Fx): strictly lower
          operand <- withLoc (termP table operandMax)
          pure (Ann (Compound name [operand]) (sourceLocFromPos sp), fix)
        _ -> fail ("not a prefix operator in this context: " ++ T.unpack name)

-- | Infix\/postfix loop for the Pratt parser.
--
-- Repeatedly tries to consume an infix or postfix operator whose fixity
-- is within the allowed range and whose left-position constraint is
-- satisfied by the current left-hand side.
ledLoop :: OpTable -> Int -> Ann PExpr -> Int -> Parser (Ann PExpr)
ledLoop table maxFix lhs lhsFix = do
  mOp <- optional (lookAhead (try (anyOpToken table)))
  case mOp of
    Just name
      | Just (fix, ty) <- Map.lookup name table.infixByName,
        fix <= maxFix,
        lhsFix <= leftMax ty fix -> do
          _ <- anyOpToken table -- consume
          case ty of
            _ | isPostfix ty -> do
              let result = Ann (Compound name [lhs]) lhs.sourceLoc
              ledLoop table maxFix result fix
            Yfx -> do
              rhs <- withLoc (termP table (fix - 1))
              let result = Ann (Compound name [lhs, rhs]) lhs.sourceLoc
              ledLoop table maxFix result fix
            Xfy -> do
              rhs <- withLoc (termP table fix)
              let result = Ann (Compound name [lhs, rhs]) lhs.sourceLoc
              ledLoop table maxFix result fix
            _ -> do
              -- Xfx (non-associative)
              rhs <- withLoc (termP table (fix - 1))
              let result = Ann (Compound name [lhs, rhs]) lhs.sourceLoc
              ledLoop table maxFix result fix
    _ -> pure lhs

-- | Maximum allowed fixity for the left argument of an operator.
-- @y@ positions allow equal fixity; @x@ positions require strictly lower.
leftMax :: OpType -> Int -> Int
leftMax Yfx fix = fix
leftMax Yf fix = fix
leftMax _ fix = fix - 1

-- | Parse an atom optionally followed by a parenthesised argument list.
--
-- Word operators are allowed as atoms and functors following standard
-- Prolog behaviour (e.g. @div@ is a valid atom and @div(X, Y)@ is a
-- valid compound even though @div@ is an operator).  Only prefix word
-- operators (e.g. @chr_constraint@) are rejected as bare atoms so that
-- the Pratt parser can handle them — but they are still allowed as
-- functors when followed by @(@.
atomOrCompoundP :: OpTable -> Parser PExpr
atomOrCompoundP table = prefixWordAsFunctor <|> regular
  where
    -- Prefix word operators are rejected by atomP, but we still allow
    -- them as functors when followed by '('.
    prefixWordAsFunctor = try $ do
      name <- lexeme identifierP
      if not (Set.member name table.wordOpSet && Map.member name table.prefixByName)
        then fail "not a prefix word operator"
        else do
          _ <- symbol "("
          args <- withLoc (termP table maxArgPrec) `sepBy` comma
          _ <- symbol ")"
          pure (Compound name args)
    regular = do
      name <- atomP table
      maybeOpen <- optional (symbol "(")
      case maybeOpen of
        Nothing -> pure (Atom name)
        Just _ -> do
          args <- withLoc (termP table maxArgPrec) `sepBy` comma
          _ <- symbol ")"
          pure (Compound name args)

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

-- | Parse dot-terminated Prolog terms from source text.
--
-- Each top-level term must be terminated by a dot (@.@).
-- Returns a list of annotated terms.
--
-- The first argument is the operator table. The second is the source file
-- name (used in error messages only).
parseTerms :: OpTable -> String -> Text -> Either (ParseErrorBundle Text Void) [Ann PExpr]
parseTerms table = parse (sc *> many (withLoc (termP table maxPrec) <* symbol ".") <* eof)

-- | Parse a single dot-terminated term from source text.
parseTerm :: OpTable -> String -> Text -> Either (ParseErrorBundle Text Void) (Ann PExpr)
parseTerm table = parse (sc *> withLoc (termP table maxPrec) <* symbol "." <* eof)

-- | Parse a single term from source text (no dot terminator required).
parseTermNoDot :: OpTable -> String -> Text -> Either (ParseErrorBundle Text Void) (Ann PExpr)
parseTermNoDot table = parse (sc *> withLoc (termP table maxPrec) <* eof)

-- | Parse the first dot-terminated term from source text, ignoring the rest.
-- Returns 'Nothing' if the input is empty or starts with something that is
-- not a valid term with the given operator table.
parseFirstTerm :: OpTable -> String -> Text -> Either (ParseErrorBundle Text Void) (Maybe (Ann PExpr))
parseFirstTerm table = parse (sc *> optional (try (withLoc (termP table maxPrec) <* symbol ".")) <* void takeRest)

-- ---------------------------------------------------------------------------
-- Pretty-printing
-- ---------------------------------------------------------------------------

-- | Render a 'PExpr' as valid Prolog source text.
--
-- Uses the operator table to decide which compounds to render as infix,
-- prefix, or postfix operators, with minimal parenthesisation based on
-- precedence.
prettyPExpr :: OpTable -> PExpr -> String
prettyPExpr table = prettyPrec table.infixByName table.prefixByName table.wordOpSet maxPrec

-- | Render a PExpr within a precedence context.
--
-- The @ctx@ parameter is the maximum fixity the expression may have without
-- needing parentheses. An operator with fixity > ctx is wrapped in parens.
--
-- Prolog operator argument conventions:
--
--   * @y@ — argument may have equal or lower fixity (same or tighter binding)
--   * @x@ — argument must have strictly lower fixity (strictly tighter)
--
-- So for @yfx@ at fixity F: left gets F, right gets F−1.
-- For @xfy@: left gets F−1, right gets F. Etc.
prettyPrec :: Map Text (Int, OpType) -> Map Text (Int, OpType) -> Set Text -> Int -> PExpr -> String
prettyPrec _ _ _ _ (Var v) = T.unpack v
prettyPrec _ _ _ _ (Int n)
  | n < 0 = "(" ++ show n ++ ")"
  | otherwise = show n
prettyPrec _ _ _ _ (Atom "[]") = "[]"
prettyPrec _ _ wops _ (Atom a) = renderAtom wops a
prettyPrec _ _ _ _ (Str s) = renderString s
prettyPrec _ _ _ _ Wildcard = "_"
-- List syntax
prettyPrec iops pops wops _ (Compound "." [h, t]) =
  "[" ++ rec maxArgPrec h.node ++ prettyListTail iops pops wops t.node ++ "]"
  where
    rec = prettyPrec iops pops wops
-- Infix operators
prettyPrec iops pops wops ctx (Compound f [l, r])
  | Just (fix, ty) <- Map.lookup f iops,
    isInfix ty =
      let (lCtx, rCtx) = case ty of
            Yfx -> (fix, fix - 1)
            Xfy -> (fix - 1, fix)
            _ -> (fix - 1, fix - 1) -- Xfx
          rendered =
            rec lCtx l.node
              ++ " "
              ++ T.unpack f
              ++ " "
              ++ rec rCtx r.node
       in if fix > ctx then "(" ++ rendered ++ ")" else rendered
  where
    rec = prettyPrec iops pops wops
-- Prefix operators
prettyPrec iops pops wops ctx (Compound f [x])
  | Just (fix, ty) <- Map.lookup f pops,
    isPrefix ty =
      let argCtx = case ty of
            Fy -> fix
            _ -> fix - 1 -- Fx
          rendered = T.unpack f ++ " " ++ rec argCtx x.node
       in if fix > ctx then "(" ++ rendered ++ ")" else rendered
  where
    rec = prettyPrec iops pops wops
-- Postfix operators
prettyPrec iops pops wops ctx (Compound f [x])
  | Just (fix, ty) <- Map.lookup f iops,
    isPostfix ty =
      let argCtx = case ty of
            Yf -> fix
            _ -> fix - 1 -- Xf
          rendered = rec argCtx x.node ++ " " ++ T.unpack f
       in if fix > ctx then "(" ++ rendered ++ ")" else rendered
  where
    rec = prettyPrec iops pops wops
-- Regular compounds
prettyPrec iops pops wops _ (Compound f args) =
  renderAtom wops f
    ++ "("
    ++ intercalate ", " [prettyPrec iops pops wops maxArgPrec a.node | a <- args]
    ++ ")"

prettyListTail :: Map Text (Int, OpType) -> Map Text (Int, OpType) -> Set Text -> PExpr -> String
prettyListTail _ _ _ (Atom "[]") = ""
prettyListTail iops pops wops (Compound "." [h, t]) =
  ", " ++ rec h.node ++ prettyListTail iops pops wops t.node
  where
    rec = prettyPrec iops pops wops maxArgPrec
prettyListTail iops pops wops other = " | " ++ prettyPrec iops pops wops maxArgPrec other

-- | True if the atom needs single-quote wrapping.
needsQuoting :: Set Text -> Text -> Bool
needsQuoting wordOps t = case T.uncons t of
  Nothing -> True
  Just (c, cs) ->
    not
      ( isLower c
          && T.all (\x -> isAlphaNum x || x == '_') cs
          && not (Set.member t wordOps)
          && not ("__" `T.isInfixOf` t)
      )

-- | Render an atom, quoting with @\'...\'@ if necessary.
renderAtom :: Set Text -> Text -> String
renderAtom wordOps s
  | needsQuoting wordOps s = "'" ++ concatMap esc (T.unpack s) ++ "'"
  | otherwise = T.unpack s
  where
    esc '\'' = "''"
    esc c = [c]

-- | Render a double-quoted string literal with escape sequences.
renderString :: Text -> String
renderString s = "\"" ++ concatMap esc (T.unpack s) ++ "\""
  where
    esc '"' = "\\\""
    esc '\\' = "\\\\"
    esc '\n' = "\\n"
    esc '\t' = "\\t"
    esc c = [c]
