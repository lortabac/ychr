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
    OpTable,
    OpType (..),
    mkOpTable,
    mergeOps,
    opTableEntries,

    -- * Parsing
    parseTerms,

    -- * Pretty-printing
    prettyPExpr,
  )
where

import Control.Monad (foldM, void)
import Control.Monad.Combinators.Expr qualified as Expr
import Data.Char (isAlphaNum, isLower)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List (intercalate)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
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

-- | Operator associativity and fixity kind.
data OpType
  = InfixL
  | InfixR
  | InfixN
  | Prefix
  | Postfix
  deriving (Show, Eq)

-- | Operator table: maps fixity level to a list of operators at that level.
--
-- Lower fixity number means higher precedence (tighter binding), following
-- the Prolog convention.
data OpTable = OpTable
  { opsByFixity :: IntMap [(OpType, Text)],
    -- | Precomputed set of non-symbolic operator names, used to reject
    -- them as atoms.
    wordOpSet :: Set Text
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
          ]
    }

-- | Merge additional operators into an existing table.
-- Returns @Left name@ if an operator conflicts (same name, different
-- fixity or type).
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
            (Set.fromList [name | (_, _, name) <- decls, not (isSymbolic name)])
      }
  where
    checkConflicts :: Either Text ()
    checkConflicts =
      let existing =
            [ (name, (fix, ty))
            | (fix, ops) <- IntMap.toList base.opsByFixity,
              (ty, name) <- ops
            ]
          newOps = [(name, (fix, ty)) | (fix, ty, name) <- decls]
          insert (n, ft) acc = case Map.lookup n acc of
            Nothing -> Right (Map.insert n ft acc)
            Just ft' | ft == ft' -> Right acc
            Just _ -> Left n
       in foldM (flip insert) Map.empty (existing ++ newOps) *> pure ()

-- | List all operator entries as @(fixity, type, name)@ triples.
opTableEntries :: OpTable -> [(Int, OpType, Text)]
opTableEntries table =
  [ (fix, ty, name)
  | (fix, ops) <- IntMap.toList table.opsByFixity,
    (ty, name) <- ops
  ]

-- ---------------------------------------------------------------------------
-- Internal helpers
-- ---------------------------------------------------------------------------

-- | Check whether a name consists entirely of symbol characters.
isSymbolic :: Text -> Bool
isSymbolic = T.all (`elem` symbolChars)

-- | Characters that can appear in symbol operators.
symbolChars :: [Char]
symbolChars = ":=<>+-*/#@^~!&?"

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
-- Rejects identifiers containing @__@ (double underscore) and identifiers
-- that are word operators.
atomP :: Set Text -> Parser Text
atomP wordOps = lexeme (unquotedP <|> quotedP)
  where
    unquotedP = do
      name <- (:) <$> lowerChar <*> many (alphaNumChar <|> char '_')
      let t = T.pack name
      if Set.member t wordOps
        then fail ("word operator: " ++ name)
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

-- | Parse a word operator.
wordOp :: Text -> Parser Text
wordOp w = lexeme $ try $ do
  _ <- string w
  notFollowedBy (alphaNumChar <|> char '_')
  pure w

-- | Parse a symbol operator using longest-match.
symbolOp :: Text -> Parser Text
symbolOp op = lexeme $ try $ do
  s <- T.pack <$> some (oneOf symbolChars)
  if s == op
    then pure s
    else fail ("expected operator " ++ show op)

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
      elems <- withLoc (termP table) `sepBy` comma
      tail_ <- option (noAnn (Atom "[]")) (symbol "|" *> withLoc (termP table))
      pure (foldr (\h t -> Compound "." [h, noAnn t]) (tail_.node) elems)

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
        try (parens (termP table)),
        atomOrCompoundP table
      ]

-- | Parse a term, including infix operator expressions.
termP :: OpTable -> Parser PExpr
termP table =
  (.node) <$> Expr.makeExprParser (atomicTermP table) (buildExprOpTable table)

-- | Parse an atom optionally followed by a parenthesised argument list.
atomOrCompoundP :: OpTable -> Parser PExpr
atomOrCompoundP table = do
  name <- atomP table.wordOpSet
  maybeOpen <- optional (symbol "(")
  case maybeOpen of
    Nothing -> pure (Atom name)
    Just _ -> do
      args <- withLoc (termP table) `sepBy` comma
      _ <- symbol ")"
      pure (Compound name args)

-- ---------------------------------------------------------------------------
-- Operator table for makeExprParser
-- ---------------------------------------------------------------------------

-- | Convert an 'OpTable' to the format expected by 'makeExprParser'.
--
-- Ascending fixity numbers correspond to descending precedence (tighter
-- binding first), which is what 'makeExprParser' expects.
buildExprOpTable :: OpTable -> [[Expr.Operator Parser (Ann PExpr)]]
buildExprOpTable table =
  [ concatMap toMegaparsecOp ops
  | (_, ops) <- IntMap.toAscList table.opsByFixity
  ]
  where
    toMegaparsecOp :: (OpType, Text) -> [Expr.Operator Parser (Ann PExpr)]
    toMegaparsecOp (InfixL, name) = [Expr.InfixL (binOp name <$ opParser name)]
    toMegaparsecOp (InfixR, name) = [Expr.InfixR (binOp name <$ opParser name)]
    toMegaparsecOp (InfixN, name) = [Expr.InfixN (binOp name <$ opParser name)]
    toMegaparsecOp (Prefix, name) = [Expr.Prefix (unOp name <$ opParser name)]
    toMegaparsecOp (Postfix, name) = [Expr.Postfix (unOp name <$ opParser name)]

    binOp op l r = noAnn (Compound op [l, r])
    unOp op x = noAnn (Compound op [x])

    opParser name
      | isSymbolic name = symbolOp name
      | otherwise = wordOp name

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
parseTerms table = parse (sc *> many (withLoc (termP table) <* symbol ".") <* eof)

-- ---------------------------------------------------------------------------
-- Pretty-printing
-- ---------------------------------------------------------------------------

-- | Render a 'PExpr' as valid Prolog source text.
--
-- Uses the operator table to decide which compounds to render as infix,
-- prefix, or postfix operators, with minimal parenthesisation based on
-- precedence.
prettyPExpr :: OpTable -> PExpr -> String
prettyPExpr table = prettyPrec opMap table.wordOpSet maxFixity
  where
    opMap :: Map.Map Text (Int, OpType)
    opMap =
      Map.fromList
        [ (name, (fix, ty))
        | (fix, ops) <- IntMap.toList table.opsByFixity,
          (ty, name) <- ops
        ]
    -- Larger than any valid fixity (1–1199), so nothing is parenthesised
    -- at top level.
    maxFixity = 1200

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
-- So for @yfx@ (InfixL) at fixity F: left gets F, right gets F−1.
-- For @xfy@ (InfixR): left gets F−1, right gets F. Etc.
prettyPrec :: Map.Map Text (Int, OpType) -> Set Text -> Int -> PExpr -> String
prettyPrec _ _ _ (Var v) = T.unpack v
prettyPrec _ _ _ (Int n)
  | n < 0 = "(" ++ show n ++ ")"
  | otherwise = show n
prettyPrec _ _ _ (Atom "[]") = "[]"
prettyPrec _ wops _ (Atom a) = renderAtom wops a
prettyPrec _ _ _ (Str s) = renderString s
prettyPrec _ _ _ Wildcard = "_"
-- List syntax
prettyPrec ops wops _ (Compound "." [h, t]) =
  "[" ++ rec 1200 h.node ++ prettyListTail ops wops t.node ++ "]"
  where
    rec = prettyPrec ops wops
-- Infix operators
prettyPrec ops wops ctx (Compound f [l, r])
  | Just (fix, ty) <- Map.lookup f ops,
    isInfix ty =
      let (lCtx, rCtx) = case ty of
            InfixL -> (fix, fix - 1)
            InfixR -> (fix - 1, fix)
            _ -> (fix - 1, fix - 1)
          rendered =
            rec lCtx l.node
              ++ " "
              ++ T.unpack f
              ++ " "
              ++ rec rCtx r.node
       in if fix > ctx then "(" ++ rendered ++ ")" else rendered
  where
    rec = prettyPrec ops wops
    isInfix InfixL = True
    isInfix InfixR = True
    isInfix InfixN = True
    isInfix _ = False
-- Prefix operators
prettyPrec ops wops ctx (Compound f [x])
  | Just (fix, Prefix) <- Map.lookup f ops =
      let rendered = T.unpack f ++ " " ++ rec (fix - 1) x.node
       in if fix > ctx then "(" ++ rendered ++ ")" else rendered
  where
    rec = prettyPrec ops wops
-- Postfix operators
prettyPrec ops wops ctx (Compound f [x])
  | Just (fix, Postfix) <- Map.lookup f ops =
      let rendered = rec (fix - 1) x.node ++ " " ++ T.unpack f
       in if fix > ctx then "(" ++ rendered ++ ")" else rendered
  where
    rec = prettyPrec ops wops
-- Regular compounds
prettyPrec ops wops _ (Compound f args) =
  renderAtom wops f
    ++ "("
    ++ intercalate ", " [prettyPrec ops wops 1200 a.node | a <- args]
    ++ ")"

prettyListTail :: Map.Map Text (Int, OpType) -> Set Text -> PExpr -> String
prettyListTail _ _ (Atom "[]") = ""
prettyListTail ops wops (Compound "." [h, t]) =
  ", " ++ rec h.node ++ prettyListTail ops wops t.node
  where
    rec = prettyPrec ops wops 1200
prettyListTail ops wops other = " | " ++ prettyPrec ops wops 1200 other

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
