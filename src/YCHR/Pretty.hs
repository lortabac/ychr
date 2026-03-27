{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Pretty-printing utilities for CHR terms and binding maps.
module YCHR.Pretty
  ( -- * Pretty class
    Pretty (..),

    -- * Existential wrapper
    PrettyE (..),

    -- * Annotated node
    AnnP (..),
    noAnnP,

    -- * Pretty-printing functions
    prettyTerm,
    prettyBindings,
    prettyQueryResult,
    prettyTermSrc,
    prettyConstraintSrc,
    prettyHeadSrc,
    prettyRuleSrc,
  )
where

import Data.Char (isAlphaNum, isLower)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Parsed qualified as P
import YCHR.Types (Constraint (..), Name (..), Term (..))

-- | Render a 'Term' as a Prolog-compatible string.
-- Unbound variables ('VarTerm' and 'Wildcard') are shown as @_@.
prettyTerm :: Term -> String
prettyTerm (IntTerm n) = show n
prettyTerm (AtomTerm s) = T.unpack s
prettyTerm (TextTerm s) = renderString s
prettyTerm (VarTerm _) = "_"
prettyTerm Wildcard = "_"
prettyTerm (CompoundTerm (Unqualified ".") [h, t]) =
  "[" ++ prettyTerm h ++ prettyListTail t ++ "]"
  where
    prettyListTail (AtomTerm "[]") = ""
    prettyListTail (CompoundTerm (Unqualified ".") [h', t']) =
      ", " ++ prettyTerm h' ++ prettyListTail t'
    prettyListTail other = "|" ++ prettyTerm other
prettyTerm (CompoundTerm (Unqualified f) ts) =
  T.unpack f ++ "(" ++ intercalate ", " (map prettyTerm ts) ++ ")"
prettyTerm (CompoundTerm (Qualified m f) ts) =
  T.unpack m ++ ":" ++ T.unpack f ++ "(" ++ intercalate ", " (map prettyTerm ts) ++ ")"

-- ---------------------------------------------------------------------------
-- Surface pretty-printer (for roundtrip: parse . prettyTermSrc = id)
-- ---------------------------------------------------------------------------

reservedWordsSrc :: [Text]
reservedWordsSrc = ["is", "div", "mod"]

-- | True if the atom string requires single-quote wrapping.
needsQuoting :: Text -> Bool
needsQuoting t = case T.uncons t of
  Nothing -> True
  Just (c, cs) ->
    not
      ( isLower c
          && T.all (\x -> isAlphaNum x || x == '_') cs
          && t `notElem` reservedWordsSrc
      )

-- | Render an atom, quoting with @\'...\'@ if necessary.
-- Embedded single quotes are doubled per ISO Prolog convention.
renderAtom :: Text -> String
renderAtom s
  | needsQuoting s = "'" ++ concatMap esc (T.unpack s) ++ "'"
  | otherwise = T.unpack s
  where
    esc '\'' = "''"
    esc c = [c]

-- | Render a string literal with double quotes and escape sequences.
renderString :: Text -> String
renderString s = "\"" ++ concatMap esc (T.unpack s) ++ "\""
  where
    esc '"' = "\\\""
    esc '\\' = "\\\\"
    esc '\n' = "\\n"
    esc '\t' = "\\t"
    esc c = [c]

infixOpsSrc :: [Text]
infixOpsSrc = ["*", "div", "mod", "+", "-", ":=", "is", "=", "==", "<", ">", "=<", ">="]

-- | Render a 'Term' as valid surface-language source text.
-- Unlike 'prettyTerm', variable names are preserved rather than collapsed to @_@.
prettyTermSrc :: Term -> String
prettyTermSrc (IntTerm n) = show n
prettyTermSrc (AtomTerm s) = renderAtom s
prettyTermSrc (TextTerm s) = renderString s
prettyTermSrc (VarTerm v) = T.unpack v
prettyTermSrc Wildcard = "_"
prettyTermSrc (CompoundTerm (Unqualified ".") [h, t]) =
  "[" ++ prettyTermSrc h ++ prettyListTailSrc t ++ "]"
  where
    prettyListTailSrc (AtomTerm "[]") = ""
    prettyListTailSrc (CompoundTerm (Unqualified ".") [h', t']) =
      ", " ++ prettyTermSrc h' ++ prettyListTailSrc t'
    prettyListTailSrc other = "|" ++ prettyTermSrc other
prettyTermSrc (CompoundTerm (Unqualified op) [l, r])
  | op `elem` infixOpsSrc =
      "(" ++ prettyTermSrc l ++ " " ++ T.unpack op ++ " " ++ prettyTermSrc r ++ ")"
prettyTermSrc (CompoundTerm (Unqualified f) ts) =
  renderAtom f ++ "(" ++ intercalate ", " (map prettyTermSrc ts) ++ ")"
prettyTermSrc (CompoundTerm (Qualified m f) ts) =
  renderAtom m
    ++ ":"
    ++ renderAtom f
    ++ "("
    ++ intercalate ", " (map prettyTermSrc ts)
    ++ ")"

-- | Render a 'Constraint' as valid surface-language source text.
prettyConstraintSrc :: Constraint -> String
prettyConstraintSrc (Constraint (Unqualified name) []) = renderAtom name
prettyConstraintSrc (Constraint (Unqualified name) args) =
  renderAtom name ++ "(" ++ intercalate ", " (map prettyTermSrc args) ++ ")"
prettyConstraintSrc (Constraint (Qualified m name) args) =
  renderAtom m
    ++ ":"
    ++ renderAtom name
    ++ case args of
      [] -> ""
      _ -> "(" ++ intercalate ", " (map prettyTermSrc args) ++ ")"

-- ---------------------------------------------------------------------------
-- User-facing output (binding map)
-- ---------------------------------------------------------------------------

-- | Serialize a variable binding map to the golden file format.
--
-- Keys are sorted alphabetically for determinism. Each line has the form
-- @K = V@ followed by a newline, matching the output of 'unlines'.
prettyBindings :: Map Text Term -> String
prettyBindings m =
  unlines [T.unpack k ++ " = " ++ prettyTerm v | (k, v) <- Map.toAscList m]

-- | Render a variable binding map as a Prolog-style query result.
--
-- Variables starting with @_@ are filtered out (internal/wildcard).
-- If no user-visible bindings remain, returns @true.@.
-- Otherwise, comma-separated @K = V@ lines terminated with a dot.
prettyQueryResult :: Map Text Term -> String
prettyQueryResult m =
  let visible = [(k, v) | (k, v) <- Map.toAscList m, not ("_" `T.isPrefixOf` k)]
   in case visible of
        [] -> "true.\n"
        _ -> formatBindings visible
  where
    formatBindings [] = ""
    formatBindings [(k, v)] = T.unpack k ++ " = " ++ prettyTerm v ++ ".\n"
    formatBindings ((k, v) : rest) =
      T.unpack k ++ " = " ++ prettyTerm v ++ ",\n" ++ formatBindings rest

-- ---------------------------------------------------------------------------
-- Parsed AST pretty-printers
-- ---------------------------------------------------------------------------

-- | Render a parsed 'P.Head' as valid surface-language source text.
--
-- Only the constraint list(s) are rendered, not the arrow.
prettyHeadSrc :: P.Head -> String
prettyHeadSrc (P.Simplification cs) = constraintList cs
prettyHeadSrc (P.Propagation cs) = constraintList cs
prettyHeadSrc (P.Simpagation ks rs) = constraintList ks ++ " \\ " ++ constraintList rs

constraintList :: [Constraint] -> String
constraintList = intercalate ", " . map prettyConstraintSrc

-- | Render a parsed 'P.Rule' as valid surface-language source text.
prettyRuleSrc :: P.Rule -> String
prettyRuleSrc r =
  namePrefix ++ prettyHeadSrc (r.head.node) ++ " " ++ arrow ++ " " ++ guardPrefix ++ bodyStr ++ "."
  where
    namePrefix = case r.name of
      Nothing -> ""
      Just ann -> renderAtom ann.node ++ " @ "
    arrow = case r.head.node of
      P.Propagation {} -> "==>"
      _ -> "<=>"
    guardPrefix = case r.guard.node of
      [] -> ""
      gs -> intercalate ", " (map prettyTermSrc gs) ++ " | "
    bodyStr = intercalate ", " (map prettyTermSrc r.body.node)

-- ---------------------------------------------------------------------------
-- Pretty class
-- ---------------------------------------------------------------------------

class Pretty a where
  prettySrc :: a -> String

instance Pretty Term where prettySrc = prettyTermSrc

instance Pretty [Term] where
  prettySrc ts = intercalate ", " (map prettyTermSrc ts)

instance Pretty Constraint where prettySrc = prettyConstraintSrc

instance Pretty P.Head where prettySrc = prettyHeadSrc

instance Pretty P.Rule where prettySrc = prettyRuleSrc

-- ---------------------------------------------------------------------------
-- Existential wrapper and annotated node
-- ---------------------------------------------------------------------------

-- | An existential wrapper for any value that can be pretty-printed.
data PrettyE = forall a. (Pretty a) => PrettyE a

instance Show PrettyE where
  show (PrettyE a) = prettySrc a

-- | A desugared node annotated with a source location and the original
-- parsed AST node that produced it.
data AnnP a = AnnP
  { node :: a,
    sourceLoc :: P.SourceLoc,
    parsed :: PrettyE
  }
  deriving (Show)

-- | Wrap a node with a dummy source location and a dummy pretty-printed origin.
-- Useful for constructing values in tests where provenance is irrelevant.
noAnnP :: (Pretty b) => b -> a -> AnnP a
noAnnP origin x = AnnP x P.dummyLoc (PrettyE origin)
