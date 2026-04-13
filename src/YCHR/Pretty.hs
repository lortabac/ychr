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
    renderAtom,
  )
where

import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Loc (Ann (..), noAnn)
import YCHR.PExpr qualified as PE
import YCHR.Parsed qualified as P
import YCHR.Parser (builtinOps)
import YCHR.Types (Constraint (..), Name (..), Term (..))

-- ---------------------------------------------------------------------------
-- Operator table for source pretty-printing
-- ---------------------------------------------------------------------------

-- | Operator table for source pretty-printing.
-- Extends 'builtinOps' with the standard arithmetic\/comparison operators
-- from the builtins library.
prettyOps :: PE.OpTable
prettyOps = case PE.mergeOps builtinOps stdArithOps of
  Right t -> t
  Left _ -> builtinOps
  where
    stdArithOps =
      [ (200, PE.Fy, "-"),
        (500, PE.Yfx, "+"),
        (500, PE.Yfx, "-"),
        (400, PE.Yfx, "*"),
        (400, PE.Yfx, "div"),
        (400, PE.Yfx, "mod"),
        (400, PE.Yfx, "rem"),
        (700, PE.Xfx, "<"),
        (700, PE.Xfx, ">"),
        (700, PE.Xfx, ">="),
        (700, PE.Xfx, "=<"),
        (700, PE.Xfx, "==")
      ]

-- ---------------------------------------------------------------------------
-- AST → PExpr conversion
-- ---------------------------------------------------------------------------

-- | Convert a 'Term' to a 'PE.PExpr'.
-- This is the inverse of 'convertTerm' in "YCHR.Parser".
termToPExpr :: Term -> PE.PExpr
termToPExpr (VarTerm v) = PE.Var v
termToPExpr (IntTerm n) = PE.Int n
termToPExpr (AtomTerm s) = PE.Atom s
termToPExpr (TextTerm s) = PE.Str s
termToPExpr Wildcard = PE.Wildcard
termToPExpr (CompoundTerm (Qualified m f) []) =
  PE.Compound ":" [noAnn (PE.Atom m), noAnn (PE.Atom f)]
termToPExpr (CompoundTerm (Qualified m f) args) =
  PE.Compound ":" [noAnn (PE.Atom m), noAnn (PE.Compound f (map (noAnn . termToPExpr) args))]
termToPExpr (CompoundTerm (Unqualified f) args) =
  PE.Compound f (map (noAnn . termToPExpr) args)

-- | Convert a 'Constraint' to a 'PE.PExpr'.
-- This is the inverse of 'convertConstraint' in "YCHR.Parser".
constraintToPExpr :: Constraint -> PE.PExpr
constraintToPExpr (Constraint (Unqualified name) []) = PE.Atom name
constraintToPExpr (Constraint (Unqualified name) args) =
  PE.Compound name (map (noAnn . termToPExpr) args)
constraintToPExpr (Constraint (Qualified m name) []) =
  PE.Compound ":" [noAnn (PE.Atom m), noAnn (PE.Atom name)]
constraintToPExpr (Constraint (Qualified m name) args) =
  PE.Compound ":" [noAnn (PE.Atom m), noAnn (PE.Compound name (map (noAnn . termToPExpr) args))]

-- | Convert a parsed 'P.Head' to a 'PE.PExpr'.
headToPExpr :: P.Head -> PE.PExpr
headToPExpr (P.Simplification cs) = commaSepPExpr (map constraintToPExpr cs)
headToPExpr (P.Propagation cs) = commaSepPExpr (map constraintToPExpr cs)
headToPExpr (P.Simpagation ks rs) =
  PE.Compound
    "\\"
    [ noAnn (commaSepPExpr (map constraintToPExpr ks)),
      noAnn (commaSepPExpr (map constraintToPExpr rs))
    ]

-- | Convert a parsed 'P.Rule' to a 'PE.PExpr'.
ruleToPExpr :: P.Rule -> PE.PExpr
ruleToPExpr r =
  let headPE = headToPExpr r.head.node
      arrow = case r.head.node of
        P.Propagation {} -> "==>"
        _ -> "<=>"
      bodyPE = commaSepPExpr (map termToPExpr r.body.node)
      guardAndBody = case r.guard.node of
        [] -> bodyPE
        gs -> PE.Compound "|" [noAnn (commaSepPExpr (map termToPExpr gs)), noAnn bodyPE]
      arrowExpr = PE.Compound arrow [noAnn headPE, noAnn guardAndBody]
   in case r.name of
        Nothing -> arrowExpr
        Just ann -> PE.Compound "@" [noAnn (PE.Atom ann.node), noAnn arrowExpr]

-- | Right-fold a list of 'PE.PExpr' into a comma-operator chain.
commaSepPExpr :: [PE.PExpr] -> PE.PExpr
commaSepPExpr [] = PE.Atom "true"
commaSepPExpr [x] = x
commaSepPExpr (x : xs) = PE.Compound "," [noAnn x, noAnn (commaSepPExpr xs)]

-- ---------------------------------------------------------------------------
-- Surface pretty-printers (via PExpr)
-- ---------------------------------------------------------------------------

-- | Render a 'Term' as valid surface-language source text.
-- Unlike 'prettyTerm', variable names are preserved rather than collapsed to @_@.
prettyTermSrc :: Term -> String
prettyTermSrc = PE.prettyPExpr prettyOps . termToPExpr

-- | Render a 'Constraint' as valid surface-language source text.
prettyConstraintSrc :: Constraint -> String
prettyConstraintSrc = PE.prettyPExpr prettyOps . constraintToPExpr

-- | Render a parsed 'P.Head' as valid surface-language source text.
prettyHeadSrc :: P.Head -> String
prettyHeadSrc = PE.prettyPExpr prettyOps . headToPExpr

-- | Render a parsed 'P.Rule' as valid surface-language source text.
prettyRuleSrc :: P.Rule -> String
prettyRuleSrc r = PE.prettyPExpr prettyOps (ruleToPExpr r) ++ "."

-- | Render an atom, quoting with @\'...\'@ if necessary.
renderAtom :: Text -> String
renderAtom = PE.renderAtom prettyOps.wordOpSet

-- ---------------------------------------------------------------------------
-- Runtime pretty-printer (not via PExpr)
-- ---------------------------------------------------------------------------

-- | Render a 'Term' as a Prolog-compatible string.
-- Unbound variables ('VarTerm' and 'Wildcard') are shown as @_@.
prettyTerm :: Term -> String
prettyTerm (IntTerm n) = show n
prettyTerm (AtomTerm s) = T.unpack s
prettyTerm (TextTerm s) = renderStringRT s
prettyTerm (VarTerm _) = "_"
prettyTerm Wildcard = "_"
prettyTerm (CompoundTerm (Unqualified "__closure") (_ : sourceForm : _)) =
  prettyTerm sourceForm
prettyTerm (CompoundTerm (Unqualified "->") [CompoundTerm (Unqualified "fun") params, body]) =
  "fun(" ++ intercalate ", " (map prettyTerm params) ++ ") -> " ++ prettyTerm body
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

-- | Render a string literal with double quotes and escape sequences.
-- Used only by 'prettyTerm' for runtime output.
renderStringRT :: Text -> String
renderStringRT s = "\"" ++ concatMap esc (T.unpack s) ++ "\""
  where
    esc '"' = "\\\""
    esc '\\' = "\\\\"
    esc '\n' = "\\n"
    esc '\t' = "\\t"
    esc c = [c]

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
-- If no user-visible bindings remain, returns an empty string.
-- Otherwise, comma-separated @K = V@ lines terminated with a dot.
prettyQueryResult :: Map Text Term -> String
prettyQueryResult m =
  let visible = [(k, v) | (k, v) <- Map.toAscList m, not ("_" `T.isPrefixOf` k)]
   in case visible of
        [] -> ""
        _ -> formatBindings visible
  where
    formatBindings [] = ""
    formatBindings [(k, v)] = T.unpack k ++ " = " ++ prettyTerm v ++ ".\n"
    formatBindings ((k, v) : rest) =
      T.unpack k ++ " = " ++ prettyTerm v ++ ",\n" ++ formatBindings rest

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
