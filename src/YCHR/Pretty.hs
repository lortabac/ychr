{-# LANGUAGE OverloadedStrings #-}

-- | Pretty-printing utilities for CHR terms and binding maps.
module YCHR.Pretty
  ( -- * Pretty-printing functions
    prettyTerm,
    prettyBindings,
    prettyQueryResult,
    prettyTermSrc,
    prettyConstraintSrc,
    prettyHeadSrc,
    prettyRuleSrc,
    prettyPExprSrc,
    renderAtom,
  )
where

import Data.Char (isUpper)
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
termToPExpr (FloatTerm n) = PE.Float n
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
-- Runtime pretty-printer (via PExpr)
-- ---------------------------------------------------------------------------

-- | Render a 'Term' as a Prolog-compatible string.
-- Unbound variables ('VarTerm' and 'Wildcard') are shown as @_@.
-- Operators are displayed using their declared fixity and precedence.
prettyTerm :: Term -> String
prettyTerm = PE.prettyPExpr prettyOps . runtimeToPExpr

-- | Convert a runtime 'Term' to a 'PE.PExpr' for pretty-printing.
-- Like 'termToPExpr' but collapses unbound variables to @_@ and
-- unwraps closure terms to show their source form.
runtimeToPExpr :: Term -> PE.PExpr
runtimeToPExpr (VarTerm _) = PE.Wildcard
runtimeToPExpr Wildcard = PE.Wildcard
runtimeToPExpr (CompoundTerm (Unqualified "__closure") (_ : sourceForm : _)) =
  unquoteToPExpr sourceForm
runtimeToPExpr (CompoundTerm (Qualified m f) []) =
  PE.Compound ":" [noAnn (PE.Atom m), noAnn (PE.Atom f)]
runtimeToPExpr (CompoundTerm (Qualified m f) args) =
  PE.Compound ":" [noAnn (PE.Atom m), noAnn (PE.Compound f (map (noAnn . runtimeToPExpr) args))]
runtimeToPExpr (CompoundTerm (Unqualified f) args) =
  PE.Compound f (map (noAnn . runtimeToPExpr) args)
runtimeToPExpr (IntTerm n) = PE.Int n
runtimeToPExpr (FloatTerm n) = PE.Float n
runtimeToPExpr (AtomTerm s) = PE.Atom s
runtimeToPExpr (TextTerm s) = PE.Str s

-- | Like 'runtimeToPExpr' but reverses the 'quoteTerm' transformation:
-- atoms that look like variable names (start with uppercase or @_@) are
-- rendered as variables. Used for closure source forms where 'quoteTerm'
-- has turned @VarTerm v@ into @AtomTerm v@.
unquoteToPExpr :: Term -> PE.PExpr
unquoteToPExpr (AtomTerm s)
  | Just (c, _) <- T.uncons s, isUpper c || c == '_' = PE.Var s
unquoteToPExpr (CompoundTerm (Unqualified f) args) =
  PE.Compound f (map (noAnn . unquoteToPExpr) args)
unquoteToPExpr (CompoundTerm (Qualified m f) []) =
  PE.Compound ":" [noAnn (PE.Atom m), noAnn (PE.Atom f)]
unquoteToPExpr (CompoundTerm (Qualified m f) args) =
  PE.Compound ":" [noAnn (PE.Atom m), noAnn (PE.Compound f (map (noAnn . unquoteToPExpr) args))]
unquoteToPExpr t = runtimeToPExpr t

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

-- | Render a 'PExpr' as valid surface-language source text.
prettyPExprSrc :: PE.PExpr -> String
prettyPExprSrc = PE.prettyPExpr prettyOps
