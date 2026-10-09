{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Internal.Rename.Macro
-- Description : Pure mechanics for macro expansion (@:- macro@).
--
-- This module holds the parts of macro expansion that need no access
-- to the renamer's monad or its global visibility environments: given
-- a macro definition and the arguments of one use, produce the
-- instantiated body; given a term, split it on top-level @,@; given a
-- term in head position, decide whether it is a constraint conjunct or
-- something a head expansion may not contain. The decision of
-- /whether/ a name denotes a macro — which needs the renamer's
-- per-module visibility environments ('YCHR.Internal.Rename.RenameCtx')
-- — lives in "YCHR.Internal.Rename" itself, next to the ordinary
-- constraint\/function visibility logic it mirrors.
--
-- See [the macro reference](../../../../docs/reference/macros.md) for
-- the user-facing specification this module implements.
module YCHR.Internal.Rename.Macro
  ( -- * Import-list permission
    importListPermitsMacro,

    -- * Instantiation
    instantiateMacro,

    -- * Conjunctions
    flattenConj,
    goalsToChain,

    -- * Head-position validity
    HeadConjunctResult (..),
    headConjunct,

    -- * Definition-time checks
    qualifiedRefsIn,
    varsIn,
  )
where

import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import YCHR.Internal.Parsed (Declaration (..), MacroDef (..), MacroExportDeclBody (..))
import YCHR.Internal.Types (Constraint (..), Name (..), Term (..))

-- | Whether a @macro(name\/arity)@ entry in an import list permits
-- importing @(name, arity)@. 'Nothing' (no import list, i.e. plain
-- @use_module(M)@) permits everything; mirrors
-- 'YCHR.Internal.Rename.importListPermits' for the macro namespace.
importListPermitsMacro :: Text -> Int -> Maybe [Declaration] -> Bool
importListPermitsMacro _ _ Nothing = True
importListPermitsMacro n arity (Just decls) = any match decls
  where
    match (MacroExportDecl MacroExportDeclBody {name = dn, arity = da}) =
      dn == n && da == arity
    match _ = False

-- | Instantiate a macro's body at one use: substitute each parameter
-- with the corresponding argument term (verbatim — arguments are
-- never themselves expanded, evaluated, or resolved first), and
-- rename every other variable in the body to a fresh one so it cannot
-- clash with any variable of the use site. 'Wildcard' is left alone
-- (each occurrence already denotes its own fresh anonymous variable).
--
-- Freshness is derived from 'seed', a number distinct for every call
-- within one renaming run (see
-- 'YCHR.Internal.Rename.freshMacroSeed') — not from the use site's
-- 'SourceLoc', which cannot do this job: two sibling goals of one
-- rule body, or two kept conjuncts of one rule head, share a single
-- 'SourceLoc' (and 'YCHR.Internal.Parsed.PExpr' origin) across the
-- whole section, by construction (see 'YCHR.Internal.Parsed.Rule').
-- Two uses of the same macro under the same section — even two plain
-- sibling uses, let alone two uses reached through nested expansion —
-- would then instantiate their non-parameter variables to the
-- identical fresh name and silently alias them. A counter has no such
-- collision.
--
-- Caller's responsibility: 'args' must have the same length as
-- 'def.params' (the caller already knows the arity matched when it
-- decided this was a macro use), and 'seed' must not repeat across
-- the uses expanded within one renaming run.
instantiateMacro :: Int -> MacroDef -> [Term] -> Term
instantiateMacro seed def args = go def.body
  where
    paramMap = zip def.params args
    freshen v = "_macro_" <> seedKey <> "_" <> v
    seedKey = Text.pack (show seed)
    go t = case t of
      VarTerm v -> case lookup v paramMap of
        Just arg -> arg
        Nothing -> VarTerm (freshen v)
      Wildcard -> Wildcard
      IntTerm _ -> t
      FloatTerm _ -> t
      TextTerm _ -> t
      CompoundTerm functor as -> CompoundTerm functor (map go as)

-- | Split a term on the top-level @,@ operator, the same conjunction
-- 'YCHR.Internal.Parser.flattenComma' splits at the surface level,
-- but operating on the already-converted 'Term' representation a
-- macro body (and its instantiation) is held in.
flattenConj :: Term -> [Term]
flattenConj (CompoundTerm (Unqualified ",") [l, r]) = flattenConj l ++ flattenConj r
flattenConj t = [t]

-- | The inverse of 'flattenConj': rebuild a right-associated @,@ chain
-- from a list of goals, so a macro expansion that produced several
-- goals can be spliced back in wherever a single 'Term' is expected
-- (a disjunction branch, or any other position whose own flattening
-- pass will split it again). An empty list — not reachable from a
-- parsed macro body, which is always at least one term — falls back
-- to @true@.
goalsToChain :: [Term] -> Term
goalsToChain [] = CompoundTerm (Unqualified "true") []
goalsToChain [t] = t
goalsToChain (t : ts) = CompoundTerm (Unqualified ",") [t, goalsToChain ts]

-- | The outcome of classifying one goal produced by a head expansion:
-- either a constraint conjunct to splice into the head (kept or
-- removed, per the use site), or a term that cannot appear in a head
-- at all (a bare variable or literal, or one of the structural
-- operators @,@\/@;@\/@\\@\/@|@\/@->@\/@=@\/@is@ — a head is a
-- conjunction of constraints, not an arbitrary goal).
data HeadConjunctResult = HeadConjunctOk Constraint | HeadConjunctInvalid Term

-- | Classify one goal of a (flattened) head expansion. See
-- 'HeadConjunctResult'.
headConjunct :: Term -> HeadConjunctResult
headConjunct (CompoundTerm name args)
  | not (isStructuralName name) = HeadConjunctOk (Constraint name args)
  where
    isStructuralName (Unqualified n) = n `elem` structuralNames
    isStructuralName (Qualified _ _) = False
    structuralNames = [",", ";", "\\", "|", "->", "=", "is"]
headConjunct t = HeadConjunctInvalid t

-- | Every @(name, arity)@ pair referenced in the term as a compound
-- qualified with exactly the given module name, at any depth. Used by
-- the 'YCHR.Internal.Rename.MacroBodyNotExported' check: a macro
-- body's self-qualified references (@M:x@, where @M@ is the macro's
-- own declaring module) must each name something @M@ declares and
-- exports.
qualifiedRefsIn :: Text -> Term -> [(Text, Int)]
qualifiedRefsIn self = go
  where
    go (CompoundTerm (Qualified m n) args)
      | m == self = (n, length args) : concatMap go args
      | otherwise = concatMap go args
    go (CompoundTerm _ args) = concatMap go args
    go _ = []

-- | Every variable name occurring anywhere in a term, for the
-- 'YCHR.Internal.Rename.UnusedMacroParameter' warning: a parameter
-- that never occurs as a 'VarTerm' in the body is unused.
varsIn :: Term -> Set Text
varsIn (VarTerm v) = Set.singleton v
varsIn (CompoundTerm _ args) = Set.unions (map varsIn args)
varsIn _ = Set.empty
