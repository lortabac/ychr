{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Internal.Compile.Passive
-- Description : Marks occurrences that can never fire as passive.
--
-- The /passive occurrences/ optimization (paper §5.3). An occurrence is
-- *passive* if it can be derived statically that the rule can never fire
-- with the active constraint matching that occurrence. A passive
-- occurrence contributes no @occurrence_c_j@ procedure and no call from
-- @activate_c@, so its (always-empty) partner search is never emitted.
--
-- This module is a pure post-pass over the fully-numbered 'OccurrenceMap'
-- (see 'YCHR.Internal.Compile.Occurrences'): it only flips the 'passive' flag,
-- never reorders or renumbers, so the ωr occurrence numbers of the
-- surviving occurrences are unchanged.
--
-- v1 detects the /subsumption \/ symmetry/ source: the kept occurrence of
-- an idempotence simpagation @c(..) \\ c(..) \<=\> ..@, and the ωr-later
-- occurrence of a symmetric two-head simplification @c(X,Y), c(Y,X) \<=\>
-- ..@. The paper's /never-stored/ source is deferred: without Late
-- Storage its only sound criterion (a constraint all of whose head
-- occurrences are single-headed guardless simplifications) is vacuous for
-- partner elimination — such a constraint can never be a partner, because
-- being a partner requires appearing in a multi-headed rule. See
-- @docs/reference/passive-occurrences.md@ for the full specification and
-- soundness argument.
--
-- The analysis is conservative: it marks an occurrence passive only when
-- soundness is guaranteed. Every predicate below is a /sufficient/, not
-- necessary, condition — correctness over completeness.
module YCHR.Internal.Compile.Passive
  ( markPassive,
  )
where

import Data.List (nub)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Compile.Types
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Parsed (AnnP (..))
import YCHR.Types (HeadArg (..), HeadConstraint)

-- | Flip the 'passive' flag on every occurrence the analysis can prove
-- can never fire. Runs after occurrence numbering, so numbers are
-- preserved and only the 'passive' field changes.
markPassive :: OccurrenceMap -> OccurrenceMap
markPassive = occMapMap (map mark)
  where
    mark occ = occ {passive = occ.passive || isPassive occ}

-- | Is this occurrence passive under any v1 source?
isPassive :: Occurrence -> Bool
isPassive occ = idempotencePassive occ || symmetryPassive occ

-- ---------------------------------------------------------------------------
-- Subsumption / symmetry analysis
-- ---------------------------------------------------------------------------

-- | The kept occurrence of an idempotence simpagation is subsumed by the
-- removed one and made passive. The rule must have exactly one kept and
-- one removed head of the same constraint type, structurally identical
-- after HNF canonicalization, with no residual guards. The occurrence is
-- passive only when it is the /kept/ one (the removed one stays active
-- and, being tried first by ωr, always fires before the kept one could).
idempotencePassive :: Occurrence -> Bool
idempotencePassive occ =
  case (hd.kept, hd.removed) of
    ([k], [r]) ->
      occ.isKept
        && sameType k r
        && allGuardsHeadEq headVars guards
        && canonArgs classes "k" k.args == canonArgs classes "r" r.args
      where
        headVars = headVarsOf (hd.kept ++ hd.removed)
        classes = buildClasses headVars guards
    _ -> False
  where
    hd = ruleHead occ.rule
    guards = ruleGuards occ.rule

-- | One occurrence of a symmetric two-head simplification is redundant.
-- The rule must have no kept heads and exactly two removed heads of the
-- same constraint type, related by swapping their argument positions,
-- with no residual guards. The ωr-later occurrence (the one not tried
-- first) is made passive.
symmetryPassive :: Occurrence -> Bool
symmetryPassive occ =
  case (hd.kept, hd.removed) of
    ([], [h0, h1]) ->
      isLaterOccurrence occ
        && sameType h0 h1
        && allGuardsHeadEq headVars guards
        && isSymmetric classes h0 h1
      where
        headVars = headVarsOf hd.removed
        classes = buildClasses headVars guards
    _ -> False
  where
    hd = ruleHead occ.rule
    guards = ruleGuards occ.rule

-- | Among the two occurrences of a symmetric two-head rule, the passive
-- one is the ωr-later of the two. Occurrence positions in the combined
-- (removed-first, right-to-left) head list run @0@ (tried first) and @1@
-- (tried later); the later one is passive.
isLaterOccurrence :: Occurrence -> Bool
isLaterOccurrence occ = occ.activeIdx == HeadPosition 1

-- | Whether the two heads describe the same unordered match: there is a
-- bijection on argument class-tokens mapping @h0@ to @h1@ and @h1@ to
-- @h0@. Built from the pairing @zip (a0 ++ a1) (a1 ++ a0)@; the mapping
-- must be a consistent function whose image has no duplicates (injective,
-- hence a bijection / involution).
isSymmetric :: ClassMap -> HeadConstraint -> HeadConstraint -> Bool
isSymmetric classes h0 h1 =
  case build Map.empty (zip (a0 ++ a1) (a1 ++ a0)) of
    Just m -> let vals = Map.elems m in length vals == length (nub vals)
    Nothing -> False
  where
    a0 = canonArgs classes "0" h0.args
    a1 = canonArgs classes "1" h1.args
    build m [] = Just m
    build m ((x, y) : rest) = case Map.lookup x m of
      Just y' | y' /= y -> Nothing
      _ -> build (Map.insert x y m) rest

-- ---------------------------------------------------------------------------
-- Head canonicalization (seeing through HNF)
-- ---------------------------------------------------------------------------

-- | A flat union-find over head variables: every key maps directly to
-- its class representative.
type ClassMap = Map Text Text

-- | The set of head-variable names in a list of head constraints.
-- Wildcards contribute no name.
headVarsOf :: [HeadConstraint] -> Set Text
headVarsOf hcs = Set.fromList [v | hc <- hcs, HeadVar v <- hc.args]

-- | Build head-variable equivalence classes from the head-variable
-- equality guards induced by HNF (e.g. @X = _hnf_0@). Only guards
-- equating two head variables union classes; all others are ignored here
-- (they are rejected separately by 'allGuardsHeadEq').
buildClasses :: Set Text -> [D.Guard] -> ClassMap
buildClasses headVars guards = foldl' union (Map.fromSet id headVars) headEqns
  where
    headEqns =
      [ (a, b)
      | D.GuardEqual (D.VarExpr a) (D.VarExpr b) <- guards,
        a `Set.member` headVars,
        b `Set.member` headVars
      ]
    union m (a, b) =
      case (Map.lookup a m, Map.lookup b m) of
        (Just ra, Just rb)
          | ra == rb -> m
          | otherwise -> Map.map (\r -> if r == rb then ra else r) m
        _ -> m

-- | The class-token list of a head's arguments: each variable maps to
-- its class representative, each wildcard to a fresh token unique to this
-- head (the @prefix@ plus its position), so wildcards never unify with
-- anything — conservatively defeating passivity when they appear.
canonArgs :: ClassMap -> Text -> [HeadArg] -> [Text]
canonArgs classes prefix args =
  [ case a of
      HeadVar v -> Map.findWithDefault v v classes
      HeadWildcard -> "_wc:" <> prefix <> ":" <> T.pack (show i)
  | (i, a) <- zip [0 :: Int ..] args
  ]

-- | Every guard is a head-variable equality (so there are no residual
-- guards). This is the v1 conservative form of "residual guards are
-- symmetric": it rejects rules like @c(X,Y), c(Y,X) \<=\> X \< Y | ..@
-- whose @X \< Y@ guard is not a head-variable equality.
allGuardsHeadEq :: Set Text -> [D.Guard] -> Bool
allGuardsHeadEq headVars = all isHeadEq
  where
    isHeadEq (D.GuardEqual (D.VarExpr a) (D.VarExpr b)) =
      a `Set.member` headVars && b `Set.member` headVars
    isHeadEq _ = False

-- ---------------------------------------------------------------------------
-- Rule accessors and helpers
-- ---------------------------------------------------------------------------

-- | A rule's post-HNF head. Pattern-matched out of the 'AnnP' wrapper
-- (the codebase reads 'AnnP' fields this way rather than via record dot).
ruleHead :: D.Rule -> D.Head
ruleHead rule = let AnnP {node = hd} = rule.head in hd

-- | A rule's post-HNF guard list.
ruleGuards :: D.Rule -> [D.Guard]
ruleGuards rule = let AnnP {node = gs} = rule.guard in gs

-- | Whether two head constraints have the same constraint type (functor
-- and arity).
sameType :: HeadConstraint -> HeadConstraint -> Bool
sameType a b = a.name == b.name && length a.args == length b.args
