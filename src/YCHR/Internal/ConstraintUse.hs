{-# LANGUAGE OverloadedStrings #-}

-- | Constraint-use checking: every rule-head occurrence of a constraint
-- must sit in a position its @:- constraint_use@ declaration allows.
--
-- An occurrence is /kept/ if the rule leaves it in the store and
-- /removed/ if the rule consumes it ('D.Head'\'s two lists). The four
-- declared policies allow:
--
--   * @any@ (the default, absent from 'D.Program.constraintUses'):
--     either position;
--   * @fact@: kept only;
--   * @event@: removed only;
--   * @tell_only@: neither — the constraint may be told, but never
--     written in a rule head.
--
-- The check is deliberately narrow and purely structural: it walks rule
-- heads only (never guards or bodies; an aggregate goal is part of the
-- head), over every rule of the flattened program, and does not ask
-- whether an occurrence can fire.
--
-- Like "YCHR.Internal.Exhaustiveness", this is an independent pass with
-- its own error type and no dependency on the CHR-encoded type checker.
-- Unlike it, the pass is not run by "YCHR.Internal.Compile.Pipeline":
-- its callers invoke it next to 'YCHR.Internal.TypeCheck.typeCheckProgram',
-- so the CLI's @--no-check@ disables it along with the rest of type
-- checking. See docs/reference/type-system.md §Constraint-use checking.
module YCHR.Internal.ConstraintUse
  ( ConstraintUseError (..),
    OccurrenceRole (..),
    checkConstraintUse,
  )
where

import Data.Map.Strict qualified as Map
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Diagnostic (Diagnostic (..))
import YCHR.Internal.Parsed (AnnP (..))
import YCHR.Internal.Types
  ( ConstraintKey (..),
    ConstraintUse (..),
    HeadConstraint (..),
    QualifiedName,
  )
-- Hidden so '.head' resolves under MicroHs (dev-docs/MICROHS_GAPS.md, gap 1).
import Prelude hiding (head)

-- | Which side of a rule head an occurrence is on.
data OccurrenceRole = KeptOccurrence | RemovedOccurrence
  deriving (Eq, Show)

-- | A rule-head occurrence in a position its constraint's declared
-- policy forbids. Carries the constraint's name and arity, its declared
-- policy, and the position the occurrence is in.
data ConstraintUseError
  = ConstraintUseViolation QualifiedName Int ConstraintUse OccurrenceRole
  deriving (Eq, Show)

-- | Check every rule head of the program. One diagnostic per offending
-- occurrence, anchored at its rule's head.
checkConstraintUse :: D.Program -> [Diagnostic ConstraintUseError]
checkConstraintUse prog
  | Map.null prog.constraintUses = []
  | otherwise = concatMap checkRule prog.rules
  where
    checkRule r =
      let AnnP h loc origin = r.head
          label = fmap ("rule " <>) r.name
          occurrences =
            [(hc, KeptOccurrence) | hc <- h.kept]
              ++ [(hc, RemovedOccurrence) | hc <- h.removed]
              -- A constraint in an aggregate goal is a kept occurrence: an
              -- aggregate keeps its goal's constraints (spec
              -- §Interaction with other features). The removal a
              -- takemin/takemax performs is not reachable yet, since
              -- selection aggregates are still rejected by the compiler.
              ++ [ (hc, KeptOccurrence)
                 | agg <- h.aggregates,
                   hc <- goalConstraints agg
                 ]
       in [ Diagnostic label (AnnP err loc origin) []
          | (hc, role) <- occurrences,
            let arity = length hc.args,
            Just use <- [Map.lookup (ConstraintKey hc.name arity) prog.constraintUses],
            not (allows use role),
            let err = ConstraintUseViolation hc.name arity use role
          ]

    -- The CHR constraint conjuncts of an aggregate goal, including those
    -- of a nested aggregate.
    goalConstraints agg = concatMap conjunctConstraints agg.goal
    conjunctConstraints (D.AggConstraint hc _) = [hc]
    conjunctConstraints (D.AggNested nested) = goalConstraints nested
    conjunctConstraints (D.AggGuard _) = []

-- | Whether a declared policy allows an occurrence in the given position.
allows :: ConstraintUse -> OccurrenceRole -> Bool
allows UseAny _ = True
allows UseFact role = role == KeptOccurrence
allows UseEvent role = role == RemovedOccurrence
allows UseTellOnly _ = False
