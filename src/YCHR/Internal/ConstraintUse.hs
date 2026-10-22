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
  ( AggregateKind (..),
    ConstraintKey (..),
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

-- | A constraint in a rule head, with the side it is on.
data Occurrence = Occurrence
  { constraint :: HeadConstraint,
    role :: OccurrenceRole
  }

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
            [Occurrence hc KeptOccurrence | hc <- h.kept]
              ++ [Occurrence hc RemovedOccurrence | hc <- h.removed]
              -- A constraint in an aggregate goal is a kept occurrence: an
              -- aggregate keeps its goal's constraints (spec
              -- §Interaction with other features). The exception is a
              -- top-level takemin/takemax, which removes the match it
              -- selects. A nested aggregate's constraints stay kept.
              ++ concat
                [ goalOccurrences topRole agg
                | agg <- h.aggregates,
                  let topRole
                        | removesMatch agg = RemovedOccurrence
                        | otherwise = KeptOccurrence
                ]
       in [ Diagnostic label (AnnP err loc origin) []
          | occ <- occurrences,
            let hc = occ.constraint
                arity = length hc.args,
            Just use <- [Map.lookup (ConstraintKey hc.name arity) prog.constraintUses],
            not (allows use occ.role),
            let err = ConstraintUseViolation hc.name arity use occ.role
          ]

    -- The CHR constraint conjuncts of an aggregate goal, including those
    -- of a nested aggregate. @role@ is the role of a constraint directly
    -- in this goal.
    goalOccurrences role agg = concatMap (conjunctOccurrences role) agg.goal
    conjunctOccurrences role (D.AggConstraint hc _) = [Occurrence hc role]
    conjunctOccurrences _ (D.AggNested nested) =
      goalOccurrences KeptOccurrence nested
    conjunctOccurrences _ (D.AggGuard _) = []

    removesMatch agg = agg.kind == AggTakemin || agg.kind == AggTakemax

-- | Whether a declared policy allows an occurrence in the given position.
allows :: ConstraintUse -> OccurrenceRole -> Bool
allows UseAny _ = True
allows UseFact role = role == KeptOccurrence
allows UseEvent role = role == RemovedOccurrence
allows UseTellOnly _ = False
