{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Internal.Compile.Occurrences
-- Description : Pre-pass that collects and numbers head occurrences.
--
-- This module owns the first phase of the CHR-to-VM compiler: walking
-- every rule head and producing, for each constraint type, a top-down
-- list of 'Occurrence' records numbered as required by the refined
-- operational semantics ωr (paper §2.2, Fig. 2). The result is a single
-- 'OccurrenceMap' that the rest of 'YCHR.Internal.Compile' consumes.
--
-- See Note [Occurrence numbering order] and Note [Anonymous rule names]
-- at the bottom of this file for the ordering and numbering choices.
module YCHR.Internal.Compile.Occurrences
  ( collectOccurrences,
  )
where

import Control.Monad.Trans.Writer.CPS (Writer, tell)
-- 'foldl'' is imported qualified because the Prelude only re-exports it from
-- base 4.20 (GHC 9.10) and this package supports GHC 9.6+. An unqualified
-- 'import Data.List (foldl'')' would be flagged redundant on newer compilers,
-- since this module needs nothing else from "Data.List".
import Data.List qualified as List
import Data.Maybe (catMaybes)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Traversable (for)
import YCHR.Internal.Compile.Aggregate
  ( aggregateResultTypeDeclared,
    collectAggregatePlans,
  )
import YCHR.Internal.Compile.Passive (markPassive)
import YCHR.Internal.Compile.Types
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Diagnostic (Diagnostic (..))
import YCHR.Internal.PExpr (PExpr)
import YCHR.Internal.Parsed (AnnP (..))
import YCHR.Internal.Parsed qualified as P
import YCHR.Internal.Types
  ( AggregateKind (..),
    HeadConstraint,
    Identifier (..),
    RuleId (..),
    SymbolTable,
    lookupSymbol,
    qualifiedToName,
  )
import YCHR.Internal.VM (ConstraintType (..))
-- Hidden so '.head' resolves under MicroHs (dev-docs/MICROHS_GAPS.md, gap 1).
import Prelude hiding (head)

-- | Walk every rule in the program and assemble the per-constraint
-- 'OccurrenceMap'. Occurrences are numbered top-down within each
-- constraint type so that occurrence number 1 is the textually first
-- occurrence (paper §5.2, Listings 1 and 2).
--
-- The result also carries the per-rule display names, indexed by the
-- rule's 'RuleId' (which mirrors its program-wide source index).
--
-- See Note [Occurrence numbering order].
collectOccurrences ::
  SymbolTable ->
  D.Program ->
  Writer [Diagnostic CompileError] CollectedOccurrences
collectOccurrences symTab prog = do
  let indexed = zip [0 ..] prog.rules
      displayNames = map (uncurry ruleDisplayName) indexed
  checkAggregateResultType prog
  -- Each rule's aggregates are planned once, here, and carried by every
  -- occurrence of that rule and by the program's procedure list.
  aggregatePlans <- traverse (uncurry collectAggregatePlans) indexed
  allOccs <-
    fmap concat (traverse (uncurry (ruleOccurrences symTab aggregatePlans)) indexed)
  let grouped =
        List.foldl'
          ( \m occ ->
              occMapAppend (Identifier occ.conName (occurrenceArity occ)) occ m
          )
          occMapEmpty
          allOccs
  -- Number occurrences first (so ωr numbers are stable), then mark the
  -- provably-passive ones. Passivity only flips a flag; it never renumbers.
  let numbered = occMapMap (assignNumbers . reverse) grouped
  pure
    CollectedOccurrences
      { occurrenceMap = markPassive numbered,
        ruleDisplayNames = displayNames,
        aggregatePlans = aggregatePlans
      }
  where
    -- Reverse before numbering to undo the prepend-on-insert in
    -- 'occMapAppend' and restore top-down rule order.
    assignNumbers = zipWith (\n o -> o {number = n}) [OccurrenceNumber 1 ..]

-- | A program that uses an aggregate has to declare the @maybe@ its
-- aggregators produce: the constructor an aggregate's @Final@ closure
-- returns, and the one the compiler decodes. Reported once per program, at
-- the first rule that has an aggregate, and never for a program that uses
-- none. A selection form has no aggregator, so it does not count.
checkAggregateResultType :: D.Program -> Writer [Diagnostic CompileError] ()
checkAggregateResultType prog =
  case [ rule
       | rule <- prog.rules,
         any (\a -> a.kind == AggPlain) rule.head.node.aggregates
       ] of
    [] -> pure ()
    rule : _ ->
      if aggregateResultTypeDeclared prog.typeDefinitions
        then pure ()
        else
          tell
            [ Diagnostic
                (fmap ("rule " <>) rule.name)
                (AnnP AggregateResultNotMaybe rule.head.sourceLoc rule.head.parsed)
                []
            ]

-- | Compute the display name of a rule. Anonymous rules get a
-- synthetic @__rule_N@ name whose index matches the rule's
-- program-wide source position. The double-underscore prefix avoids
-- clashes with user-defined names.
-- See Note [Anonymous rule names].
ruleDisplayName :: Int -> D.Rule -> Text
ruleDisplayName ruleIdx rule = case rule.name of
  Just n -> n
  Nothing -> "__rule_" <> T.pack (show ruleIdx)

-- | Produce one 'Occurrence' record for every head constraint of a
-- single rule, plus one for every CHR constraint conjunct of one of its
-- aggregate goals.
--
-- The ordinary occurrences come first, so within a rule a goal
-- occurrence follows that rule's ordinary occurrences of the same type
-- in the numbered occurrence list (spec §2 "Order"). The other heads
-- become the partner list of each occurrence; a goal occurrence's
-- partners are /all/ the regular heads, since its active constraint is
-- not a head.
--
-- The rule's aggregates are planned by the caller and shared by all of its
-- occurrences, so an occurrence can compute them without re-planning. An
-- aggregate the planner dropped (one with a nested take form)
-- contributes no goal occurrence: there is no plan to compute it with. A
-- selection form is planned like any other aggregate, so its conjuncts
-- are goal occurrences too.
ruleOccurrences ::
  SymbolTable ->
  [[AggregatePlan]] ->
  Int ->
  D.Rule ->
  Writer [Diagnostic CompileError] [Occurrence]
ruleOccurrences symTab aggregatePlans ruleIdx rule = do
  let AnnP {node = ruleHead} = rule.head
      kept = ruleHead.kept
      removed = ruleHead.removed
      ctx =
        RuleCtx
          { symTab = symTab,
            rule = rule,
            ruleId = RuleId ruleIdx,
            display = ruleDisplayName ruleIdx rule,
            -- Indexed by the rule's program-wide position, which is its
            -- 'RuleId'. The list is built from the same rule order, so the
            -- index is in range by construction.
            aggregates = aggregatePlans !! ruleIdx,
            -- Occurrences are ordered removed-first, right-to-left within
            -- each group, following the ωr refined operational semantics
            -- (paper §2.2, Fig. 2). Removed occurrences are tried before
            -- kept ones, and within each group the rightmost head
            -- constraint gets the lowest (earliest) occurrence number.
            heads =
              zipWith
                (\i c -> HeadEntry i c False)
                [HeadPosition 0 ..]
                (reverse removed)
                ++ zipWith
                  (\i c -> HeadEntry i c True)
                  [HeadPosition (length removed) ..]
                  (reverse kept)
          }
  ordinary <- catMaybes <$> traverse (mkOccurrence ctx) ctx.heads
  -- One goal occurrence per CHR constraint conjunct of a planned
  -- aggregate's goal, nested goals included. The plan is matched by its
  -- source index, since the planner drops unsupported forms and leaves
  -- gaps in the list.
  goalOccurrences <-
    fmap catMaybes . sequence $
      [ mkGoalOccurrence
          ctx
          hc
          GoalOccurrence
            { aggregateIndex = plan.position,
              activeIndex = j,
              conjuncts = level.conjuncts,
              enclosing = level.enclosing,
              levelShared = level.levelShared
            }
      | (i, _) <- zip [0 :: Int ..] rule.head.node.aggregates,
        Just plan <- [List.find (\p -> p.position == i) ctx.aggregates],
        level <- aggregateGoals [] [] plan,
        (j, D.AggConstraint hc _) <- zip [0 :: Int ..] level.conjuncts
      ]
  pure (ordinary ++ goalOccurrences)

-- | What every occurrence of one rule shares.
data RuleCtx = RuleCtx
  { symTab :: SymbolTable,
    rule :: D.Rule,
    ruleId :: RuleId,
    display :: Text,
    -- | The rule's aggregate plans.
    aggregates :: [AggregatePlan],
    -- | The rule's heads, in occurrence order.
    heads :: [HeadEntry]
  }

-- | One regular head of a rule: a 'Partner' before its constraint type is
-- looked up.
data HeadEntry = HeadEntry
  { -- | Position in the rule's combined (removed ++ kept) head list.
    idx :: HeadPosition,
    constraint :: HeadConstraint,
    isKept :: Bool
  }

-- | One goal of an aggregate, with what surrounds it. The fields are the
-- 'GoalOccurrence' fields of the same name.
data GoalLevel = GoalLevel
  { conjuncts :: [D.AggregateConjunct],
    enclosing :: [[D.AggregateConjunct]],
    levelShared :: [[Text]]
  }

-- | Every goal of an aggregate, with the goals enclosing it innermost first
-- and, for each of those, the shared inputs of the nested aggregate whose
-- goal sits inside it: the aggregate's own goal, then the goals nested in
-- it, in source order and depth first (spec §2 "Order").
aggregateGoals ::
  [[D.AggregateConjunct]] ->
  [[Text]] ->
  AggregatePlan ->
  [GoalLevel]
aggregateGoals enclosing shared plan =
  GoalLevel {conjuncts = plan.goal, enclosing = enclosing, levelShared = shared}
    : concat
      [ aggregateGoals (plan.goal : enclosing) (n.shared : shared) n
      | n <- plan.nested
      ]

-- | Build a single 'Occurrence' record for one head of the rule, as the
-- active constraint. The other heads become the partner list.
--
-- Returns 'Nothing' when a partner's constraint type is not in the
-- symbol table: 'lookupCType' has already reported the miss, and an
-- occurrence with an unresolvable partner cannot be compiled.
mkOccurrence ::
  RuleCtx ->
  HeadEntry ->
  Writer [Diagnostic CompileError] (Maybe Occurrence)
mkOccurrence ctx active = do
  partners <- resolvePartners ctx [h | h <- ctx.heads, h.idx /= active.idx]
  pure $ do
    resolvedPartners <- sequence partners
    pure
      Occurrence
        { conName = qualifiedToName active.constraint.name,
          number = OccurrenceNumber 0,
          rule = ctx.rule,
          ruleId = ctx.ruleId,
          ruleDisplay = ctx.display,
          activeIdx = active.idx,
          isKept = active.isKept,
          activeArgs = active.constraint.args,
          partners = resolvedPartners,
          aggregates = ctx.aggregates,
          passive = False,
          goalOcc = Nothing
        }

-- | Build the 'Occurrence' for one CHR constraint conjunct of an
-- aggregate goal. Every regular head is a partner, since the active
-- constraint is not a head. The 'GoalOccurrence' says where the conjunct
-- sits: its position in its goal, which the location phase needs to
-- evaluate the conjunct's own guards in their goal-order place, and the
-- goals around it.
mkGoalOccurrence ::
  RuleCtx ->
  HeadConstraint ->
  GoalOccurrence ->
  Writer [Diagnostic CompileError] (Maybe Occurrence)
mkGoalOccurrence ctx activeCon goal = do
  partners <- resolvePartners ctx ctx.heads
  pure $ do
    resolvedPartners <- sequence partners
    pure
      Occurrence
        { conName = qualifiedToName activeCon.name,
          number = OccurrenceNumber 0,
          rule = ctx.rule,
          ruleId = ctx.ruleId,
          ruleDisplay = ctx.display,
          -- Meaningless for a goal occurrence: the active constraint
          -- is not a head. See 'YCHR.Internal.Compile.Types.activeHeadPosition'.
          activeIdx = HeadPosition 0,
          -- Firing never removes the active goal constraint as a head.
          -- A take form may still remove it as its selected match:
          -- 'YCHR.Internal.Compile.genSelectStmts' finds the match again
          -- and 'YCHR.Internal.Compile.genKillStmts' kills it.
          isKept = True,
          activeArgs = activeCon.args,
          partners = resolvedPartners,
          aggregates = ctx.aggregates,
          passive = False,
          goalOcc = Just goal
        }

-- | Resolve every head's constraint type, reporting a miss and
-- returning 'Nothing' for that entry so the caller can drop the whole
-- occurrence.
resolvePartners ::
  RuleCtx ->
  [HeadEntry] ->
  Writer [Diagnostic CompileError] [Maybe Partner]
resolvePartners ctx entries = do
  let headLoc = ctx.rule.head.sourceLoc
      headPretty = ctx.rule.head.parsed
      ruleLabel = Just ("rule " <> ctx.display)
  for entries $ \entry -> do
    let con = entry.constraint
    ct <-
      lookupCType
        ctx.symTab
        headLoc
        headPretty
        ruleLabel
        (Identifier (qualifiedToName con.name) (length con.args))
    pure $ do
      cType <- ct
      pure
        Partner
          { idx = entry.idx,
            constraint = con,
            isKept = entry.isKept,
            cType = cType
          }

-- | Look up a constraint type in the symbol table, reporting an error
-- and returning 'Nothing' on a miss. The caller drops the occurrence
-- so that the rest of the pass can keep going and collect more
-- diagnostics; 'YCHR.Internal.Compile.compile' aborts as soon as any
-- diagnostic was emitted, so nothing downstream ever observes the
-- shortened occurrence list.
lookupCType ::
  SymbolTable ->
  P.SourceLoc ->
  PExpr ->
  Maybe Text ->
  Identifier ->
  Writer [Diagnostic CompileError] (Maybe ConstraintType)
lookupCType symTab loc p label ident = case lookupSymbol ident symTab of
  Just ct -> pure (Just ct)
  Nothing -> do
    tell [Diagnostic label (AnnP (UnknownConstraintType ident.name) loc p) []]
    pure Nothing

{- Note [Occurrence numbering order]

'collectOccurrences' folds each rule's occurrences into the
'OccurrenceMap' with 'occMapAppend', which is implemented on top of
@Map.insertWith (++)@ and therefore prepends. Reversing the resulting
list before 'assignNumbers' restores top-down rule order so that
occurrence number 1 is the textually first occurrence of the
constraint, matching the convention in the paper's Listings.

Partner ordering inside 'ruleOccurrences' is "removed first,
right-to-left": this is the ωr refined operational semantics from
Duck et al. (2004) and the paper §2.2, Fig. 2. Removed occurrences are
tried before kept ones so that simplifications fire eagerly, and within
each group the rightmost head constraint gets the lowest occurrence
number so that join order matches a left-to-right scan of the body when
the rule is read as a Horn clause.
-}

{- Note [Anonymous rule names]

Anonymous rules get a synthetic @__rule_N@ display name in
'ruleDisplayName'. N is the rule's program-wide source position, the
same number as its 'RuleId', so each anonymous rule gets its own name in
diagnostics, stack frames and traces. The propagation history is keyed
on the 'RuleId', not on the name.
-}
