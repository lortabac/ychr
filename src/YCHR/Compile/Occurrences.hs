{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Compile.Occurrences
-- Description : Pre-pass that collects and numbers head occurrences.
--
-- This module owns the first phase of the CHR-to-VM compiler: walking
-- every rule head and producing, for each constraint type, a top-down
-- list of 'Occurrence' records numbered as required by the refined
-- operational semantics ωr (paper §2.2, Fig. 2). The result is a single
-- 'OccurrenceMap' that the rest of 'YCHR.Compile' consumes.
--
-- See the \"Notes\" block in 'YCHR.Compile' for the rationale behind the
-- ordering and numbering choices.
module YCHR.Compile.Occurrences
  ( collectOccurrences,
  )
where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Traversable (for)
import Effectful (Eff)
import Effectful.Writer.Static.Local (Writer, tell)
import YCHR.Compile.Types
import YCHR.Desugared qualified as D
import YCHR.Diagnostic (Diagnostic (..))
import YCHR.PExpr (PExpr)
import YCHR.Parsed (AnnP (..))
import YCHR.Parsed qualified as P
import YCHR.Types (Constraint, Identifier (..), RuleId (..), SymbolTable, lookupSymbol)
import YCHR.VM (ConstraintType (..))

-- | Walk every rule in the program and assemble the per-constraint
-- 'OccurrenceMap'. Occurrences are numbered top-down within each
-- constraint type so that occurrence number 1 is the textually first
-- occurrence (paper §5.2, Listings 1 and 2).
--
-- Also returns the list of per-rule display names, indexed by the
-- rule's 'RuleId' (which mirrors its program-wide source index).
collectOccurrences :: SymbolTable -> D.Program -> Eff '[Writer [Diagnostic CompileError]] (OccurrenceMap, [Text])
collectOccurrences symTab prog = do
  let indexed = zip [0 ..] prog.rules
      displayNames = map (uncurry ruleDisplayName) indexed
  allOccs <- fmap concat (traverse (ruleOccurrences symTab) indexed)
  let grouped = foldl' (\m occ -> occMapAppend (Identifier occ.conName occ.conArity) occ m) occMapEmpty allOccs
  pure (occMapMap (assignNumbers . reverse) grouped, displayNames)
  where
    -- Reverse before numbering to undo the prepend-on-insert in
    -- 'occMapAppend' and restore top-down rule order.
    assignNumbers = zipWith (\n o -> o {number = n}) [OccurrenceNumber 1 ..]

-- | Compute the display name of a rule. Anonymous rules get a
-- synthetic @__rule_N@ name whose index matches the rule's
-- program-wide source position. The double-underscore prefix avoids
-- clashes with user-defined names.
ruleDisplayName :: Int -> D.Rule -> Text
ruleDisplayName ruleIdx rule = case rule.name of
  Just n -> n
  Nothing -> "__rule_" <> T.pack (show ruleIdx)

-- | Produce one 'Occurrence' record for every head constraint of a
-- single rule. The active head varies; the other heads become the
-- partner list of that occurrence.
ruleOccurrences :: SymbolTable -> (Int, D.Rule) -> Eff '[Writer [Diagnostic CompileError]] [Occurrence]
ruleOccurrences symTab (ruleIdx, rule) = do
  let AnnP {node = ruleHead} = rule.head
      kept = ruleHead.kept
      removed = ruleHead.removed
      -- Occurrences are ordered removed-first, right-to-left within
      -- each group, following the ωr refined operational semantics
      -- (paper §2.2, Fig. 2). Removed occurrences are tried before
      -- kept ones, and within each group the rightmost head constraint
      -- gets the lowest (earliest) occurrence number.
      orderedOccurrences =
        [(i, c, False) | (i, c) <- zip [HeadPosition 0 ..] (reverse removed)]
          ++ [(i, c, True) | (i, c) <- zip [HeadPosition (length removed) ..] (reverse kept)]
      ruleId' = RuleId ruleIdx
      display = ruleDisplayName ruleIdx rule
  for orderedOccurrences $ \(idx, con, isKept) ->
    mkOccurrence symTab rule ruleId' display orderedOccurrences idx con isKept

-- | Build a single 'Occurrence' record for the active head constraint
-- at @activeIdx@. The other entries in @combined@ become the partner
-- list.
mkOccurrence ::
  SymbolTable ->
  D.Rule ->
  RuleId ->
  Text ->
  [(HeadPosition, Constraint, Bool)] ->
  HeadPosition ->
  Constraint ->
  Bool ->
  Eff '[Writer [Diagnostic CompileError]] Occurrence
mkOccurrence symTab rule ruleId' display combined activeIdx activeCon activeIsKept = do
  let partners' = [(idx, con, isKept) | (idx, con, isKept) <- combined, idx /= activeIdx]
      headLoc = rule.head.sourceLoc
      headPretty = rule.head.parsed
  let ruleLabel = Just ("rule " <> display)
  partners <- for partners' $ \(idx, con, isKept) -> do
    ct <- lookupCType symTab headLoc headPretty ruleLabel (Identifier con.name (length con.args))
    pure
      Partner
        { idx = idx,
          constraint = con,
          isKept = isKept,
          cType = ct
        }
  pure
    Occurrence
      { conName = activeCon.name,
        conArity = length activeCon.args,
        number = OccurrenceNumber 0,
        rule = rule,
        ruleId = ruleId',
        ruleDisplay = display,
        activeIdx = activeIdx,
        isKept = activeIsKept,
        activeArgs = activeCon.args,
        partners = partners
      }

-- | Look up a constraint type in the symbol table or report an error.
-- Returns a placeholder 'ConstraintType' on failure so that the rest
-- of the pass can keep going and collect more diagnostics.
lookupCType ::
  SymbolTable ->
  P.SourceLoc ->
  PExpr ->
  Maybe Text ->
  Identifier ->
  Eff '[Writer [Diagnostic CompileError]] ConstraintType
lookupCType symTab loc p label ident = case lookupSymbol ident symTab of
  Just ct -> pure ct
  Nothing -> do
    tell [Diagnostic label (AnnP (UnknownConstraintType ident.name) loc p)]
    pure (ConstraintType (-1))
