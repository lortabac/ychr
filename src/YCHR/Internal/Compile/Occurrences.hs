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
-- in "YCHR.Internal.Compile" for the rationale behind the ordering and
-- numbering choices.
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
import YCHR.Internal.Compile.Passive (markPassive)
import YCHR.Internal.Compile.Types
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Diagnostic (Diagnostic (..))
import YCHR.Internal.PExpr (PExpr)
import YCHR.Internal.Parsed (AnnP (..))
import YCHR.Internal.Parsed qualified as P
import YCHR.Internal.Types
  ( HeadConstraint,
    Identifier (..),
    RuleId (..),
    SymbolTable,
    lookupSymbol,
    qualifiedToName,
  )
import YCHR.Internal.VM (ConstraintType (..))

-- | Walk every rule in the program and assemble the per-constraint
-- 'OccurrenceMap'. Occurrences are numbered top-down within each
-- constraint type so that occurrence number 1 is the textually first
-- occurrence (paper §5.2, Listings 1 and 2).
--
-- The result also carries the per-rule display names, indexed by the
-- rule's 'RuleId' (which mirrors its program-wide source index).
--
-- See Note [Occurrence numbering order] in "YCHR.Internal.Compile".
collectOccurrences ::
  SymbolTable ->
  D.Program ->
  Writer [Diagnostic CompileError] CollectedOccurrences
collectOccurrences symTab prog = do
  let indexed = zip [0 ..] prog.rules
      displayNames = map (uncurry ruleDisplayName) indexed
  allOccs <- fmap concat (traverse (ruleOccurrences symTab) indexed)
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
        ruleDisplayNames = displayNames
      }
  where
    -- Reverse before numbering to undo the prepend-on-insert in
    -- 'occMapAppend' and restore top-down rule order.
    assignNumbers = zipWith (\n o -> o {number = n}) [OccurrenceNumber 1 ..]

-- | Compute the display name of a rule. Anonymous rules get a
-- synthetic @__rule_N@ name whose index matches the rule's
-- program-wide source position. The double-underscore prefix avoids
-- clashes with user-defined names.
-- See Note [Anonymous rule names] in "YCHR.Internal.Compile".
ruleDisplayName :: Int -> D.Rule -> Text
ruleDisplayName ruleIdx rule = case rule.name of
  Just n -> n
  Nothing -> "__rule_" <> T.pack (show ruleIdx)

-- | Produce one 'Occurrence' record for every head constraint of a
-- single rule. The active head varies; the other heads become the
-- partner list of that occurrence.
ruleOccurrences ::
  SymbolTable ->
  ( Int,
    D.Rule
  ) ->
  Writer [Diagnostic CompileError] [Occurrence]
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
  fmap catMaybes $ for orderedOccurrences $ \(idx, con, isKept) ->
    mkOccurrence symTab rule ruleId' display orderedOccurrences idx con isKept

-- | Build a single 'Occurrence' record for the active head constraint
-- at @activeIdx@. The other entries in @combined@ become the partner
-- list.
--
-- Returns 'Nothing' when a partner's constraint type is not in the
-- symbol table: 'lookupCType' has already reported the miss, and an
-- occurrence with an unresolvable partner cannot be compiled.
mkOccurrence ::
  SymbolTable ->
  D.Rule ->
  RuleId ->
  Text ->
  [(HeadPosition, HeadConstraint, Bool)] ->
  HeadPosition ->
  HeadConstraint ->
  Bool ->
  Writer [Diagnostic CompileError] (Maybe Occurrence)
mkOccurrence symTab rule ruleId' display combined activeIdx activeCon activeIsKept = do
  let partners' = [(idx, con, isKept) | (idx, con, isKept) <- combined, idx /= activeIdx]
      headLoc = rule.head.sourceLoc
      headPretty = rule.head.parsed
  let ruleLabel = Just ("rule " <> display)
  partners <- for partners' $ \(idx, con, isKept) -> do
    ct <-
      lookupCType
        symTab
        headLoc
        headPretty
        ruleLabel
        ( Identifier
            (qualifiedToName con.name)
            ( length
                con.args
            )
        )
    pure $ do
      cType <- ct
      pure
        Partner
          { idx = idx,
            constraint = con,
            isKept = isKept,
            cType = cType
          }
  pure $ do
    resolvedPartners <- sequence partners
    pure
      Occurrence
        { conName = qualifiedToName activeCon.name,
          number = OccurrenceNumber 0,
          rule = rule,
          ruleId = ruleId',
          ruleDisplay = display,
          activeIdx = activeIdx,
          isKept = activeIsKept,
          activeArgs = activeCon.args,
          partners = resolvedPartners,
          passive = False
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
    tell [Diagnostic label (AnnP (UnknownConstraintType ident.name) loc p)]
    pure Nothing
