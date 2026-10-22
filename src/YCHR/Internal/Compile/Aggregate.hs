{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Internal.Compile.Aggregate
-- Description : Plan the head aggregates of one rule.
--
-- An aggregate is a head conjunct that summarizes an unbounded part of
-- the constraint store. The compiler lowers it to a generated procedure
-- that folds over the goal's matches; see @docs\/reference\/aggregates.md@
-- for the language, and 'YCHR.Internal.Compile.genAggregateProcedure' for
-- the lowering, which stays in "YCHR.Internal.Compile" because it needs
-- that module's expression and guard compilers.
--
-- This module owns the part that is a function of the rule alone:
--
--   * the inputs the procedure takes as parameters and the names it binds,
--     read from 'D.aggShared' and 'D.aggBinds'
--     ("YCHR.Internal.Desugar.AggregateScope" fills them). The partition
--     does not depend on which occurrence is active, so one plan serves
--     every occurrence of a rule and one procedure serves every plan.
--
--   * what the computed result is matched against, as a 'ResultMatch': the
--     tests the pattern has to pass and the bindings that follow them.
--
--   * the plans of the aggregates nested in a goal ('nested').
--
--   * the diagnostics for a form this compiler does not allow (a nested
--     @takemin@\/@takemax@), and for a program whose aggregators cannot
--     produce the result type the protocol needs.
--
-- == Note [Aggregator representation]
--
-- The compiler assumes two things about @library(aggregates)@, both
-- recorded in @docs\/reference\/aggregates.md@:
--
--   * an @Agg@ expression evaluates to @aggregates:aggregator(Init, Inc,
--     Final)@, a three-argument compound, so its fields are @get-arg
--     0\/1\/2@. The generated procedure checks the shape with @bmatch-term@
--     before reading them, so a wrong one is a runtime error, not a silent
--     misread.
--
--   * @Final@ returns @library(maybe)@'s @maybe@: @just(Result)@ when the
--     aggregate is defined, @nothing@ when it is not. The procedure decodes
--     it with the @maybe:just@ functor, and treats anything that is neither
--     as a runtime error naming the protocol. A program that does not
--     declare @maybe:just\/1@ at all is reported at compile time by
--     'aggregateResultTypeDeclared'.
module YCHR.Internal.Compile.Aggregate
  ( -- * Planning
    collectAggregatePlans,
    aggregateResultTypeDeclared,

    -- * Result matching
    aggregateResultMatch,
  )
where

import Control.Monad (zipWithM)
import Control.Monad.Trans.State.Strict (State, evalState, get, put)
import Control.Monad.Trans.Writer.CPS (Writer, tell)
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import YCHR.Internal.Compile.Names
import YCHR.Internal.Compile.Types
import YCHR.Internal.Desugar (bodyGoalVars, guardVars)
import YCHR.Internal.Desugar.AggregateScope (aggregateGoalLocals, aggregateMentionedVars)
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Diagnostic (Diagnostic (..))
import YCHR.Internal.Parsed (AnnP (..))
import YCHR.Internal.Types
  ( AggregateKind (..),
    DataConstructor (..),
    Term (..),
    TypeDefinition (..),
    typeConstructors,
  )
import YCHR.Internal.Types qualified as Types
import YCHR.Internal.VM
-- Hidden so '.head' resolves under MicroHs (dev-docs/MICROHS_GAPS.md, gap 1).
import Prelude hiding (head)

-- ---------------------------------------------------------------------------
-- Planning
-- ---------------------------------------------------------------------------

-- | Plan every aggregate of a rule, in source order.
--
-- The rule's index is part of each procedure's name, which has to be unique
-- across the program; an aggregate's own index is part of its local names,
-- which only have to be unique within the procedure that uses them.
--
-- A form this compiler does not allow is reported and dropped, so one
-- bad aggregate does not hide the aggregates after it.
collectAggregatePlans ::
  Int ->
  D.Rule ->
  Writer [Diagnostic CompileError] [AggregatePlan]
collectAggregatePlans ruleIdx rule = do
  plans <- go 0 [] (rule.head.node.aggregates)
  checkLocalEscapes rule plans
  pure plans
  where
    go _ acc [] = pure (reverse acc)
    go k acc (a : rest) = do
      supported <- checkSupported rule a
      if not supported
        then go (k + 1) acc rest
        else do
          plan <- planAggregate ruleIdx rule [k] a
          go (k + 1) (plan : acc) rest

-- | Plan one aggregate at @path@.
planAggregate ::
  Int ->
  D.Rule ->
  [Int] ->
  D.Aggregate ->
  Writer [Diagnostic CompileError] AggregatePlan
planAggregate ruleIdx rule path a = do
  nested <- planNestedAggregates ruleIdx rule path a.goal
  pure
    AggregatePlan
      { position = case reverse path of
          i : _ -> i
          [] -> 0,
        path = path,
        kind = a.kind,
        procName = aggregateProcName ruleIdx path,
        agg = a.agg,
        element = a.element,
        goal = a.goal,
        shared = shared,
        bind = a.aggBinds,
        resultMatch = resultMatch,
        nested = nested
      }
  where
    shared = a.aggShared
    resolve v
      | Just i <- List.elemIndex v shared = Just (Var (aggregateSharedParam i))
      | otherwise = Nothing
    resultMatch
      | a.kind /= AggPlain = mempty
      | otherwise = aggregateResultMatch (Var aggregatePayloadName) resolve a.result

-- | Plan the aggregates nested in a goal, in goal order.
--
-- A variable of a nested aggregate that also occurs in a later conjunct of
-- the enclosing goal is shared by the spec, but nothing has bound it yet
-- when the nested aggregate is computed. That is reported as an unbound
-- variable, as for a @?@ guard that reads a variable too early. A later
-- nested aggregate does not count: as at the top level, two sibling
-- aggregates may each have a local of the same name.
planNestedAggregates ::
  Int ->
  D.Rule ->
  [Int] ->
  [D.AggregateConjunct] ->
  Writer [Diagnostic CompileError] [AggregatePlan]
planNestedAggregates ruleIdx rule path = go 0
  where
    go _ [] = pure []
    go j (c : rest) = case c of
      D.AggNested n -> do
        let locals =
              aggregateMentionedVars n
                `Set.difference` Set.fromList n.aggShared
                `Set.difference` Set.fromList n.aggBinds
            laterLocals = aggregateGoalLocals [r | r <- rest, not (isNested r)]
            tooEarly = locals `Set.intersection` laterLocals
        tell
          [ Diagnostic label (AnnP (UnboundVariable v) loc origin) []
          | v <- Set.toAscList tooEarly
          ]
        plan <- planAggregate ruleIdx rule (path ++ [j]) n
        (plan :) <$> go (j + 1) rest
      _ -> go (j + 1) rest

    isNested (D.AggNested _) = True
    isNested _ = False

    label = fmap ("rule " <>) rule.name
    loc = rule.head.sourceLoc
    origin = rule.head.parsed

-- | Report every variable only an aggregate's goal binds that the rule's
-- guard or body reads anyway.
--
-- Such a variable is not a distinct rule variable: it is renamed apart per
-- match, so a use in the guard or body would silently read whatever the last
-- match left in it. Reporting the escape turns a typo into a diagnostic
-- instead of a rule that quietly reads the wrong value.
checkLocalEscapes ::
  D.Rule ->
  [AggregatePlan] ->
  Writer [Diagnostic CompileError] ()
checkLocalEscapes rule plans = case Set.toAscList escaped of
  [] -> pure ()
  variables ->
    tell
      [ Diagnostic
          label
          (AnnP (AggregateLocalEscapes v) loc origin)
          []
      | v <- variables
      ]
  where
    -- A shared variable is a head variable, so it is not an escape, and a
    -- variable the result pattern binds is bound by the aggregate call, so
    -- it is in scope in the guard and body by design. Every other variable
    -- a goal binds is local to the aggregate.
    --
    -- A selection's goal variables are visible, so its only locals are
    -- those of the aggregates nested in its goal, and a name it binds is
    -- not an escape even when another aggregate has a local of the same
    -- name. The same formula covers both kinds: a selection binds its
    -- visible goal variables.
    locals =
      Set.unions
        [ aggregateGoalLocals p.goal
            `Set.difference` Set.fromList p.shared
            `Set.difference` Set.fromList p.bind
        | p <- plans
        ]
    visible = Set.fromList [v | p <- plans, isSelectionPlan p, v <- p.bind]
    escaped =
      (locals `Set.difference` visible)
        `Set.intersection` ( guardVars rule.guard.node
                               `Set.union` bodyGoalVars rule.body.node
                           )
    label = fmap ("rule " <>) rule.name
    loc = rule.head.sourceLoc
    origin = rule.head.parsed

-- | Report a @takemin@\/@takemax@ nested anywhere in an aggregate's goal,
-- which is not allowed, and say whether the aggregate can be planned.
--
-- The check is anchored at the rule head, since an aggregate carries no
-- source location of its own.
checkSupported :: D.Rule -> D.Aggregate -> Writer [Diagnostic CompileError] Bool
checkSupported rule a = case nestedTakes a of
  [] -> pure True
  takes -> do
    tell
      [ Diagnostic label (AnnP (AggregateNestedTake (takeName k)) loc origin) []
      | k <- takes
      ]
    pure False
  where
    nestedTakes agg =
      concat
        [ [n.kind | n.kind == AggTakemin || n.kind == AggTakemax] ++ nestedTakes n
        | D.AggNested n <- agg.goal
        ]
    takeName AggTakemax = "takemax"
    takeName _ = "takemin"
    label = fmap ("rule " <>) rule.name
    loc = rule.head.sourceLoc
    origin = rule.head.parsed

-- | Whether the program declares @library(maybe)@'s @maybe\/1@ and its
-- @just\/1@ constructor: what an aggregator's @Final@ closure has to return.
-- Checked once for the whole program, and only when some rule has an
-- aggregate, so a program that uses none gains no diagnostic.
--
-- The check reads the program's own type definitions, so a program that
-- declares its own @maybe@ is accepted on the same terms as one that
-- imports the library.
aggregateResultTypeDeclared :: [TypeDefinition] -> Bool
aggregateResultTypeDeclared typeDefs = any declaresMaybe typeDefs
  where
    declaresMaybe td =
      td.name == maybeTypeName
        && any
          (\dc -> dc.conName == justConName && length dc.conArgs == 1)
          (typeConstructors td)

-- | @library(maybe)@'s type and the constructor the protocol needs. Both
-- are qualified with their declaring module, which the renamer fixes.
maybeTypeName, justConName :: Types.Name
maybeTypeName = Types.Qualified "maybe" "maybe"
justConName = Types.Qualified "maybe" "just"

-- ---------------------------------------------------------------------------
-- Result matching
-- ---------------------------------------------------------------------------

-- | Compile a result pattern against the computed payload.
--
-- Every test precedes every binding, so a pattern that cannot match leaves
-- the out-cells untouched: the rule does not apply and no half-done binding
-- survives the guard's soft failure. A variable already in scope — a shared
-- input — is compared with @BEqual@, which has ask semantics and is total
-- on unbound operands, while a fresh one (or one that repeats an earlier
-- position of the same pattern) is either bound or compared against the
-- first occurrence's value. The out-cell is always the /left/ operand of
-- that @BUnify@: unification binds its left operand and returns that
-- operand's observers, so binding a fresh cell enqueues no reactivation,
-- whereas the other order would bind the computed result and enqueue
-- whatever observes it — inside the guard window, where Late Storage
-- leaves the active constraint unstored. See @dev-docs\/INVARIANTS.md@.
--
-- A variable of the goal that the result pattern mentions is /not/ an
-- input here: the goal's variables are local to the aggregate, and after
-- the fold the loop slot holds only the last match's value (or nothing).
-- It is bound as a fresh result variable instead.
aggregateResultMatch ::
  -- | The computed payload, in the procedure that computes it.
  ValExpr ->
  -- | A variable already in scope there, or 'Nothing' when the pattern has
  -- to bind it.
  (Text -> Maybe ValExpr) ->
  Term ->
  ResultMatch
aggregateResultMatch payload resolve term = evalState (go [] term) Map.empty
  where
    at [] = payload
    at path = List.foldl' (\e i -> GetArg e i) payload path

    -- The state maps each variable the pattern has already bound to the
    -- path it was bound at, so a repeated variable is tested against the
    -- first occurrence instead of being bound twice (which would be two
    -- independent unifications of the same name).
    go :: [Word] -> Term -> State (Map.Map Text [Word]) ResultMatch
    go path t = case t of
      Wildcard -> pure mempty
      VarTerm v -> case resolve v of
        Just e -> pure (test (BEqual e (at path)))
        Nothing -> do
          bound <- get
          case Map.lookup v bound of
            Just first -> pure (test (BEqual (at first) (at path)))
            Nothing -> do
              put (Map.insert v path bound)
              pure (ResultMatch [] [ResultBind {var = v, value = at path}])
      IntTerm n -> pure (test (BEqual (Lit (IntLit n)) (at path)))
      FloatTerm f -> pure (test (BEqual (Lit (FloatLit f)) (at path)))
      TextTerm s -> pure (test (BEqual (Lit (TextLit s)) (at path)))
      CompoundTerm name [] ->
        pure (test (BEqual (Lit (AtomLit (functorAtom name))) (at path)))
      CompoundTerm name args -> do
        argsMatch <- zipWithM (\i arg -> go (path ++ [i]) arg) [0 ..] args
        pure
          ( test (BMatchTerm (at path) (vmName name) (fromIntegral (length args)))
              <> mconcat argsMatch
          )

    test b = ResultMatch [b] []

-- | The atom a zero-arity constructor has at run time, matching
-- 'YCHR.Internal.Compile.compileTerm'.
functorAtom :: Types.Name -> Text
functorAtom name = (vmName name).unName
