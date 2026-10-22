{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Internal.Desugar.AggregateScope
-- Description : Which names an aggregate shares, owns and binds.
--
-- Fills the binder fields of 'D.Aggregate' ('D.aggShared', 'D.aggLocals',
-- 'D.aggBinds') and its result pattern's head normal form
-- ('D.aggResult'). The compiler and the type checker both read them, so
-- the two agree on the scopes by construction. See
-- @docs\/reference\/aggregates.md@ §Variables and
-- @docs\/reference\/type-system.md@ §Scopes.
--
-- The walk tracks what is bound before each aggregate runs. At the top
-- level that is the regular heads' variables, the variables the head's
-- HNF guards extract, and what the aggregates to its left bind. Inside a
-- goal it is the enclosing aggregate's shared names plus what the
-- conjuncts so far bind, in goal order: a constraint's arguments, the
-- variables its HNF guards extract, and what a nested aggregate binds.
module YCHR.Internal.Desugar.AggregateScope
  ( scopeAggregates,
    aggregateMentionedVars,
    aggregateGoalLocals,
  )
where

import Control.Monad.Trans.State.Strict (State, evalState, get, put, runState)
import Data.Foldable (toList)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Desugar.Hnf (HnfState (..), hnfState, normalizeArg)
import YCHR.Internal.Desugar.Vars (exprVars, guardVars, headArgVars)
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Types (AggregateKind (..), HeadArg (..), Term (..))

-- | Fill the binder fields of a rule's aggregates, given the names bound
-- before the first one.
scopeAggregates :: Set Text -> [D.Aggregate] -> [D.Aggregate]
scopeAggregates bound0 aggs = evalState (go bound0 aggs) 0
  where
    go _ [] = pure []
    go bound (a : rest) =
      (:) <$> scopeAggregate bound a <*> go (boundAfter bound a) rest

-- | Fill one aggregate's fields, and those of the aggregates nested in its
-- goal. The state numbers the @$res_N@ names, which have to be unique in
-- the rule.
scopeAggregate :: Set Text -> D.Aggregate -> State Int D.Aggregate
scopeAggregate bound a = do
  result <-
    if a.kind == AggPlain
      then Just <$> resultHnf bound a.result
      else pure Nothing
  goal' <- scopeGoal (Set.fromList shared) a.goal
  let own = exprVars a.element `Set.union` Set.unions (map conjunctVars goal')
      -- A selection's goal variables are what it binds: they are visible.
      -- A plain form's result is matched outside the goal, so a result
      -- variable that the goal also mentions is a local too.
      locals
        | a.kind == AggPlain = own `Set.difference` Set.fromList shared
        | otherwise =
            own `Set.difference` Set.fromList shared `Set.difference` Set.fromList binds
  pure
    a
      { D.goal = goal',
        D.aggShared = shared,
        D.aggLocals = Set.toAscList locals,
        D.aggBinds = binds,
        D.aggResult = result
      }
  where
    shared = Set.toAscList (aggregateMentionedVars a `Set.intersection` bound)
    binds = aggregateBinds bound a
    conjunctVars (D.AggConstraint hc guards) =
      Set.unions (map headArgVars hc.args) `Set.union` guardVars guards
    conjunctVars (D.AggGuard g) = guardVars [g]
    conjunctVars (D.AggNested nested) = Set.fromList nested.aggBinds

-- | Fill the fields of the aggregates nested in a goal, tracking what the
-- goal has bound at each position.
scopeGoal :: Set Text -> [D.AggregateConjunct] -> State Int [D.AggregateConjunct]
scopeGoal _ [] = pure []
scopeGoal scope (c : rest) = case c of
  D.AggConstraint hc guards ->
    let scope' =
          Set.unions (scope : map headArgVars hc.args)
            `Set.union` Set.fromList [v | D.GuardGetArg v _ _ <- guards]
     in (c :) <$> scopeGoal scope' rest
  D.AggGuard _ -> (c :) <$> scopeGoal scope rest
  D.AggNested nested ->
    (:)
      <$> (D.AggNested <$> scopeAggregate scope nested)
      <*> scopeGoal (boundAfter scope nested) rest

-- | The result pattern in head normal form, with @bound@ as what HNF has
-- already seen: a bound variable is a test, a fresh one a binding.
resultHnf :: Set Text -> Term -> State Int D.AggregateResult
resultHnf bound t = do
  n <- get
  let (arg, st) =
        runState
          (normalizeArg t)
          hnfState {counter = n, seen = bound, prefix = resultPrefix}
      guards = toList st.guards
  case arg of
    HeadVar v -> do
      put st.counter
      pure (D.AggregateResult v guards)
    -- A wildcard still needs a slot to type the payload in.
    HeadWildcard -> do
      put (st.counter + 1)
      pure (D.AggregateResult (resultPrefix <> T.pack (show st.counter)) guards)

-- | Prefix of the fresh result variables. @$@ keeps them apart from source
-- variables, and @res@ from HNF's @$hnf_N@.
resultPrefix :: Text
resultPrefix = "$res_"

-- | The names an aggregate binds in the enclosing scope: a selection
-- binds its goal's variables, the core form what its result pattern
-- introduces, in pattern order.
aggregateBinds :: Set Text -> D.Aggregate -> [Text]
aggregateBinds bound a
  | a.kind /= AggPlain = Set.toAscList (selectionGoalVars a.goal `Set.difference` bound)
  | otherwise = go Set.empty [a.result]
  where
    go _ [] = []
    go seen (t : ts) = case t of
      VarTerm v
        | v `Set.member` bound || v `Set.member` seen -> go seen ts
        | otherwise -> v : go (Set.insert v seen) ts
      CompoundTerm _ args -> go seen (args ++ ts)
      _ -> go seen ts

-- | What is in scope after an aggregate: its result, whether the pattern
-- bound it or checked it, or the goal variables of a selection.
boundAfter :: Set Text -> D.Aggregate -> Set Text
boundAfter bound a
  | a.kind /= AggPlain = bound `Set.union` selectionGoalVars a.goal
  | otherwise = bound `Set.union` termVars a.result

-- | Every variable an aggregate mentions, in any of its four positions,
-- and in the four positions of every aggregate nested in its goal. A head
-- variable that only a nested @Element@ reads is still an input, so it has
-- to be passed down.
aggregateMentionedVars :: D.Aggregate -> Set Text
aggregateMentionedVars a =
  Set.unions
    [ maybe Set.empty exprVars a.agg,
      exprVars a.element,
      aggregateGoalLocals a.goal,
      Set.unions [aggregateMentionedVars n | D.AggNested n <- a.goal],
      termVars a.result
    ]

-- | Variables a goal binds, so the procedure may read them as locals: the
-- arguments of its constraint conjuncts, the fresh variables their HNF
-- guards introduce, the variables a @?@ guard mentions, and — for a nested
-- aggregate — whatever its own goal and result pattern bind.
aggregateGoalLocals :: [D.AggregateConjunct] -> Set Text
aggregateGoalLocals = Set.unions . map conjunctVars
  where
    conjunctVars (D.AggConstraint hc guards) =
      Set.unions (map headArgVars hc.args) `Set.union` guardVars guards
    conjunctVars (D.AggGuard g) = guardVars [g]
    conjunctVars (D.AggNested n) =
      aggregateGoalLocals n.goal `Set.union` termVars n.result

-- | The variables a selection's goal makes visible to the rest of the
-- rule: the arguments of its constraint conjuncts, the variables their
-- HNF guards extract from a compound argument, and what a nested
-- aggregate binds. A @?@ guard binds nothing, and HNF's own fresh names
-- (@$hnf_N@) are not source variables, so neither is included.
selectionGoalVars :: [D.AggregateConjunct] -> Set Text
selectionGoalVars = Set.filter (not . T.isPrefixOf "$") . Set.unions . map conjunctVars
  where
    conjunctVars (D.AggConstraint hc guards) =
      Set.unions (map headArgVars hc.args)
        `Set.union` Set.fromList [v | D.GuardGetArg v _ _ <- guards]
    -- A nested aggregate shows what it binds and keeps its locals.
    conjunctVars (D.AggNested n) = boundAfter Set.empty n
    conjunctVars (D.AggGuard _) = Set.empty

-- | The variables a term mentions.
termVars :: Term -> Set Text
termVars t = case t of
  VarTerm v -> Set.singleton v
  Wildcard -> Set.empty
  IntTerm _ -> Set.empty
  FloatTerm _ -> Set.empty
  TextTerm _ -> Set.empty
  CompoundTerm _ args -> Set.unions (map termVars args)
