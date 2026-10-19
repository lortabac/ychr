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
--   * which variables of an aggregate are /shared/ — the inputs the
--     procedure takes as parameters — and which are local to its goal, as
--     the spec defines it: a variable is shared when it also occurs in the
--     rule's regular heads or in an earlier aggregate's result (for a
--     nested aggregate: when the enclosing goal has bound it by then). The
--     partition therefore does not depend on which occurrence is active,
--     so one plan serves every occurrence of a rule and one procedure
--     serves every plan.
--
--   * what the computed result is matched against, as a 'ResultMatch': the
--     tests the pattern has to pass and the bindings that follow them.
--
--   * the plans of the aggregates nested in a goal ('planNested').
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
    aggregateGoalLocals,
    aggregateResultTypeDeclared,

    -- * Result matching
    aggregateResultMatch,
  )
where

import Control.Monad.Trans.Writer.CPS (Writer, tell)
import Data.Foldable (toList)
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Compile.Names
import YCHR.Internal.Compile.Types
import YCHR.Internal.Desugar (bodyGoalVars, guardVars)
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Diagnostic (Diagnostic (..))
import YCHR.Internal.Parsed (AnnP (..))
import YCHR.Internal.Types
  ( AggregateKind (..),
    DataConstructor (..),
    HeadArg (..),
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
  plans <- go 0 headVars [] (rule.head.node.aggregates)
  checkLocalEscapes rule plans
  pure plans
  where
    headVars =
      Set.unions
        [ argVars arg
        | hc <- rule.head.node.kept ++ rule.head.node.removed,
          arg <- hc.args
        ]
        `Set.union` hnfBoundVars
    -- HNF decomposes a compound head argument into a fresh variable plus
    -- 'GuardGetArg' guards, so a variable introduced that way —
    -- @c(f(X)), count(d(X), N)@ — is a head variable too, not a goal
    -- local. Only HNF emits 'GuardGetArg', so the rule's guards contain
    -- no other binding form.
    hnfBoundVars = Set.fromList [v | D.GuardGetArg v _ _ <- rule.guard.node]

    go _ _ acc [] = pure (reverse acc)
    go k bound acc (a : rest) = do
      supported <- checkSupported rule a
      if not supported
        then go (k + 1) bound acc rest
        else do
          plan <- planAggregate ruleIdx rule [k] bound a
          go (k + 1) (boundAfter bound a) (plan : acc) rest

-- | Plan one aggregate at @path@, given the variables in scope where it is
-- computed: the regular heads and the aggregates to its left for a
-- top-level one, the enclosing goal so far for a nested one.
planAggregate ::
  Int ->
  D.Rule ->
  [Int] ->
  Set Text ->
  D.Aggregate ->
  Writer [Diagnostic CompileError] AggregatePlan
planAggregate ruleIdx rule path bound a = do
  nested <- planNestedAggregates ruleIdx rule path (Set.fromList shared) a.goal
  pure
    AggregatePlan
      { planIndex = case reverse path of
          i : _ -> i
          [] -> 0,
        planPath = path,
        planKind = a.kind,
        planProcName = aggregateProcName ruleIdx path,
        planAgg = a.agg,
        planElement = a.element,
        planGoal = a.goal,
        planShared = shared,
        planBind = aggregateBinds bound a,
        planResultMatch = resultMatch,
        planNested = nested
      }
  where
    shared = Set.toAscList (aggregateMentionedVars a `Set.intersection` bound)
    resolve v
      | Just i <- List.elemIndex v shared = Just (Var (aggregateSharedParam i))
      | otherwise = Nothing
    resultMatch
      | a.kind /= AggPlain = mempty
      | otherwise = aggregateResultMatch (Var aggregatePayloadName) resolve a.result

-- | The variables an aggregate's procedure binds through its out-cells, in
-- the order of its out parameters. A selection binds the goal's own
-- variables: they are the selected match's values, visible to the rest of
-- the rule (or of the enclosing goal). The core form binds the variables
-- its result pattern introduces.
aggregateBinds :: Set Text -> D.Aggregate -> [Text]
aggregateBinds bound a
  | a.kind /= AggPlain = Set.toAscList (selectionGoalVars a.goal `Set.difference` bound)
  | otherwise =
      map fst (aggregateResultMatch (Var aggregatePayloadName) resolve a.result).resultBinds
  where
    resolve v
      | v `Set.member` bound = Just (Var (Name v))
      | otherwise = Nothing

-- | What is in scope after an aggregate: its result, whether the pattern
-- bound it or checked it, or the goal variables of a selection.
boundAfter :: Set Text -> D.Aggregate -> Set Text
boundAfter bound a
  | a.kind /= AggPlain = bound `Set.union` selectionGoalVars a.goal
  | otherwise = bound `Set.union` termVars a.result

-- | Plan the aggregates nested in a goal. The walk follows the goal in goal
-- order and tracks what the fold has in scope at each position, the same
-- way 'YCHR.Internal.Compile.wrapGoalConjuncts' extends its variable map:
-- the arguments of a constraint conjunct, the variables its HNF guards
-- extract, and the variables an earlier nested aggregate binds.
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
  Set Text ->
  [D.AggregateConjunct] ->
  Writer [Diagnostic CompileError] [(Int, AggregatePlan)]
planNestedAggregates ruleIdx rule path = go 0
  where
    go _ _ [] = pure []
    go j scope (c : rest) = case c of
      D.AggConstraint hc guards ->
        let scope' =
              Set.unions (scope : map argVars hc.args)
                `Set.union` Set.fromList [v | D.GuardGetArg v _ _ <- guards]
         in go (j + 1) scope' rest
      D.AggGuard _ -> go (j + 1) scope rest
      D.AggNested n -> do
        let locals =
              aggregateMentionedVars n
                `Set.difference` scope
                `Set.difference` Set.fromList (aggregateBinds scope n)
            tooEarly =
              locals `Set.intersection` aggregateGoalLocals [r | r <- rest, not (isNested r)]
        tell
          [ Diagnostic label (AnnP (UnboundVariable v) loc origin) []
          | v <- Set.toAscList tooEarly
          ]
        plan <- planAggregate ruleIdx rule (path ++ [j]) scope n
        ((j, plan) :) <$> go (j + 1) (boundAfter scope n) rest

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
        [ aggregateGoalLocals p.planGoal
            `Set.difference` Set.fromList p.planShared
            `Set.difference` Set.fromList p.planBind
        | p <- plans
        ]
    visible = Set.fromList [v | p <- plans, isSelectionPlan p, v <- p.planBind]
    escaped =
      (locals `Set.difference` visible)
        `Set.intersection` ( guardVars rule.guard.node
                               `Set.union` bodyGoalVars rule.body.node
                           )
    label = fmap ("rule " <>) rule.name
    loc = rule.head.sourceLoc
    origin = rule.head.parsed

-- | The variables a rule head constraint binds.
argVars :: HeadArg -> Set Text
argVars (HeadVar v) = Set.singleton v
argVars HeadWildcard = Set.empty

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
      Set.unions (map argVars hc.args) `Set.union` guardVars guards
    conjunctVars (D.AggGuard g) = guardVars [g]
    conjunctVars (D.AggNested n) =
      aggregateGoalLocals n.goal `Set.union` termVars n.result

-- | The variables a selection's goal makes visible to the rest of the
-- rule: the arguments of its constraint conjuncts, the variables their
-- HNF guards extract from a compound argument, and what a nested
-- aggregate binds. A @?@ guard binds nothing,
-- and HNF's own fresh names (@$hnf_N@) are not source variables, so
-- neither is included.
selectionGoalVars :: [D.AggregateConjunct] -> Set Text
selectionGoalVars = Set.filter (not . T.isPrefixOf "$") . Set.unions . map conjunctVars
  where
    conjunctVars (D.AggConstraint hc guards) =
      Set.unions (map argVars hc.args)
        `Set.union` Set.fromList [v | D.GuardGetArg v _ _ <- guards]
    -- A nested aggregate shows what it binds and keeps its locals.
    conjunctVars (D.AggNested n) = boundAfter Set.empty n
    conjunctVars (D.AggGuard _) = Set.empty

-- | The variables an expression mentions. A lambda's parameters are
-- subtracted: the desugarer's lifter has already replaced every lambda with
-- a closure term by the time the compiler runs, so this arm exists only to
-- keep the walk total.
exprVars :: D.Expr -> Set Text
exprVars e = case e of
  D.VarExpr v -> Set.singleton v
  D.IntExpr _ -> Set.empty
  D.FloatExpr _ -> Set.empty
  D.TextExpr _ -> Set.empty
  D.WildcardExpr -> Set.empty
  D.FunRefExpr _ _ -> Set.empty
  D.CtorExpr _ args -> Set.unions (map exprVars args)
  D.CallExpr _ args -> Set.unions (map exprVars args)
  D.ApplyExpr f args -> exprVars f `Set.union` Set.unions (map exprVars args)
  D.HostExpr _ args -> Set.unions (map exprVars args)
  D.LambdaExpr params body ->
    Set.unions (map exprVars (toList body))
      `Set.difference` Set.fromList [v | HeadVar v <- toList params]

-- | The variables a term mentions.
termVars :: Term -> Set Text
termVars t = case t of
  VarTerm v -> Set.singleton v
  Wildcard -> Set.empty
  IntTerm _ -> Set.empty
  FloatTerm _ -> Set.empty
  TextTerm _ -> Set.empty
  CompoundTerm _ args -> Set.unions (map termVars args)

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
maybeTypeName :: Types.Name
maybeTypeName = Types.Qualified "maybe" "maybe"

justConName :: Types.Name
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
aggregateResultMatch payload resolve term = fst (go Map.empty [] term)
  where
    at [] = payload
    at path = List.foldl' (\e i -> GetArg e i) payload path

    -- @bound@ maps each variable the pattern has already bound to the
    -- path it was bound at, so a repeated variable is tested against the
    -- first occurrence instead of being bound twice (which would be two
    -- independent unifications of the same name).
    go :: Map.Map Text [Word] -> [Word] -> Term -> (ResultMatch, Map.Map Text [Word])
    go bound path t = case t of
      Wildcard -> (mempty, bound)
      VarTerm v -> case resolve v of
        Just e -> (test (BEqual e (at path)), bound)
        Nothing -> case Map.lookup v bound of
          Just first -> (test (BEqual (at first) (at path)), bound)
          Nothing -> (ResultMatch [] [(v, at path)], Map.insert v path bound)
      IntTerm n -> (test (BEqual (Lit (IntLit n)) (at path)), bound)
      FloatTerm f -> (test (BEqual (Lit (FloatLit f)) (at path)), bound)
      TextTerm s -> (test (BEqual (Lit (TextLit s)) (at path)), bound)
      CompoundTerm name [] ->
        (test (BEqual (Lit (AtomLit (functorAtom name))) (at path)), bound)
      CompoundTerm name args ->
        let step (rm, b) (i, arg) =
              let (rm', b') = go b (path ++ [i]) arg
               in (rm <> rm', b')
            (argsMatch, bound') =
              List.foldl' step (mempty, bound) (zip [0 ..] args)
         in ( test (BMatchTerm (at path) (vmName name) (fromIntegral (length args)))
                <> argsMatch,
              bound'
            )

    test b = ResultMatch [b] []

-- | The atom a zero-arity constructor has at run time, matching
-- 'YCHR.Internal.Compile.compileTerm'.
functorAtom :: Types.Name -> Text
functorAtom name = (vmName name).unName
