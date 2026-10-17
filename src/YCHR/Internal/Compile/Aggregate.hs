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
--     rule's regular heads or in an earlier aggregate's result. The
--     partition therefore does not depend on which occurrence is active,
--     so one plan serves every occurrence of a rule and one procedure
--     serves every plan.
--
--   * what the computed result is matched against, as a 'ResultMatch': the
--     tests the pattern has to pass and the bindings that follow them.
--
--   * the diagnostics for a form this compiler does not implement yet, and
--     for a program whose aggregators cannot produce the result type the
--     protocol needs.
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
-- A form this compiler does not implement yet is reported and dropped, so
-- one unsupported aggregate does not hide the aggregates after it.
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
          let shared =
                Set.toAscList (aggregateMentionedVars a `Set.intersection` bound)
              resolve v
                | Just i <- List.elemIndex v shared =
                    Just (Var (aggregateSharedParam i))
                | otherwise = Nothing
              resultMatch =
                aggregateResultMatch (Var aggregatePayloadName) resolve a.result
              plan =
                AggregatePlan
                  { planIndex = k,
                    planProcName = aggregateProcName ruleIdx k,
                    planAgg = a.agg,
                    planElement = a.element,
                    planGoal = a.goal,
                    planShared = shared,
                    planBind = map fst resultMatch.resultBinds,
                    planResultMatch = resultMatch
                  }
              -- The result of an aggregate is in scope for every aggregate
              -- to its right, whether the pattern bound it or checked it.
              bound' = bound `Set.union` termVars a.result
          go (k + 1) bound' (plan : acc) rest

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
    -- A shared variable is a head variable, so it is not an escape; a result
    -- variable the pattern binds is in scope in the guard and body by
    -- design, and is not a goal local either.
    locals =
      Set.unions
        [ aggregateGoalLocals p.planGoal `Set.difference` Set.fromList p.planShared
        | p <- plans
        ]
    escaped =
      locals
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

-- | Every variable an aggregate mentions, in any of its four positions.
aggregateMentionedVars :: D.Aggregate -> Set Text
aggregateMentionedVars a =
  Set.unions
    [ maybe Set.empty exprVars a.agg,
      exprVars a.element,
      aggregateGoalLocals a.goal,
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

-- | Report the aggregate forms the compiler does not implement yet, and say
-- whether the aggregate can be planned.
--
-- Both checks are anchored at the rule head, since an aggregate carries no
-- source location of its own. The form name and arity are what the user
-- wrote, so the diagnostic points at something recognizable.
checkSupported :: D.Rule -> D.Aggregate -> Writer [Diagnostic CompileError] Bool
checkSupported rule a = do
  kindOk <- case a.kind of
    AggPlain -> pure True
    kind -> do
      report (aggregateKindName kind) (aggregateKindArity kind)
      pure False
  nestedOk <- case [() | D.AggNested _ <- a.goal] of
    [] -> pure True
    _ -> do
      report "aggregate" 4
      pure False
  pure (kindOk && nestedOk)
  where
    report name arity =
      tell
        [ Diagnostic
            label
            (AnnP (AggregateNotImplemented name arity) loc origin)
            []
        ]

    label = fmap ("rule " <>) rule.name
    loc = rule.head.sourceLoc
    origin = rule.head.parsed

-- | The reserved functor name of an aggregate kind, as the user wrote it.
aggregateKindName :: AggregateKind -> Text
aggregateKindName AggPlain = "aggregate"
aggregateKindName AggArgmin = "argmin"
aggregateKindName AggArgmax = "argmax"
aggregateKindName AggTakemin = "takemin"
aggregateKindName AggTakemax = "takemax"

-- | How many arguments an aggregate kind takes.
aggregateKindArity :: AggregateKind -> Int
aggregateKindArity AggPlain = 4
aggregateKindArity _ = 2

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
