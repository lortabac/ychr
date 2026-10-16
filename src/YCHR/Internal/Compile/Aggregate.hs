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
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import YCHR.Internal.Compile.Names
import YCHR.Internal.Compile.Types
import YCHR.Internal.Desugar (guardVars)
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
collectAggregatePlans ruleIdx rule = go 0 headVars [] (rule.head.node.aggregates)
  where
    headVars =
      Set.unions
        [ argVars arg
        | hc <- rule.head.node.kept ++ rule.head.node.removed,
          arg <- hc.args
        ]

    go _ _ acc [] = pure (reverse acc)
    go k bound acc (a : rest) = do
      supported <- checkSupported rule a
      if not supported
        then go (k + 1) bound acc rest
        else do
          let goalLocals = aggregateGoalLocals a.goal
              shared =
                Set.toAscList (aggregateMentionedVars a `Set.intersection` bound)
              resolve v
                | Just i <- List.elemIndex v shared =
                    Just (Var (aggregateSharedParam i))
                | Set.member v goalLocals = Just (Var (Name v))
                | otherwise = Nothing
              resultMatch =
                aggregateResultMatch (Var aggregatePayloadName) resolve a.result
              plan =
                AggregatePlan
                  { planIndex = k,
                    planKind = a.kind,
                    planProcName = aggregateProcName ruleIdx k,
                    planAgg = a.agg,
                    planElement = a.element,
                    planGoal = a.goal,
                    planResult = a.result,
                    planShared = shared,
                    planBind = map fst resultMatch.resultBinds,
                    planResultMatch = resultMatch
                  }
              -- The result of an aggregate is in scope for every aggregate
              -- to its right, whether the pattern bound it or checked it.
              bound' = bound `Set.union` termVars a.result
          go (k + 1) bound' (plan : acc) rest

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
-- input or a goal-local — is compared with @BEqual@, which has ask
-- semantics and is total on unbound operands, while a fresh one is bound
-- with @BUnify@. The out-cell is always the /left/ operand of that
-- @BUnify@: unification binds its left operand and returns that operand's
-- observers, so binding a fresh cell enqueues no reactivation, whereas the
-- other order would bind the computed result and enqueue whatever observes
-- it — inside the guard window, where Late Storage leaves the active
-- constraint unstored. See @dev-docs\/INVARIANTS.md@.
aggregateResultMatch ::
  -- | The computed payload, in the procedure that computes it.
  ValExpr ->
  -- | A variable already in scope there, or 'Nothing' when the pattern has
  -- to bind it.
  (Text -> Maybe ValExpr) ->
  Term ->
  ResultMatch
aggregateResultMatch payload resolve = go []
  where
    at [] = payload
    at path = List.foldl' (\e i -> GetArg e i) payload path

    go path t = case t of
      Wildcard -> mempty
      VarTerm v -> case resolve v of
        Just e -> test (BEqual e (at path))
        Nothing -> ResultMatch [] [(v, at path)]
      IntTerm n -> test (BEqual (Lit (IntLit n)) (at path))
      FloatTerm f -> test (BEqual (Lit (FloatLit f)) (at path))
      TextTerm s -> test (BEqual (Lit (TextLit s)) (at path))
      CompoundTerm name [] ->
        test (BEqual (Lit (AtomLit (functorAtom name))) (at path))
      CompoundTerm name args ->
        test (BMatchTerm (at path) (vmName name) (fromIntegral (length args)))
          <> mconcat
            [ go (path ++ [i]) arg
            | (i, arg) <- zip [0 ..] args
            ]

    test b = ResultMatch [b] []

-- | The atom a zero-arity constructor has at run time, matching
-- 'YCHR.Internal.Compile.compileTerm'.
functorAtom :: Types.Name -> Text
functorAtom name = (vmName name).unName
