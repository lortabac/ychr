{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Internal.Desugar
-- Description : Transforms the resolved AST into the compiler's internal AST.
--
-- The pass between the resolved 'YCHR.Internal.Resolved.Program' and
-- the 'YCHR.Internal.Desugared.Program' the compiler reads. It does,
-- in order:
--
-- 1. /Head-kind flattening/: map the three head kinds
--    ('R.Simplification', 'R.Propagation', 'R.Simpagation') to the
--    uniform @Kept\/Removed@ shape of 'D.Head'.
--
-- 2. /Head Normal Form (HNF)/: in every head constraint, replace
--    non-variable and duplicated-variable arguments with fresh variables,
--    emitting explicit 'D.GuardEqual' / 'D.GuardMatch' / 'D.GuardGetArg'
--    guards.
--
-- 3. /Goal classification/: turn each body expression into
--    'D.BodyGoal' values (see 'desugarBodyGoal').
--
-- 4. /Guard classification/: map each surface guard term to a 'D.Guard'.
--
-- 5. /Function-equation desugaring/: HNF-normalize function-equation
--    patterns and produce 'D.Function' values.
--
-- 6. /Lambda lifting/: replace @fun(...) -> ...@ closures with top-level
--    @__lambda_N@ functions plus closure compound terms carrying the
--    captured free variables.
--
-- Module erasure and equation grouping are handled upstream by the
-- resolve phase ('YCHR.Internal.Resolve').
--
-- 'extractSymbolTable' is a separate utility that numbers every
-- constraint of the desugared program; it is not part of the main
-- pipeline.
--
-- Non-obvious design choices are in the \"Notes\" block at the bottom
-- of this file.
module YCHR.Internal.Desugar
  ( -- * Pipeline
    desugarProgram,
    desugarQueryGoals,

    -- * Lambda lifting
    liftAllLambdas,
    LiftedQuery (..),
    liftQueryLambdas,

    -- * Symbol table
    SymbolTable,
    extractSymbolTable,

    -- * Variable scopes
    bodyGoalVars,
    guardVars,
    ruleScope,

    -- * Rule helpers
    ruleModName,

    -- * Errors
    DesugarError (..),
  )
where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict
  ( State,
    StateT,
    evalStateT,
    get,
    gets,
    modify,
    modify',
    runState,
    runStateT,
    state,
  )
import Control.Monad.Trans.Writer.CPS (Writer, runWriter, tell)
import Data.Foldable (toList)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq, (|>))
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Desugar.AggregateScope (scopeAggregates)
import YCHR.Internal.Desugar.Hnf
  ( Hnf,
    HnfState (..),
    headTermToExpr,
    hnfState,
    normalizeArg,
  )
import YCHR.Internal.Desugar.Vars (exprVars, guardVars, headArgVars, sequenceFree)
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Diagnostic (Diagnostic (..), noDiag)
import YCHR.Internal.PExpr (PExpr (Atom))
import YCHR.Internal.Parsed (AnnP (..), noAnnP)
import YCHR.Internal.Parsed qualified as P
import YCHR.Internal.Resolved qualified as R
import YCHR.Internal.Types
-- Hidden so '.head' resolves under MicroHs (dev-docs/MICROHS_GAPS.md, gap 1).
import Prelude hiding (head)

-- | Errors produced by the desugaring pass.
data DesugarError
  = -- | A rule-body expression did not match any of the recognized
    -- body-goal forms (unification, @is@, host call, user-function
    -- call, dynamic dispatch, constraint tell, @true@). See
    -- 'desugarBodyGoal' for the accepted shapes.
    UnexpectedBodyExpr R.Expr
  | -- | A guard expression that structurally cannot evaluate to a
    -- boolean (e.g. a numeric literal, a non-@true@/@false@ atom, a
    -- data constructor application, a lambda). See 'guardExprIsAllowed'
    -- for the rejection predicate.
    NonBooleanGuard R.Expr
  | -- | A non-final item in a function body sequence was not one of the
    -- allowed shapes (@X is E@, @host:f(args)@, function call, or
    -- @'$call'@).
    NonPreludeFunctionBodyItem R.Expr
  | -- | A non-final @is@ binding had a non-variable LHS, which is not
    -- supported in a function body (function bodies have no unification
    -- machinery).
    NonVariableIsInFunctionBody R.Expr
  | -- | A query used the disjunction operator @;@ at its top level. A
    -- query is not a rule body: there is no enclosing rule to lift a
    -- disjunct out of, and no compiled program to add the lifted
    -- constraint to. The goal-level form works instead
    -- (@solve(quote((A ; B)))@), where the driver reads the @;@ at run
    -- time.
    DisjunctionInQuery
  | -- | An @:- inline@-marked function does not have exactly one
    -- equation. Carries the function's qualified name and the actual
    -- equation count. See 'YCHR.Internal.Desugar.Inline'.
    InlineNotSingleEquation QualifiedName Int
  | -- | An @:- inline@-marked function's single equation carries a
    -- guard — either user-written, or HNF-synthesized because a
    -- parameter is not a plain variable or wildcard. Carries the
    -- function's qualified name.
    InlineGuardedEquation QualifiedName
  | -- | An @:- inline@-marked function's single equation has a
    -- non-empty prelude (statements before its final expression).
    -- Carries the function's qualified name.
    InlineStatefulEquation QualifiedName
  | -- | Two or more @:- inline@-marked functions call each other,
    -- directly or transitively. Carries the flattened names of every
    -- function on the cycle, sorted.
    InlineCycle [Text]
  deriving (Eq, Show)

-- | Prefix for fresh variables introduced when rewriting a non-variable
-- @T is E@ form into @R is E, R = T@ (see 'desugarBodyGoal').
isPrefix :: Text
isPrefix = "__is_"

-- | Prefix for top-level function names produced by the lambda-lifter
-- (see 'liftAllLambdas' and 'liftQueryLambdas').
lambdaPrefix :: Text
lambdaPrefix = "__lambda_"

-- | Functor name for self-describing closure terms.
closureFunctor :: Text
closureFunctor = "__closure"

-- | Quote an expression so it becomes ground: variable references
-- become 0-arity ctor literals; wildcards become @CtorExpr "_" []@.
-- Used to embed the original lambda source form in the closure
-- expression without introducing dangling variable references. The
-- pretty-printer reads the quoted form back out at display time; the
-- form is never evaluated. See the comment at 'sourceForm' in
-- 'liftExpr' for the reason 'LambdaExpr' is flattened here rather
-- than preserved.
quoteExpr :: R.Expr -> R.Expr
quoteExpr (R.VarExpr v) = R.CtorExpr (Unqualified v) []
quoteExpr R.WildcardExpr = R.CtorExpr (Unqualified "_") []
quoteExpr (R.CtorExpr n args) = R.CtorExpr n (map quoteExpr args)
quoteExpr (R.CallExpr qn args) = R.CallExpr qn (map quoteExpr args)
quoteExpr (R.ApplyExpr f args) =
  R.ApplyExpr (quoteExpr f) (map quoteExpr args)
quoteExpr (R.HostExpr f args) = R.HostExpr f (map quoteExpr args)
quoteExpr (R.LambdaExpr params body) =
  R.CtorExpr
    (Unqualified "->")
    [ R.CtorExpr (Unqualified "fun") (map paramAtom (NE.toList params)),
      quoteSequence body
    ]
  where
    paramAtom (HeadVar v) = R.CtorExpr (Unqualified v) []
    paramAtom HeadWildcard = R.CtorExpr (Unqualified "_") []
    quoteSequence = go . NE.toList
      where
        go [e] = quoteExpr e
        go (e : es) =
          R.CtorExpr
            (Unqualified ",")
            [quoteExpr e, go es]
        go [] = R.CtorExpr (Unqualified "true") [] -- unreachable: NonEmpty
quoteExpr e@(R.IntExpr _) = e
quoteExpr e@(R.FloatExpr _) = e
quoteExpr e@(R.TextExpr _) = e
quoteExpr e@(R.FunRefExpr _ _) = e

-- | The primary entry point: converts a resolved program to a desugared program.
desugarProgram :: R.Program -> Either [Diagnostic DesugarError] D.Program
desugarProgram rprog =
  let (result, errs) = runWriter $ do
        rules <- traverse desugarRule rprog.rules
        functions <- traverse desugarFunctionDef rprog.functions
        pure
          D.Program
            { rules = rules,
              functions = functions,
              constraintTypes = rprog.constraintTypes,
              constraintBounds = rprog.constraintBounds,
              constraintUses = rprog.constraintUses,
              nameVisibility = rprog.nameVisibility,
              typeDefinitions = rprog.typeDefinitions
            }
   in if null errs then Right result else Left errs

-- | Number every constraint of a desugared program, from 0.
--
-- Constraint names come from two sources:
--
--   1. Every head constraint and body-tell in every rule (rules are the
--      primary source — they tell us which constraints participate in
--      the ωr activation-dispatch loop).
--   2. Every constraint declared via @:- chr_constraint@ that does not
--      appear in any rule (unreferenced constraints still need a
--      @tell_c@ procedure so the user can tell them at goal time without
--      a raw \"Constraint not found\" error).
extractSymbolTable :: D.Program -> SymbolTable
extractSymbolTable prog =
  let rules = prog.rules
      ruleIds =
        Set.fromList
          [ qualifiedNameToIdentifier key.name key.arity
          | r <- rules,
            key <- getRuleConstraints r
          ]
      -- Declared constraints that no rule mentions still need a tell_c
      -- and an activate_c. See the note at the bottom of this module.
      declaredIds =
        Set.fromList
          [ qualifiedNameToIdentifier key.name key.arity
          | key <- Map.keys prog.constraintTypes
          ]
      allIds = ruleIds `Set.union` declaredIds
   in mkSymbolTable (zip (Set.toList allIds) (map ConstraintType [0 ..]))

-- | Every constraint occurrence in a desugared rule, as its qualified
-- name and arity. Head constraints, body tells
-- and aggregate goals are all included, since all contribute to the
-- constraint-symbol table.
getRuleConstraints :: D.Rule -> [ConstraintKey]
getRuleConstraints r =
  let AnnP {node = rHead} = r.head
      AnnP {node = rBody} = r.body
      headKey hc = ConstraintKey hc.name (length hc.args)
   in map headKey rHead.kept
        ++ map headKey rHead.removed
        ++ concatMap aggKeys rHead.aggregates
        ++ [ConstraintKey qn (length args) | D.BodyTell qn args <- rBody]
  where
    aggKeys a = concatMap conjunctKey a.goal
    conjunctKey (D.AggConstraint hc _) = [ConstraintKey hc.name (length hc.args)]
    conjunctKey (D.AggNested a) = aggKeys a
    conjunctKey (D.AggGuard _) = []

-- | Desugar one resolved rule: classify its body goals, desugar its user
-- guards, flatten the head kind, and run HNF on the head and on every
-- aggregate goal. HNF-emitted head guards are prepended to the user guards
-- so they run first; an aggregate goal's guards stay with the conjunct that
-- emitted them.
desugarRule :: R.Rule -> Writer [Diagnostic DesugarError] D.Rule
desugarRule r = do
  let ruleLabel = fmap (\ann -> "rule " <> ann.node) r.name
  ruleBody <-
    desugarBodyGoals r.moduleName ruleLabel r.body.sourceLoc r.body.parsed r.body.node
  userGuards <- traverse (desugarGuard r.guard.sourceLoc r.guard.parsed) r.guard.node
  (hd, st) <-
    runStateT (desugarHead r.head.sourceLoc r.head.parsed r.head.node) hnfState
  let guards = toList st.guards
      -- What is bound before the first aggregate: the regular heads, and
      -- the variables their HNF guards extract from a compound argument.
      headBound =
        Set.fromList [v | hc <- hd.kept ++ hd.removed, HeadVar v <- hc.args]
          `Set.union` Set.fromList [v | D.GuardGetArg v _ _ <- guards]
      normalizedHead =
        D.Head hd.kept hd.removed (scopeAggregates headBound hd.aggregates)
  pure
    D.Rule
      { name = fmap (.node) r.name,
        head = AnnP normalizedHead r.head.sourceLoc r.head.parsed,
        guard = AnnP (guards ++ userGuards) r.guard.sourceLoc r.guard.parsed,
        body = AnnP ruleBody r.body.sourceLoc r.body.parsed
      }

-- | HNF state over the desugarer's diagnostics.
type HnfW = StateT HnfState (Writer [Diagnostic DesugarError])

-- | Run a pure HNF step in 'HnfW'.
hnf :: Hnf a -> HnfW a
hnf m = state (runState m)

-- | Normalize a head: its kept and removed constraints, then its
-- aggregates, in one HNF state, so a fresh name is unique across the
-- whole rule. Kept is processed before removed so that variables first
-- appearing in kept constraints become the canonical binding (see the
-- note at the bottom of this module). The aggregates are not scoped
-- yet.
desugarHead :: P.SourceLoc -> PExpr -> R.Head -> HnfW D.Head
desugarHead loc origin h = do
  let parts = flattenHeadKind h
  kept' <- hnf (traverse normalizeConstraint parts.kept)
  removed' <- hnf (traverse normalizeConstraint parts.removed)
  aggs <- traverse (desugarAggregate loc origin) parts.aggregates
  pure (D.Head kept' removed' aggs)

-- | Desugar one resolved aggregate. Its expressions are already typed
-- (resolution did that); the guards are classified here, so a non-boolean
-- @?@ conjunct fails at compile time like any other guard, and the goal's
-- constraints are normalized here, so the guards HNF emits for them stay
-- with them.
--
-- The goal starts from an empty @seen@ set even though the counter is
-- shared with the head: a goal's variables are bound by its own loop nest,
-- and which of them are inputs is decided on the occurrence side from the
-- variable map, not here. Reusing the head's set would make a shared
-- variable's first occurrence in the goal look like a duplicate and emit a
-- redundant equality against a fresh name, and a sibling aggregate's local
-- variable would leak into this one's guards. A shared variable reached
-- through a compound argument is recognized the same way: HNF emits a
-- get-arg for it, and the fold's variable map already binds it, so the
-- extraction becomes a test rather than a rebinding.
desugarAggregate :: P.SourceLoc -> PExpr -> R.Aggregate -> HnfW D.Aggregate
desugarAggregate loc origin a = do
  modify' (\st -> st {seen = Set.empty})
  goal' <- desugarConjuncts loc origin a.goal
  pure
    D.Aggregate
      { D.kind = a.kind,
        D.agg = a.agg,
        D.element = a.element,
        D.goal = goal',
        D.result = a.result,
        -- Filled by 'scopeAggregates' once the whole head is desugared.
        D.aggShared = [],
        D.aggLocals = [],
        D.aggBinds = [],
        D.aggResult = Nothing
      }

-- | Desugar one aggregate's goal conjuncts, left to right, in one HNF
-- state, so that a variable repeated across two conjuncts of the same
-- goal is matched by an equality guard.
desugarConjuncts ::
  P.SourceLoc ->
  PExpr ->
  [R.AggregateConjunct] ->
  HnfW [D.AggregateConjunct]
desugarConjuncts loc origin = traverse conjunct
  where
    conjunct c = case c of
      R.AggConstraint qc -> hnf (normalizeGoalConstraint qc)
      -- A nested goal has its own variables: keep the counter it advanced,
      -- but not its @seen@ set, so the conjuncts after it are normalized
      -- against this goal's variables only.
      R.AggNested a -> do
        seen0 <- gets (.seen)
        a' <- desugarAggregate loc origin a
        modify' (\st -> st {seen = seen0})
        pure (D.AggNested a')
      R.AggGuard g -> D.AggGuard <$> lift (desugarGuard loc origin g)

-- | A resolved head, split by role. Propagation rules keep every
-- constraint; simplification rules remove every constraint; simpagation
-- rules carry both lists explicitly.
data HeadParts = HeadParts
  { kept :: [QualifiedConstraint],
    removed :: [QualifiedConstraint],
    aggregates :: [R.Aggregate]
  }

-- | Map the three resolved head kinds to 'HeadParts'.
flattenHeadKind :: R.Head -> HeadParts
flattenHeadKind h = case h of
  R.Simplification rs aggs -> HeadParts [] rs aggs
  R.Propagation ks aggs -> HeadParts ks [] aggs
  R.Simpagation ks rs aggs -> HeadParts ks rs aggs

-- ---------------------------------------------------------------------------
-- Head Normal Form (HNF)
-- ---------------------------------------------------------------------------

-- In every head constraint, replace non-variable and duplicated-variable
-- arguments with fresh variables and emit explicit 'D.GuardEqual',
-- 'D.GuardMatch', and 'D.GuardGetArg' guards that recover the original
-- meaning. The core of it lives in "YCHR.Internal.Desugar.Hnf".

-- | Normalize one constraint conjunct of an aggregate goal, with that
-- conjunct's own guards in emission order.
--
-- The guards are taken back out of the shared accumulator, so they stay
-- with the conjunct they came from: they are evaluated inside the loop that
-- matches that conjunct, not in the rule's guard beside the head's own HNF
-- guards.
normalizeGoalConstraint :: QualifiedConstraint -> Hnf D.AggregateConjunct
normalizeGoalConstraint qc = do
  saved <- gets (.guards)
  modify' (\st -> st {guards = Seq.empty})
  hc <- normalizeConstraint qc
  own <- gets (\st -> toList st.guards)
  modify' (\st -> st {guards = saved})
  pure (D.AggConstraint hc own)

-- | Normalize the arguments of one head constraint, narrowing them
-- from raw 'Term's to 'HeadArg's.
normalizeConstraint :: QualifiedConstraint -> Hnf HeadConstraint
normalizeConstraint (QualifiedConstraint cname cargs) =
  HeadConstraint cname <$> traverse normalizeArg cargs

-- | Desugar a resolved function definition: HNF-normalize its equation
-- patterns and produce a 'D.Function'.
desugarFunctionDef :: R.FunctionDef -> Writer [Diagnostic DesugarError] D.Function
desugarFunctionDef fdef = do
  desugaredEqs <- traverse desugarResolvedEquation fdef.equations
  pure
    D.Function
      { name = fdef.name,
        arity = fdef.arity,
        signatures = fdef.signatures,
        requiring = fdef.requiring,
        refining = fdef.refining,
        lambdaArity = Nothing,
        inline = fdef.inline,
        equations = desugaredEqs
      }

desugarResolvedEquation ::
  AnnP R.FunctionEquation ->
  Writer [Diagnostic DesugarError] (AnnP D.Equation)
desugarResolvedEquation annEq = do
  eq <- desugarEquation' annEq.node
  pure (AnnP eq annEq.sourceLoc annEq.parsed)

desugarEquation' :: R.FunctionEquation -> Writer [Diagnostic DesugarError] D.Equation
desugarEquation' eq = do
  let (normalizedArgs, st) = runState (traverse normalizeArg eq.args) hnfState
      guards = toList st.guards
  userGuards <- traverse (desugarGuard eq.guard.sourceLoc eq.guard.parsed) eq.guard.node
  prelude <- classifyFunctionPrelude eq.rhs.sourceLoc eq.rhs.parsed eq.rhs.node
  pure
    D.Equation
      { params = normalizedArgs,
        guards = guards ++ userGuards,
        prelude = prelude,
        rhs = NE.last eq.rhs.node
      }

-- | Classify the non-final items of a function-body sequence, the
-- prelude before its return expression. Each must be one of
-- @host:f(args)@, @X is E@ (variable LHS), a function call, or
-- @'$call'(F, args)@; anything else is reported as 'NonPreludeFunctionBodyItem'.
-- A non-variable @is@ LHS in non-final position is reported as
-- 'NonVariableIsInFunctionBody'. The return expression is left as-is.
classifyFunctionPrelude ::
  P.SourceLoc ->
  PExpr ->
  NE.NonEmpty R.Expr ->
  Writer [Diagnostic DesugarError] [D.FunStmt]
classifyFunctionPrelude loc origin body =
  traverse (classifyFunStmt loc origin) (NE.init body)

-- | Classify a single non-final function-body expression into a 'D.FunStmt'.
-- Emits a diagnostic and returns a no-op placeholder when the shape is
-- not one of the allowed forms; the placeholder is unreachable because
-- compilation aborts whenever any diagnostic is emitted.
classifyFunStmt ::
  P.SourceLoc ->
  PExpr ->
  R.Expr ->
  Writer [Diagnostic DesugarError] D.FunStmt
classifyFunStmt loc origin e = case e of
  R.HostExpr f args -> pure (D.FunHostStmt f args)
  R.CtorExpr (Unqualified "is") [R.VarExpr v, expr] -> pure (D.FunIs v expr)
  R.CtorExpr (Unqualified "is") [_, _] -> do
    tell [Diagnostic Nothing (AnnP (NonVariableIsInFunctionBody e) loc origin) []]
    pure (D.FunHostStmt "" [])
  R.CallExpr qn args -> pure (D.FunCall qn args)
  R.ApplyExpr f args -> pure (D.FunApply f args)
  _ -> do
    tell [Diagnostic Nothing (AnnP (NonPreludeFunctionBodyItem e) loc origin) []]
    pure (D.FunHostStmt "" [])

-- | Classify a resolved guard expression into a 'D.Guard'.
--
-- Expressions that structurally cannot evaluate to a boolean
-- (non-boolean literals, data constructor applications other than
-- @prelude:true@/@prelude:false@, function references, lambdas,
-- wildcards) are rejected with 'NonBooleanGuard'. This catches
-- categorical bugs like writing @=@ (a data constructor application)
-- or a numeric literal in guard position at desugar time, independent
-- of whether the optional typechecker runs.
desugarGuard ::
  P.SourceLoc ->
  PExpr ->
  R.Expr ->
  Writer [Diagnostic DesugarError] D.Guard
desugarGuard loc origin e
  | guardExprIsAllowed e = pure (D.GuardExpr e)
  | otherwise = do
      tell [Diagnostic Nothing (AnnP (NonBooleanGuard e) loc origin) []]
      pure (D.GuardExpr e)

-- | Predicate: can this expression plausibly evaluate to a boolean?
-- Variables, calls, dynamic dispatch, host calls, the bare atoms
-- @true@/@false@, and the canonicalized @prelude:true@/@prelude:false@
-- constructors are accepted. Every other atom is rejected: an
-- unqualified atom that is neither @true@ nor @false@ cannot possibly
-- evaluate to a boolean.
guardExprIsAllowed :: R.Expr -> Bool
guardExprIsAllowed e = case e of
  R.VarExpr {} -> True
  R.CtorExpr (Unqualified "true") [] -> True
  R.CtorExpr (Unqualified "false") [] -> True
  R.CallExpr {} -> True
  R.ApplyExpr {} -> True
  R.HostExpr {} -> True
  R.CtorExpr (Qualified "prelude" "true") [] -> True
  R.CtorExpr (Qualified "prelude" "false") [] -> True
  _ -> False

-- | The scope a query goal's dynamic @tell\/N@ carries: the name of the
-- pseudo-module the renamer resolves query goals in
-- ("YCHR.Internal.Rename"'s @buildQueryRenameEnv@). The query runner
-- resolves such a tell against every module's exports, which is that
-- pseudo-module's visibility, so it does not consult the scope.
queryScope :: Text
queryScope = "<query>"

-- | Desugar a list of query goal expressions into 'BodyGoal's.
-- Returns 'Left' if any desugaring errors occur.
desugarQueryGoals :: [R.Expr] -> Either [Diagnostic DesugarError] [D.BodyGoal]
desugarQueryGoals goals =
  let (results, errs) =
        runWriter $
          desugarBodyGoals queryScope Nothing P.dummyLoc (Atom "") goals
      -- A query has no enclosing rule to lift a disjunct out of, and
      -- the program it runs against is already compiled, so there is
      -- nowhere to put the lifted constraint either. Rejected here
      -- rather than in the renamer so the goal-level @;@ inside
      -- @quote/1@, which the search driver reads at run time, keeps
      -- working.
      disjErrs =
        [ noDiag (AnnP DisjunctionInQuery P.dummyLoc (Atom ""))
        | any isDisjunction results
        ]
      allErrs = errs ++ disjErrs
   in if null allErrs then Right results else Left allErrs
  where
    isDisjunction (D.BodyOr _) = True
    isDisjunction _ = False

-- ---------------------------------------------------------------------------
-- Fresh @__is_N@ names for body desugaring
-- ---------------------------------------------------------------------------

-- | A fresh @__is_N@ variable name.
freshVarName :: StateT Int (Writer [Diagnostic DesugarError]) Text
freshVarName = do
  n <- get
  modify (+ 1)
  pure (isPrefix <> T.pack (show n))

runVarNameSupply ::
  StateT Int (Writer [Diagnostic DesugarError]) a ->
  Writer [Diagnostic DesugarError] a
runVarNameSupply m = evalStateT m 0

-- | Desugar a list of body expressions, flattening any multi-goal
-- expansions (e.g. non-variable @is@ LHS).
desugarBodyGoals ::
  Text ->
  Maybe Text ->
  P.SourceLoc ->
  PExpr ->
  [R.Expr] ->
  Writer [Diagnostic DesugarError] [D.BodyGoal]
desugarBodyGoals scope label loc origin exprs =
  runVarNameSupply $ concat <$> traverse (desugarBodyGoal scope label loc origin) exprs

-- | Classify a resolved body expression into 'D.BodyGoal's.
--
-- Patterns, tried in this order (order matters):
--
-- 1. @X = Y@ -> 'D.BodyUnify'
-- 2. @X is Expr@ (variable LHS) -> 'D.BodyIs'
-- 3. @T is Expr@ (non-variable LHS) -> @R is Expr, R = T@ with fresh @R@
-- 4. 'R.HostExpr' -> 'D.BodyHostStmt'
-- 5. @true@ in either spelling -> 'D.BodyTrue'
-- 6. 'R.CallExpr' -> 'D.BodyCall'
-- 7. 'R.ApplyExpr' -> 'D.BodyApply'
-- 8. @tell(G, …)@ -> 'D.BodyTellDynamic'
-- 9. @A ; B@ -> 'D.BodyOr'
-- 10. Constructor with a 'Qualified' name -> 'D.BodyTell'
-- 11. Anything else -> error
desugarBodyGoal ::
  Text ->
  Maybe Text ->
  P.SourceLoc ->
  PExpr ->
  R.Expr ->
  StateT Int (Writer [Diagnostic DesugarError]) [D.BodyGoal]
desugarBodyGoal scope label loc origin e = case e of
  -- Surface '=' arrives as CtorExpr "=" from the resolver.
  R.CtorExpr (Unqualified "=") [l, r] -> pure [D.BodyUnify l r]
  -- 'is' with a variable LHS.
  R.CtorExpr (Unqualified "is") [R.VarExpr v, expr] ->
    pure [D.BodyIs v expr]
  -- 'is' with a non-variable LHS: introduce a fresh value, then unify.
  R.CtorExpr (Unqualified "is") [lhs, expr] -> do
    v <- freshVarName
    pure [D.BodyIs v expr, D.BodyUnify (R.VarExpr v) lhs]
  R.HostExpr f args -> pure [D.BodyHostStmt f args]
  R.CtorExpr (Qualified "prelude" "true") [] -> pure [D.BodyTrue]
  R.CtorExpr (Unqualified "true") [] -> pure [D.BodyTrue]
  R.CallExpr qn args -> pure [D.BodyCall qn args]
  R.ApplyExpr f args -> pure [D.BodyApply f args]
  -- A dynamic @tell\/N@. The renamer has already rejected a bare @tell@
  -- and one wider than 'R.maxTellArity', and rewritten every literal
  -- goal into the plain tell it denotes.
  R.CtorExpr (Unqualified "tell") (g : extras) ->
    pure [D.BodyTellDynamic scope g extras]
  -- Disjunction. The parser nests @;@ to the right, so the branches of
  -- @(a ; b ; c)@ are read off the right spine; a left-nested
  -- @((a ; b) ; c)@ keeps its left operand as one branch, which is
  -- itself a disjunction and nests. Each branch is a body conjunction,
  -- so its own top-level commas are flattened the same way the rule
  -- body's were.
  R.CtorExpr (Unqualified ";") [_, _] -> do
    branches <-
      traverse
        (fmap concat . traverse (desugarBodyGoal scope label loc origin) . conjuncts)
        (disjuncts e)
    pure [D.BodyOr (NE.fromList branches)]
  R.CtorExpr (Qualified m b) args ->
    pure [D.BodyTell (QualifiedName m b) args]
  _ -> do
    lift (tell [Diagnostic label (AnnP (UnexpectedBodyExpr e) loc origin) []])
    pure [D.BodyTrue]

-- | The branches of a disjunction, read off the right spine. Always at
-- least two, because the caller has already matched a @;@ compound.
disjuncts :: R.Expr -> [R.Expr]
disjuncts (R.CtorExpr (Unqualified ";") [l, r]) = l : disjuncts r
disjuncts e = [e]

-- | The goals of one body conjunction. @,@ at the top of a disjunct is
-- the same sequencer it is at the top of a rule body, which the parser
-- has already flattened there.
conjuncts :: R.Expr -> [R.Expr]
conjuncts (R.CtorExpr (Unqualified ",") [l, r]) = conjuncts l ++ conjuncts r
conjuncts e = [e]

-- ---------------------------------------------------------------------------
-- Lambda lifting
-- ---------------------------------------------------------------------------

-- | State of the lambda-lifter: a counter that supplies fresh
-- @__lambda_N@ names, the top-level functions that have already been
-- lifted out (in discovery order), and an error accumulator for
-- lambda-body classification failures discovered during the lift.
-- Errors here mirror the diagnostics 'desugarEquation'' emits for the
-- top-level RHS sequence of an equation.
--
-- 'liftedFunctions' is a 'Seq' for the same reason 'HnfState.guards'
-- is: appending keeps it in discovery order, so 'D.Program.functions'
-- lists lifted lambdas in that order. Nothing downstream depends on it
-- (lifted functions are looked up by name); it only shows in the order
-- procedures are emitted.
data LiftState = LiftState
  { counter :: !Int,
    liftedFunctions :: Seq D.Function,
    liftErrors :: [Diagnostic DesugarError]
  }

-- | The lambda-lifter's monad.
type Lift = State LiftState

-- | Lift lambdas in a single expression. Each 'R.LambdaExpr' is
-- replaced by a /self-describing closure/ of the form
-- @__closure(LambdaId, SourceForm, F1, …, Fn)@: @LambdaId@ is an atom
-- identifying the lifted function, @SourceForm@ is a quoted copy of
-- the original lambda (for pretty-printing), and @F1 .. Fn@ are the
-- captured free variables. The lambda body itself is lifted into a
-- fresh top-level 'D.Function'.
--
-- Lifted lambdas carry no @requiring@ clause. The type checker runs
-- on the pre-lift program, where the lambda body is checked in place
-- under the enclosing equation's context — including the ambient
-- signatures its @requiring@ clause contributes — so inheriting the
-- parent's clause here would be dead data (and the checker's
-- untyped-function path ignores it anyway).
liftExpr :: Text -> Set.Set Text -> R.Expr -> Lift R.Expr
liftExpr modName scope expr = case expr of
  R.LambdaExpr params body -> do
    let paramsList = NE.toList params
        paramVarNames = Set.fromList [v | HeadVar v <- paramsList]
        bodyList = NE.toList body
        -- Walk the body left-to-right so that a name bound by an
        -- earlier 'X is E' shadows later uses of X but does NOT
        -- shadow uses in the same item's RHS or in items that
        -- precede the binding. The latter still capture the outer
        -- value, which 'fun(X) -> N is N + 1, N end' relies on:
        -- the inner 'N' on the RHS of 'is' is the captured outer N.
        bodyFree = sequenceFree bodyList
        freeVars =
          Set.toAscList
            ( bodyFree
                `Set.intersection` scope
                `Set.difference` paramVarNames
            )
        -- The inner scope is a superset; locally-bound names are
        -- added so nested lambdas can find them, on top of params
        -- and any names bound by prelude 'is' statements.
        innerScope =
          scope
            `Set.union` paramVarNames
            `Set.union` Set.fromList
              [v | R.CtorExpr (Unqualified "is") [R.VarExpr v, _] <- bodyList]
    -- The body is lifted first, so a nested lambda gets a lower number.
    liftedBody <- NE.fromList <$> traverse (liftExpr modName innerScope) bodyList
    idx <- gets (.counter)
    let (prelude, classifyErrs) =
          runWriter (classifyFunctionPrelude P.dummyLoc (Atom "") liftedBody)
        lambdaName = lambdaPrefix <> T.pack (show idx)
        qualName = QualifiedName modName lambdaName
        allParams = map HeadVar freeVars ++ paramsList
        func =
          D.Function
            { name = qualName,
              arity = length allParams,
              signatures = [],
              requiring = [],
              refining = Nothing,
              lambdaArity = Just (length paramsList),
              inline = False,
              equations =
                [ noAnnP
                    D.Equation
                      { params = allParams,
                        guards = [],
                        prelude = prelude,
                        rhs = NE.last liftedBody
                      }
                ]
            }
        lambdaId = modName <> "__" <> lambdaName
        -- The quoted source form is for pretty-printing only and must
        -- stay opaque: it contains the lambda body with all its
        -- function-named subterms (@'+'@, @'*'@, user functions, …)
        -- still spelled out, and 'compileExpr' would otherwise
        -- eagerly evaluate them at closure-construction time. Wrap
        -- in @quote/1@ so 'compileExpr' short-circuits via
        -- 'compileTerm' on the 'R.exprToTerm' of the quoted subtree.
        --
        -- 'quoteExpr' also rewrites 'R.LambdaExpr' into a surface
        -- @->@/@fun@ 'CtorExpr' with atomised parameter names.
        -- Keeping a real 'LambdaExpr' here would leave its parameter
        -- variables as 'HeadVar's; 'R.exprToTerm' would turn each
        -- into a 'VarTerm', and 'compileTerm' would then look it up
        -- in the enclosing rule's varMap (where it does not exist)
        -- and raise 'UnboundVariable'. Atomising the parameters
        -- breaks that lookup chain.
        sourceForm =
          R.CtorExpr (Unqualified "quote") [quoteExpr expr]
        closureArgs =
          R.CtorExpr (Unqualified lambdaId) [] : sourceForm : map R.VarExpr freeVars
    modify' $ \st ->
      st
        { counter = idx + 1,
          liftedFunctions = st.liftedFunctions |> func,
          liftErrors = st.liftErrors ++ classifyErrs
        }
    pure (R.CtorExpr (Unqualified closureFunctor) closureArgs)
  R.CtorExpr name args -> R.CtorExpr name <$> traverse go args
  R.CallExpr qn args -> R.CallExpr qn <$> traverse go args
  R.ApplyExpr f args -> R.ApplyExpr <$> go f <*> traverse go args
  R.HostExpr f args -> R.HostExpr f <$> traverse go args
  _ -> pure expr
  where
    go = liftExpr modName scope

-- | Lift lambdas in a body goal. Every body goal carries 'Expr'-typed
-- children, so 'liftExpr' walks them uniformly.
liftBodyGoal :: Text -> Set.Set Text -> D.BodyGoal -> Lift D.BodyGoal
liftBodyGoal modName scope goal = case goal of
  D.BodyIs v expr -> D.BodyIs v <$> go expr
  D.BodyCall qn args -> D.BodyCall qn <$> traverse go args
  D.BodyApply f args -> D.BodyApply <$> go f <*> traverse go args
  D.BodyTellDynamic m g extras ->
    D.BodyTellDynamic m <$> go g <*> traverse go extras
  D.BodyTell qn args -> D.BodyTell qn <$> traverse go args
  D.BodyUnify t1 t2 -> D.BodyUnify <$> go t1 <*> go t2
  D.BodyHostStmt f args -> D.BodyHostStmt f <$> traverse go args
  -- Every branch is lifted in the same scope: a disjunct sees exactly
  -- the variables the enclosing rule body sees.
  D.BodyOr branches ->
    D.BodyOr <$> traverse (traverse (liftBodyGoal modName scope)) branches
  D.BodyTrue -> pure D.BodyTrue
  where
    go = liftExpr modName scope

-- | Lift lambdas in a guard. 'GuardExpr' and 'GuardEqual' carry
-- user-written expressions that can contain a lambda
-- (@X == fun(Y) -> Y end@ is unusual but legal), so both arms walk
-- their operands with 'liftExpr'. 'GuardMatch' and 'GuardGetArg' are
-- HNF-synthetic: their operands are always 'R.VarExpr', so a walk
-- would be a no-op and we leave them untouched.
liftGuard :: Text -> Set.Set Text -> D.Guard -> Lift D.Guard
liftGuard modName scope guard_ = case guard_ of
  D.GuardExpr e -> D.GuardExpr <$> go e
  D.GuardEqual e1 e2 -> D.GuardEqual <$> go e1 <*> go e2
  _ -> pure guard_
  where
    go = liftExpr modName scope

-- | Lift lambdas in a function equation. The scope visible to the RHS
-- (and therefore to any lambda captured inside it) includes the pattern
-- parameters /and/ the variables introduced by HNF guards — most
-- importantly 'D.GuardGetArg', which binds the user-written components
-- of a compound pattern like @maplist(F, [X|Xs]) -> ...@.
liftEquation :: Text -> D.Equation -> Lift D.Equation
liftEquation modName eq = do
  let scope =
        Set.unions (map headArgVars eq.params)
          `Set.union` guardVars eq.guards
          `Set.union` funStmtBindings eq.prelude
  guards' <- traverse (liftGuard modName scope) eq.guards
  prelude' <- traverse (liftFunStmt modName scope) eq.prelude
  rhs' <- liftExpr modName scope eq.rhs
  pure eq {D.guards = guards', D.prelude = prelude', D.rhs = rhs'}

-- | Lift lambdas in a function-body prelude statement.
liftFunStmt :: Text -> Set.Set Text -> D.FunStmt -> Lift D.FunStmt
liftFunStmt modName scope stmt = case stmt of
  D.FunIs v expr -> D.FunIs v <$> go expr
  D.FunHostStmt f args -> D.FunHostStmt f <$> traverse go args
  D.FunCall qn args -> D.FunCall qn <$> traverse go args
  D.FunApply f args -> D.FunApply <$> go f <*> traverse go args
  where
    go = liftExpr modName scope

-- | Variables bound by a list of function-body prelude statements (only
-- 'FunIs' contributes a binding).
funStmtBindings :: [D.FunStmt] -> Set.Set Text
funStmtBindings = Set.fromList . concatMap binds
  where
    binds (D.FunIs v _) = [v]
    binds _ = []

-- | Lift lambdas in a function definition. Each equation keeps its own
-- source location and parsed origin.
liftFunction :: D.Function -> Lift D.Function
liftFunction func = do
  eqs' <- traverse (traverse (liftEquation func.name.moduleName)) func.equations
  pure func {D.equations = eqs'}

-- | Extract all variables from a rule head (kept + removed constraints).
ruleHeadVars :: D.Head -> Set.Set Text
ruleHeadVars h =
  Set.unions
    [ headArgVars arg
    | c <- h.kept ++ h.removed,
      arg <- c.args
    ]

-- | Every variable a rule mentions: head, guard, and body. A lambda or a
-- disjunct lifted out of the rule may capture only these.
ruleScope :: D.Rule -> Set.Set Text
ruleScope rule =
  ruleHeadVars rule.head.node
    `Set.union` guardVars rule.guard.node
    `Set.union` bodyGoalVars rule.body.node

-- | Extract the module name from a rule's head constraints. The
-- qualification invariant is enforced by 'QualifiedConstraint'; the
-- only way this can fail is an empty head, which the parser does not
-- produce for well-formed rules.
ruleModName :: D.Head -> Text
ruleModName h = case h.kept ++ h.removed of
  (c : _) -> c.name.moduleName
  [] -> error "Desugar.ruleModName: empty rule head"

-- | Collect all variables from a list of body goals.
bodyGoalVars :: [D.BodyGoal] -> Set.Set Text
bodyGoalVars = Set.unions . map goalVars
  where
    goalVars (D.BodyIs v expr) = Set.insert v (exprVars expr)
    goalVars (D.BodyCall _ args) = Set.unions (map exprVars args)
    goalVars (D.BodyApply f args) =
      exprVars f `Set.union` Set.unions (map exprVars args)
    goalVars (D.BodyTellDynamic _ g extras) =
      exprVars g `Set.union` Set.unions (map exprVars extras)
    goalVars (D.BodyTell _ args) = Set.unions (map exprVars args)
    goalVars (D.BodyUnify e1 e2) = exprVars e1 `Set.union` exprVars e2
    goalVars (D.BodyHostStmt _ args) = Set.unions (map exprVars args)
    goalVars (D.BodyOr branches) =
      Set.unions (map bodyGoalVars (NE.toList branches))
    goalVars D.BodyTrue = Set.empty

-- | Lift lambdas in a rule. The scope includes all variables from the
-- entire rule (head, guard, and body).
--
-- The aggregates are lifted last, so their lambdas are numbered after
-- the guard's and the body's.
liftRule :: D.Rule -> Lift D.Rule
liftRule rule = do
  let headAnn = rule.head
      headNode = headAnn.node
      guardAnn = rule.guard
      bodyAnn = rule.body
      scope = ruleScope rule
      modName = ruleModName headNode
  guards' <- traverse (liftGuard modName scope) guardAnn.node
  body' <- traverse (liftBodyGoal modName scope) bodyAnn.node
  aggs' <- traverse (liftAggregate modName scope) headNode.aggregates
  pure
    rule
      { D.head = headAnn {node = headNode {D.aggregates = aggs'}},
        D.guard = guardAnn {node = guards'},
        D.body = bodyAnn {node = body'}
      }

-- | Lift lambdas in one aggregate. Its three expression positions see
-- different scopes:
--
--   * @agg@ is evaluated once, before the fold's loops, so a lambda in it
--     may capture only what the rule's own scope holds. A capture of one of
--     the aggregate's goal variables is not in that scope, so the name is
--     left out of the closure and compiling the lifted body reports it as
--     unbound — the right diagnostic for a value the closure cannot have.
--
--   * @element@ and the goal's @?@ guards are evaluated inside those loops,
--     so a lambda in them may capture the goal's own variables: the closure
--     is built there, and the lifter turns each capture into a leading
--     parameter.
liftAggregate :: Text -> Set.Set Text -> D.Aggregate -> Lift D.Aggregate
liftAggregate modName outerScope a = do
  let innerScope = outerScope `Set.union` aggregateGoalVars a
  -- @agg@ is 'Nothing' for a selection form.
  agg' <- traverse (liftExpr modName outerScope) a.agg
  element' <- liftExpr modName innerScope a.element
  goal' <- traverse (liftConjunct modName innerScope) a.goal
  pure a {D.agg = agg', D.element = element', D.goal = goal'}

-- | Lift lambdas in one aggregate-goal conjunct: the conjunct's own HNF
-- guards, a @?@ guard's expression, or a nested aggregate, which shares the
-- enclosing goal's scope.
liftConjunct :: Text -> Set.Set Text -> D.AggregateConjunct -> Lift D.AggregateConjunct
liftConjunct modName scope c = case c of
  D.AggConstraint hc guards ->
    D.AggConstraint hc <$> traverse (liftGuard modName scope) guards
  D.AggNested a -> D.AggNested <$> liftAggregate modName scope a
  D.AggGuard g -> D.AggGuard <$> liftGuard modName scope g

-- | Variables an aggregate's goal makes available inside its loops: the
-- arguments of its constraint conjuncts, the fresh variables their HNF
-- guards introduce, the variables a @?@ guard mentions, and — for a nested
-- aggregate — the variables its result pattern is matched against.
--
-- The aggregate's own @result@ is deliberately absent: it is matched after
-- the fold, outside the loops an element or a goal guard is evaluated in.
aggregateGoalVars :: D.Aggregate -> Set.Set Text
aggregateGoalVars a = Set.unions (map conjunctVars a.goal)
  where
    conjunctVars (D.AggConstraint hc guards) =
      Set.unions (map headArgVars hc.args) `Set.union` guardVars guards
    conjunctVars (D.AggGuard g) = guardVars [g]
    conjunctVars (D.AggNested n) =
      aggregateGoalVars n `Set.union` exprVars (headTermToExpr n.result)

-- | Post-desugaring pass: lift all lambda expressions into top-level
-- functions. Fails with the diagnostics produced while classifying
-- lambda body sequences (see 'classifyFunStmt').
liftAllLambdas :: D.Program -> Either [Diagnostic DesugarError] D.Program
liftAllLambdas prog = case st.liftErrors of
  [] -> Right lifted {D.functions = lifted.functions ++ toList st.liftedFunctions}
  errs -> Left errs
  where
    (lifted, st) = runState liftParts (LiftState 0 Seq.empty [])
    liftParts = do
      functions' <- traverse liftFunction prog.functions
      rules' <- traverse liftRule prog.rules
      pure prog {D.functions = functions', D.rules = rules'}

-- | Query goals after lambda lifting, and the functions lifted out of
-- them.
data LiftedQuery = LiftedQuery
  { goals :: [D.BodyGoal],
    lambdas :: [D.Function]
  }

-- | Lift lambdas from query body goals. Returns the rewritten goals
-- and any generated function definitions (to be compiled on the fly).
-- Uses @\"__query\"@ as the module name for lifted lambdas, and starts
-- the counter high enough to avoid collisions with program lambdas.
-- Like all lifted lambdas, query lambdas carry no @requiring@ clause.
liftQueryLambdas ::
  Int ->
  [D.BodyGoal] ->
  Either [Diagnostic DesugarError] LiftedQuery
liftQueryLambdas startCounter goals = case st.liftErrors of
  [] -> Right LiftedQuery {goals = goals', lambdas = toList st.liftedFunctions}
  errs -> Left errs
  where
    scope = bodyGoalVars goals
    (goals', st) =
      runState
        (traverse (liftBodyGoal "__query" scope) goals)
        (LiftState startCounter Seq.empty [])

{- ---------------------------------------------------------------------------
Notes
-----------------------------------------------------------------------------

Why HNF processes 'kept' constraints before 'removed' ones: variables
that appear for the first time in a kept constraint become the canonical
binding for that name. A variable that then recurs in a removed
constraint is renamed to a fresh @$hnf_N@ and equated to the canonical
one via a 'D.GuardEqual'. Reversing the order would work just as well
mathematically but would mean the canonical binding "moves" whenever a
rule is rewritten from simpagation to simplification/propagation, which
the paper's scheme avoids.

Why there are four different fresh-variable prefixes:

  * @$hnf_N@   — HNF-introduced variables for duplicated or non-variable
                head arguments ("YCHR.Internal.Desugar.Hnf").
  * @$res_N@   — the same for an aggregate's result pattern
                ("YCHR.Internal.Desugar.AggregateScope"), with its own
                counter.
  * @__is_N@   — fresh LHS variables for the non-variable @is@ form
                (@T is E@ becomes @R is E, R = T@). Double-underscore so
                they cannot collide with the HNF prefix or with any
                user-written name.
  * @__lambda_N@ — names of top-level functions created by the
                lambda-lifter. Double-underscore again to stay clear of
                user names.

Each prefix is owned by a different phase and they cannot collide with
each other or with user variables.

Why 'extractSymbolTable' scans both rules and constraintTypes: the symbol
table assigns a numeric ID to every CHR constraint type so the VM can
dispatch activations by array index. Rule heads provide the primary
source (they determine which constraints participate in the &omega;r
activation-dispatch loop). Functions are invoked by name through
'D.BodyCall', not through the constraint dispatch table, so they
do not need numeric IDs. Constraints declared via ':- chr_constraint'
that never appear in any rule are also included from the
'prog.constraintTypes' map; without a symbol-table entry the compiler
generates no 'tell_c' procedure for them and the user gets a raw
"Constraint not found" error at goal time.

Why 'liftQueryLambdas' uses @\"__query\"@ as the module name: query
goals don't belong to any user module, but lifted lambdas still need a
'Qualified' name. @__query@ is a synthetic qualifier that cannot clash
with a real module (module names in the surface language don't start
with an underscore). The caller ('Run.runProgramWithQuery') passes
a @startCounter@ greater than the number of program lambdas so query
@__lambda_N@ indices do not overlap with ones already baked into the
compiled program.

Why 'liftEquation's scope includes 'guardVars': HNF may decompose a
compound pattern like @[X|Xs]@ into a 'D.GuardGetArg' that binds @X@ and
@Xs@. Those names are not visible from @eq.params@ (which only
contains the top-level @$hnf_N@), but they are valid references from
the RHS — including from inside a lambda. The lambda-lifter therefore
has to see them too, otherwise the lambda would be lifted without
capturing them and the reference would dangle at runtime. Test:
@"Desugar.lambda-lift.lambda captures HNF-bound pattern variable"@.
--------------------------------------------------------------------------- -}
