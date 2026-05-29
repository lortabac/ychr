{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Desugar
-- Description : Transforms the resolved AST into the compiler's internal AST.
--
-- The Desugarer is the transformation pass between the resolved
-- 'YCHR.Resolved.Program' and the internal 'YCHR.Desugared.Program'
-- consumed by the compiler. It performs, in order:
--
-- 1. /Head-kind flattening/: map the three surface head kinds
--    ('P.Simplification', 'P.Propagation', 'P.Simpagation') to the
--    uniform @Kept\/Removed@ shape of 'D.Head'.
--
-- 2. /Head Normal Form (HNF)/: in every head constraint, replace
--    non-variable and duplicated-variable arguments with fresh variables,
--    emitting explicit 'D.GuardEqual' / 'D.GuardMatch' / 'D.GuardGetArg'
--    guards.
--
-- 3. /Goal classification/: partition each body into structured 'D.BodyGoal'
--    values ('D.BodyUnify', 'D.BodyIs', 'D.BodyHostStmt',
--    'D.BodyCall', 'D.BodyTell', or 'D.BodyTrue').
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
-- resolve phase ('YCHR.Resolve').
--
-- 'extractSymbolTable' is a separate utility that assigns sequential IDs
-- to every 'Qualified' rule-head constraint in the desugared program; it
-- is not part of the main pipeline.
--
-- Non-obvious design choices are documented in the \"Notes\" block at the
-- bottom of this file.
module YCHR.Desugar
  ( -- * Pipeline
    desugarProgram,
    desugarQueryGoals,

    -- * Lambda lifting
    liftAllLambdas,
    liftQueryLambdas,

    -- * Symbol table
    SymbolTable,
    extractSymbolTable,

    -- * Errors
    DesugarError (..),
  )
where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, modify)
import Control.Monad.Trans.Writer.CPS (Writer, runWriter, tell)
import Data.List (mapAccumL)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Desugared qualified as D
import YCHR.Diagnostic (Diagnostic (..))
import YCHR.PExpr (PExpr (Atom))
import YCHR.Parsed (AnnP (..), noAnnP)
import YCHR.Parsed qualified as P
import YCHR.Resolved qualified as R
import YCHR.Types

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
  deriving (Eq, Show)

-- | Prefix for fresh variables introduced by the Head Normal Form
-- transformation (see 'normalizeHead').
hnfPrefix :: Text
hnfPrefix = "_hnf_"

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

-- | Convert a head-position 'Term' (always a pattern: variable, wildcard,
-- literal, or constructor compound) to its 'R.Expr' equivalent. HNF
-- emits guards whose operands are these patterns, so the conversion is
-- exhaustive over the pattern grammar.
headTermToExpr :: Term -> R.Expr
headTermToExpr (VarTerm v) = R.VarExpr v
headTermToExpr Wildcard = R.WildcardExpr
headTermToExpr (IntTerm n) = R.IntExpr n
headTermToExpr (FloatTerm n) = R.FloatExpr n
headTermToExpr (TextTerm s) = R.TextExpr s
headTermToExpr (CompoundTerm n args) =
  R.CtorExpr n (map headTermToExpr args)

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
              typeDefinitions = rprog.typeDefinitions
            }
   in if null errs then Right result else Left errs

-- | Scans a desugared program and builds the optimization map.
-- It ensures that all qualified names get a sequential ID starting from 0.
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
          [ qualifiedNameToIdentifier name arity
          | r <- rules,
            (name, arity) <- getRuleConstraints r
          ]
      -- Constraints declared via :- chr_constraint that never appear in
      -- any rule still need a tell_c and activate_c procedure. Without
      -- a symbol-table entry the compiler skips them entirely and the
      -- user hits a raw "user error (Constraint not found)" at goal time.
      declaredIds =
        Set.fromList
          [ qualifiedNameToIdentifier qn (length types)
          | (qn, types) <- Map.toList prog.constraintTypes
          ]
      allIds = ruleIds `Set.union` declaredIds
   in mkSymbolTable (zip (Set.toList allIds) (map ConstraintType [0 ..]))

-- | Helper to find every constraint instance in a desugared rule,
-- returning its qualified name and arity. Head and body tells are both
-- included, since both contribute to the constraint-symbol table.
getRuleConstraints :: D.Rule -> [(QualifiedName, Int)]
getRuleConstraints r =
  let AnnP {node = rHead} = r.head
      AnnP {node = rBody} = r.body
      headPair hc = (hc.name, length hc.args)
   in map headPair rHead.kept
        ++ map headPair rHead.removed
        ++ [(qn, length args) | D.BodyTell qn args <- rBody]

-- | Desugar one resolved rule: classify its body goals, desugar its user
-- guards, flatten the head kind, and run HNF on the head. HNF-emitted
-- guards are prepended to the user guards so they run first.
desugarRule :: R.Rule -> Writer [Diagnostic DesugarError] D.Rule
desugarRule r = do
  let ruleLabel = fmap (\ann -> "rule " <> ann.node) r.name
  ruleBody <- desugarBodyGoals ruleLabel r.body.sourceLoc r.body.parsed r.body.node
  userGuards <- traverse (desugarGuard r.guard.sourceLoc r.guard.parsed) r.guard.node
  let (rawKept, rawRemoved) = flattenHeadKind r.head.node
      (guards, normalizedHead) = normalizeHead rawKept rawRemoved
  pure
    D.Rule
      { name = fmap (.node) r.name,
        head = AnnP normalizedHead r.head.sourceLoc r.head.parsed,
        guard = AnnP (guards ++ userGuards) r.guard.sourceLoc r.guard.parsed,
        body = AnnP ruleBody r.body.sourceLoc r.body.parsed
      }

-- | Map the three resolved head kinds to a uniform @(kept, removed)@
-- pair of raw 'QualifiedConstraint' lists. Propagation rules keep every
-- constraint; simplification rules remove every constraint; simpagation
-- rules carry both lists explicitly. The result is fed to
-- 'normalizeHead', which produces the 'D.Head' with HNF-narrowed
-- 'HeadConstraint' arguments.
flattenHeadKind :: R.Head -> ([QualifiedConstraint], [QualifiedConstraint])
flattenHeadKind h = case h of
  R.Simplification rs -> ([], rs)
  R.Propagation ks -> (ks, [])
  R.Simpagation ks rs -> (ks, rs)

-- ---------------------------------------------------------------------------
-- Head Normal Form (HNF)
-- ---------------------------------------------------------------------------

-- | In every head constraint, replace non-variable and duplicated-variable
-- arguments with fresh variables and emit explicit 'D.GuardEqual',
-- 'D.GuardMatch', and 'D.GuardGetArg' guards that recover the original
-- semantics.

-- | Threaded state for HNF: a fresh-variable counter, the set of
-- variable names already seen in the head so far (so that duplicates
-- can be detected), and the list of guards accumulated in reverse order.
data HnfState = HnfState
  { counter :: !Int,
    seen :: Set.Set Text,
    guards :: [D.Guard] -- accumulated in reverse
  }

-- | Normalize the kept and removed constraints of a head. Kept is
-- processed before removed so that variables first appearing in kept
-- constraints become the canonical binding (see the note at the bottom
-- of this module).
normalizeHead :: [QualifiedConstraint] -> [QualifiedConstraint] -> ([D.Guard], D.Head)
normalizeHead kept removed =
  let initState = HnfState 0 Set.empty []
      (st1, kept') = mapAccumL normalizeConstraint initState kept
      (st2, removed') = mapAccumL normalizeConstraint st1 removed
   in (reverse st2.guards, D.Head kept' removed')

-- | Normalize the arguments of one head constraint, narrowing them
-- from raw 'Term's to 'HeadArg's.
normalizeConstraint :: HnfState -> QualifiedConstraint -> (HnfState, HeadConstraint)
normalizeConstraint st (QualifiedConstraint cname cargs) =
  let (st', args') = mapAccumL normalizeArg st cargs
   in (st', HeadConstraint cname args')

-- | Normalize one argument of a head constraint. Fresh variables are
-- only introduced for duplicates and non-variables; first-use variables
-- and wildcards pass through.
normalizeArg :: HnfState -> Term -> (HnfState, HeadArg)
normalizeArg HnfState {counter, seen, guards} (VarTerm v)
  | Set.member v seen =
      let fresh = hnfPrefix <> T.pack (show counter)
       in ( HnfState
              { counter = counter + 1,
                seen,
                guards = D.GuardEqual (R.VarExpr v) (R.VarExpr fresh) : guards
              },
            HeadVar fresh
          )
  | otherwise =
      ( HnfState {counter, seen = Set.insert v seen, guards},
        HeadVar v
      )
-- Wildcards pass through unchanged: they match anything, are never referenced,
-- and cannot duplicate, so no fresh variable or guard is needed.
normalizeArg st Wildcard = (st, HeadWildcard)
normalizeArg HnfState {counter, seen, guards} (CompoundTerm cname cargs) =
  let fresh = hnfPrefix <> T.pack (show counter)
      st' = HnfState {counter = counter + 1, seen, guards}
      st'' = decomposeCompound st' fresh cname cargs
   in (st'', HeadVar fresh)
normalizeArg HnfState {counter, seen, guards} term =
  let fresh = hnfPrefix <> T.pack (show counter)
   in ( HnfState
          { counter = counter + 1,
            seen,
            guards = D.GuardEqual (R.VarExpr fresh) (headTermToExpr term) : guards
          },
        HeadVar fresh
      )

-- | Decompose a compound term into match and extraction guards. Both
-- 'Qualified' and 'Unqualified' constructor functors are handled
-- uniformly: the renamer canonicalizes data constructors to their
-- 'Qualified' form, and the compiler emits both as a single flat-atom
-- compound (see 'YCHR.Compile.compileTerm') — so HNF can just emit one
-- 'GuardMatch' per compound regardless of where the name originated.
decomposeCompound :: HnfState -> Text -> Name -> [Term] -> HnfState
decomposeCompound HnfState {counter, seen, guards} parentVar cname cargs =
  let matchGuard = D.GuardMatch (R.VarExpr parentVar) cname (length cargs)
      st' = HnfState {counter, seen, guards = matchGuard : guards}
   in foldl' (\s (i, arg) -> decomposeArg s parentVar i arg) st' (zip [0 ..] cargs)

-- | Decompose a single argument of a compound term.
decomposeArg :: HnfState -> Text -> Int -> Term -> HnfState
decomposeArg HnfState {counter, seen, guards} parentVar i (VarTerm v)
  | Set.member v seen =
      -- Duplicate variable: extract and check equality
      let fresh = hnfPrefix <> T.pack (show counter)
          getGuard = D.GuardGetArg fresh (R.VarExpr parentVar) i
          eqGuard = D.GuardEqual (R.VarExpr v) (R.VarExpr fresh)
       in HnfState
            { counter = counter + 1,
              seen,
              guards = eqGuard : getGuard : guards
            }
  | otherwise =
      -- First occurrence: extract and bind
      let getGuard = D.GuardGetArg v (R.VarExpr parentVar) i
       in HnfState
            { counter,
              seen = Set.insert v seen,
              guards = getGuard : guards
            }
decomposeArg st _ _ Wildcard = st
decomposeArg HnfState {counter, seen, guards} parentVar i (CompoundTerm cname cargs) =
  -- Nested compound: extract then recursively decompose
  let fresh = hnfPrefix <> T.pack (show counter)
      getGuard = D.GuardGetArg fresh (R.VarExpr parentVar) i
      st' =
        HnfState
          { counter = counter + 1,
            seen,
            guards = getGuard : guards
          }
   in decomposeCompound st' fresh cname cargs
decomposeArg HnfState {counter, seen, guards} parentVar i term =
  -- Ground term (atom, integer, string): extract and check equality
  let fresh = hnfPrefix <> T.pack (show counter)
      getGuard = D.GuardGetArg fresh (R.VarExpr parentVar) i
      eqGuard = D.GuardEqual (R.VarExpr fresh) (headTermToExpr term)
   in HnfState
        { counter = counter + 1,
          seen,
          guards = eqGuard : getGuard : guards
        }

-- | Desugar a resolved function definition: HNF-normalize its equation
-- patterns and produce a 'D.Function'.
desugarFunctionDef :: R.FunctionDef -> Writer [Diagnostic DesugarError] D.Function
desugarFunctionDef fdef = do
  desugaredEqs <- traverse desugarResolvedEquation fdef.equations
  let (loc, parsed) = case fdef.equations of
        (AnnP _eq eqLoc eqParsed : _) -> (eqLoc, eqParsed)
        [] -> (P.dummyLoc, Atom "function")
  pure
    D.Function
      { name = fdef.name,
        arity = fdef.arity,
        signatures = fdef.signatures,
        requiring = fdef.requiring,
        equations = AnnP desugaredEqs loc parsed
      }

desugarResolvedEquation ::
  AnnP R.FunctionEquation ->
  Writer [Diagnostic DesugarError] D.Equation
desugarResolvedEquation annEq = desugarEquation' annEq.node

desugarEquation' :: R.FunctionEquation -> Writer [Diagnostic DesugarError] D.Equation
desugarEquation' eq = do
  let initState = HnfState 0 Set.empty []
      (st, normalizedArgs) = mapAccumL normalizeArg initState eq.args
      guards = reverse st.guards
  userGuards <- traverse (desugarGuard eq.guard.sourceLoc eq.guard.parsed) eq.guard.node
  (prelude, returnExpr) <-
    classifyFunctionBody eq.rhs.sourceLoc eq.rhs.parsed eq.rhs.node
  pure
    D.Equation
      { params = normalizedArgs,
        guards = guards ++ userGuards,
        prelude = prelude,
        rhs = returnExpr
      }

-- | Split a function-body sequence into its non-final prelude items
-- and the trailing return expression. Each non-final item must be one
-- of @host:f(args)@, @X is E@ (variable LHS), a function call, or
-- @'$call'(F, args)@; anything else is reported as 'NonPreludeFunctionBodyItem'.
-- A non-variable @is@ LHS in non-final position is reported as
-- 'NonVariableIsInFunctionBody'. The return expression is left as-is.
classifyFunctionBody ::
  P.SourceLoc ->
  PExpr ->
  NE.NonEmpty R.Expr ->
  Writer [Diagnostic DesugarError] ([D.FunStmt], R.Expr)
classifyFunctionBody loc origin body = do
  let (initExprs, lastExpr) = (NE.init body, NE.last body)
  stmts <- traverse (classifyFunStmt loc origin) initExprs
  pure (stmts, lastExpr)

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
    tell [Diagnostic Nothing (AnnP (NonVariableIsInFunctionBody e) loc origin)]
    pure (D.FunHostStmt "" [])
  R.CallExpr qn args -> pure (D.FunCall qn args)
  R.ApplyExpr f args -> pure (D.FunApply f args)
  _ -> do
    tell [Diagnostic Nothing (AnnP (NonPreludeFunctionBodyItem e) loc origin)]
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
      tell [Diagnostic Nothing (AnnP (NonBooleanGuard e) loc origin)]
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

-- | Desugar a list of query goal expressions into 'BodyGoal's.
-- Returns 'Left' if any desugaring errors occur.
desugarQueryGoals :: [R.Expr] -> Either [Diagnostic DesugarError] [D.BodyGoal]
desugarQueryGoals goals =
  let (results, errs) =
        runWriter $
          desugarBodyGoals Nothing P.dummyLoc (Atom "") goals
   in if null errs then Right results else Left errs

-- ---------------------------------------------------------------------------
-- VarNameSupply: fresh variable generation for desugaring
-- ---------------------------------------------------------------------------

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
  Maybe Text ->
  P.SourceLoc ->
  PExpr ->
  [R.Expr] ->
  Writer [Diagnostic DesugarError] [D.BodyGoal]
desugarBodyGoals label loc origin exprs =
  runVarNameSupply $ concat <$> traverse (desugarBodyGoal label loc origin) exprs

-- | Classify a resolved body expression into 'D.BodyGoal's.
--
-- Pattern priority (order matters):
--
-- 1. @X = Y@ -> 'D.BodyUnify'
-- 2. @X is Expr@ (variable LHS) -> 'D.BodyIs'
-- 3. @T is Expr@ (non-variable LHS) -> @R is Expr, R = T@ with fresh @R@
-- 4. 'R.HostExpr' -> 'D.BodyHostStmt'
-- 5. 'R.CallExpr' -> 'D.BodyCall'
-- 6. 'R.ApplyExpr' -> 'D.BodyApply'
-- 7. Constructor with a 'Qualified' name -> 'D.BodyTell'
-- 8. @true@ in any spelling -> 'D.BodyTrue'
-- 9. Anything else -> error
desugarBodyGoal ::
  Maybe Text ->
  P.SourceLoc ->
  PExpr ->
  R.Expr ->
  StateT Int (Writer [Diagnostic DesugarError]) [D.BodyGoal]
desugarBodyGoal label loc origin e = case e of
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
  R.CtorExpr (Qualified m b) args ->
    pure [D.BodyTell (QualifiedName m b) args]
  _ -> do
    lift (tell [Diagnostic label (AnnP (UnexpectedBodyExpr e) loc origin)])
    pure [D.BodyTrue]

-- ---------------------------------------------------------------------------
-- Lambda lifting
-- ---------------------------------------------------------------------------

-- | Threaded state for the lambda-lifter: a counter that supplies fresh
-- @__lambda_N@ names, the list of top-level functions that have already
-- been lifted out (in reverse discovery order), and an error accumulator
-- for lambda-body classification failures discovered during the lift.
-- Errors here mirror the diagnostics 'desugarEquation'' emits for the
-- top-level RHS sequence of an equation.
data LiftState = LiftState
  { counter :: !Int,
    liftedFunctions :: [D.Function],
    liftErrors :: [Diagnostic DesugarError]
  }

-- | Collect all variable names referenced inside an expression.
exprVars :: R.Expr -> Set.Set Text
exprVars (R.VarExpr v) = Set.singleton v
exprVars (R.CtorExpr _ args) = Set.unions (map exprVars args)
exprVars (R.CallExpr _ args) = Set.unions (map exprVars args)
exprVars (R.ApplyExpr f args) =
  exprVars f `Set.union` Set.unions (map exprVars args)
exprVars (R.HostExpr _ args) = Set.unions (map exprVars args)
exprVars (R.LambdaExpr params body) =
  sequenceFree (NE.toList body)
    `Set.difference` Set.fromList [v | HeadVar v <- NE.toList params]
exprVars (R.FunRefExpr _ _) = Set.empty
exprVars (R.IntExpr _) = Set.empty
exprVars (R.FloatExpr _) = Set.empty
exprVars (R.TextExpr _) = Set.empty
exprVars R.WildcardExpr = Set.empty

-- | Free variables of a sequenced expression list (lambda body or
-- top-level function body), treating an @X is E@ item as a binder for
-- X: uses of X /before/ the binding (and uses of X in @E@ itself, which
-- is evaluated /before/ the binding takes effect) still count, while
-- uses in /later/ items resolve to the local binding and do not escape.
sequenceFree :: [R.Expr] -> Set.Set Text
sequenceFree = go Set.empty
  where
    go _ [] = Set.empty
    go bound (e : es) =
      let usedHere = case e of
            R.CtorExpr (Unqualified "is") [R.VarExpr _, rhs] -> exprVars rhs
            _ -> exprVars e
          contrib = usedHere `Set.difference` bound
          bound' = case e of
            R.CtorExpr (Unqualified "is") [R.VarExpr v, _] ->
              Set.insert v bound
            _ -> bound
       in contrib `Set.union` go bound' es

-- | Lift lambdas in a single expression. Each 'R.LambdaExpr' is
-- replaced by a /self-describing closure/ of the form
-- @__closure(LambdaId, SourceForm, F1, …, Fn)@: @LambdaId@ is an atom
-- identifying the lifted function, @SourceForm@ is a quoted copy of
-- the original lambda (for pretty-printing), and @F1 .. Fn@ are the
-- captured free variables. The lambda body itself is lifted into a
-- fresh top-level 'D.Function'. Returns the updated state and the
-- rewritten expression.
--
-- @parentRequiring@ is the enclosing bounded declaration's
-- @requiring@ clause (or @[]@ when the lambda's parent is unbounded).
-- Every lifted lambda inherits this clause so that bound-named
-- operations inside the lambda body resolve against the same ambient
-- signatures as in the parent's equation. Nested lambdas inherit
-- recursively.
liftExpr ::
  Text ->
  Set.Set Text ->
  [BoundSig] ->
  LiftState ->
  R.Expr ->
  (LiftState, R.Expr)
liftExpr modName scope parentRequiring st0 expr = case expr of
  R.LambdaExpr params body ->
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
        (st1, liftedBody) =
          mapAccumL
            (liftExpr modName innerScope parentRequiring)
            st0
            bodyList
        liftedBodyNE = NE.fromList liftedBody
        (preludeExprs, rhsExpr) =
          (NE.init liftedBodyNE, NE.last liftedBodyNE)
        (prelude, classifyErrs) =
          runWriter $
            traverse
              (classifyFunStmt P.dummyLoc (Atom ""))
              preludeExprs
        st1' = st1 {liftErrors = st1.liftErrors ++ classifyErrs}
        idx = st1'.counter
        lambdaName = lambdaPrefix <> T.pack (show idx)
        qualName = QualifiedName modName lambdaName
        allParams = map HeadVar freeVars ++ paramsList
        func =
          D.Function
            { name = qualName,
              arity = length allParams,
              signatures = [],
              requiring = parentRequiring,
              equations =
                noAnnP
                  [ D.Equation
                      { params = allParams,
                        guards = [],
                        prelude = prelude,
                        rhs = rhsExpr
                      }
                  ]
            }
        st2 =
          st1'
            { counter = idx + 1,
              liftedFunctions = func : st1'.liftedFunctions
            }
        lambdaId = modName <> "__" <> lambdaName
        -- The quoted source form is for pretty-printing only and must
        -- stay opaque: it contains the lambda body with all its
        -- function-named subterms (@'+'@, @'*'@, user functions, …)
        -- still spelled out, and 'compileExpr' would otherwise
        -- eagerly evaluate them at closure-construction time. Wrap
        -- in @term/1@ so 'compileExpr' short-circuits via
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
          R.CtorExpr (Unqualified "term") [quoteExpr expr]
        closureArgs =
          R.CtorExpr (Unqualified lambdaId) [] : sourceForm : map R.VarExpr freeVars
     in (st2, R.CtorExpr (Unqualified closureFunctor) closureArgs)
  R.CtorExpr name args ->
    let (st1, args') =
          mapAccumL (liftExpr modName scope parentRequiring) st0 args
     in (st1, R.CtorExpr name args')
  R.CallExpr qn args ->
    let (st1, args') =
          mapAccumL (liftExpr modName scope parentRequiring) st0 args
     in (st1, R.CallExpr qn args')
  R.ApplyExpr f args ->
    let (st1, f') = liftExpr modName scope parentRequiring st0 f
        (st2, args') =
          mapAccumL (liftExpr modName scope parentRequiring) st1 args
     in (st2, R.ApplyExpr f' args')
  R.HostExpr f args ->
    let (st1, args') =
          mapAccumL (liftExpr modName scope parentRequiring) st0 args
     in (st1, R.HostExpr f args')
  _ -> (st0, expr)

-- | Lift lambdas in a body goal. Every body goal carries 'Expr'-typed
-- children, so 'liftExpr' walks them uniformly.
liftBodyGoal ::
  Text ->
  Set.Set Text ->
  [BoundSig] ->
  LiftState ->
  D.BodyGoal ->
  (LiftState, D.BodyGoal)
liftBodyGoal modName scope parentRequiring st goal = case goal of
  D.BodyIs v expr ->
    let (st', expr') = liftExpr modName scope parentRequiring st expr
     in (st', D.BodyIs v expr')
  D.BodyCall qn args ->
    let (st', args') =
          mapAccumL (liftExpr modName scope parentRequiring) st args
     in (st', D.BodyCall qn args')
  D.BodyApply f args ->
    let (st', f') = liftExpr modName scope parentRequiring st f
        (st'', args') =
          mapAccumL (liftExpr modName scope parentRequiring) st' args
     in (st'', D.BodyApply f' args')
  D.BodyTell qn args ->
    let (st', args') =
          mapAccumL (liftExpr modName scope parentRequiring) st args
     in (st', D.BodyTell qn args')
  D.BodyUnify t1 t2 ->
    let (st', t1') = liftExpr modName scope parentRequiring st t1
        (st'', t2') = liftExpr modName scope parentRequiring st' t2
     in (st'', D.BodyUnify t1' t2')
  D.BodyHostStmt f args ->
    let (st', args') =
          mapAccumL (liftExpr modName scope parentRequiring) st args
     in (st', D.BodyHostStmt f args')
  D.BodyTrue -> (st, D.BodyTrue)

-- | Lift lambdas in a guard. 'GuardExpr' and 'GuardEqual' carry
-- user-written expressions that can contain a lambda
-- (@X == fun(Y) -> Y end@ is unusual but legal), so both arms walk
-- their operands with 'liftExpr'. 'GuardMatch' and 'GuardGetArg' are
-- HNF-synthetic: their operands are always 'R.VarExpr', so a walk
-- would be a no-op and we leave them untouched.
liftGuard ::
  Text ->
  Set.Set Text ->
  [BoundSig] ->
  LiftState ->
  D.Guard ->
  (LiftState, D.Guard)
liftGuard modName scope parentRequiring st guard_ = case guard_ of
  D.GuardExpr e ->
    let (st', e') = liftExpr modName scope parentRequiring st e
     in (st', D.GuardExpr e')
  D.GuardEqual e1 e2 ->
    let (st', e1') = liftExpr modName scope parentRequiring st e1
        (st'', e2') = liftExpr modName scope parentRequiring st' e2
     in (st'', D.GuardEqual e1' e2')
  _ -> (st, guard_)

-- | Lift lambdas in a function equation. The scope visible to the RHS
-- (and therefore to any lambda captured inside it) includes the pattern
-- parameters /and/ the variables introduced by HNF guards — most
-- importantly 'D.GuardGetArg', which binds the user-written components
-- of a compound pattern like @maplist(F, [X|Xs]) -> ...@.
liftEquation ::
  Text ->
  [BoundSig] ->
  LiftState ->
  D.Equation ->
  (LiftState, D.Equation)
liftEquation modName parentRequiring st eq =
  let scope =
        Set.unions (map headArgVars eq.params)
          `Set.union` guardVars eq.guards
          `Set.union` funStmtBindings eq.prelude
      (st', guards') =
        mapAccumL (liftGuard modName scope parentRequiring) st eq.guards
      (st'', prelude') =
        mapAccumL (liftFunStmt modName scope parentRequiring) st' eq.prelude
      (st''', rhs') = liftExpr modName scope parentRequiring st'' eq.rhs
   in (st''', eq {D.guards = guards', D.prelude = prelude', D.rhs = rhs'})

-- | Lift lambdas in a function-body prelude statement.
liftFunStmt ::
  Text ->
  Set.Set Text ->
  [BoundSig] ->
  LiftState ->
  D.FunStmt ->
  (LiftState, D.FunStmt)
liftFunStmt modName scope parentRequiring st stmt = case stmt of
  D.FunIs v expr ->
    let (st', expr') = liftExpr modName scope parentRequiring st expr
     in (st', D.FunIs v expr')
  D.FunHostStmt f args ->
    let (st', args') =
          mapAccumL (liftExpr modName scope parentRequiring) st args
     in (st', D.FunHostStmt f args')
  D.FunCall qn args ->
    let (st', args') =
          mapAccumL (liftExpr modName scope parentRequiring) st args
     in (st', D.FunCall qn args')
  D.FunApply f args ->
    let (st', f') = liftExpr modName scope parentRequiring st f
        (st'', args') =
          mapAccumL (liftExpr modName scope parentRequiring) st' args
     in (st'', D.FunApply f' args')

-- | Variables bound by a list of function-body prelude statements (only
-- 'FunIs' contributes a binding).
funStmtBindings :: [D.FunStmt] -> Set.Set Text
funStmtBindings = Set.fromList . concatMap binds
  where
    binds (D.FunIs v _) = [v]
    binds _ = []

-- | Lift lambdas in a function definition. The function's own
-- @requiring@ clause is the @parentRequiring@ propagated to every
-- lambda lifted out of its equations.
liftFunction :: LiftState -> D.Function -> (LiftState, D.Function)
liftFunction st func =
  let modName = func.name.moduleName
      (st', eqs') =
        mapAccumL
          (liftEquation modName func.requiring)
          st
          func.equations.node
   in (st', func {D.equations = func.equations {node = eqs'}})

-- | Variables introduced by a single 'HeadArg'. Wildcards contribute
-- nothing.
headArgVars :: HeadArg -> Set.Set Text
headArgVars (HeadVar v) = Set.singleton v
headArgVars HeadWildcard = Set.empty

-- | Extract all variables from a rule head (kept + removed constraints).
ruleHeadVars :: D.Head -> Set.Set Text
ruleHeadVars h =
  Set.unions
    [ headArgVars arg
    | c <- h.kept ++ h.removed,
      arg <- c.args
    ]

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
    goalVars (D.BodyTell _ args) = Set.unions (map exprVars args)
    goalVars (D.BodyUnify e1 e2) = exprVars e1 `Set.union` exprVars e2
    goalVars (D.BodyHostStmt _ args) = Set.unions (map exprVars args)
    goalVars D.BodyTrue = Set.empty

-- | Collect all variables from a list of guards.
guardVars :: [D.Guard] -> Set.Set Text
guardVars = Set.unions . map gVars
  where
    gVars (D.GuardExpr e) = exprVars e
    gVars (D.GuardEqual e1 e2) = exprVars e1 `Set.union` exprVars e2
    gVars (D.GuardGetArg v e _) = Set.insert v (exprVars e)
    gVars (D.GuardMatch e _ _) = exprVars e

-- | Lift lambdas in a rule. The scope includes all variables from the
-- entire rule (head, guard, and body). Rules use an empty
-- @parentRequiring@: bounded constraints contribute ambient signatures
-- at type-check time through the head-occurrence mechanism, not by
-- pushing bounds onto lifted lambdas (lambdas in rule bodies that need
-- bound-named operations remain rare in practice).
liftRule :: LiftState -> D.Rule -> (LiftState, D.Rule)
liftRule st rule =
  let headNode = rule.head.node
      scope =
        ruleHeadVars headNode
          `Set.union` guardVars rule.guard.node
          `Set.union` bodyGoalVars rule.body.node
      modName = ruleModName headNode
      (st', guards') =
        mapAccumL (liftGuard modName scope []) st rule.guard.node
      (st'', body') =
        mapAccumL (liftBodyGoal modName scope []) st' rule.body.node
   in ( st'',
        rule
          { D.guard = rule.guard {node = guards'},
            D.body = rule.body {node = body'}
          }
      )

-- | Post-desugaring pass: lift all lambda expressions into top-level
-- functions. Returns any diagnostics produced while classifying lambda
-- body sequences (see 'classifyFunStmt'). Callers must merge these
-- with the rest of the pipeline's errors.
liftAllLambdas :: D.Program -> (D.Program, [Diagnostic DesugarError])
liftAllLambdas prog =
  let initState = LiftState 0 [] []
      (st1, functions') = mapAccumL liftFunction initState prog.functions
      (st2, rules') = mapAccumL liftRule st1 prog.rules
   in ( prog
          { D.functions = functions' ++ st2.liftedFunctions,
            D.rules = rules'
          },
        st2.liftErrors
      )

-- | Lift lambdas from query body goals. Returns the rewritten goals
-- and any generated function definitions (to be compiled on the fly).
-- Uses @\"__query\"@ as the module name for lifted lambdas, and starts
-- the counter high enough to avoid collisions with program lambdas.
-- Query lambdas inherit no @requiring@ clause: the top-level goal has
-- no enclosing bounded declaration whose bound could propagate.
liftQueryLambdas ::
  Int ->
  [D.BodyGoal] ->
  ([D.BodyGoal], [D.Function], [Diagnostic DesugarError])
liftQueryLambdas startCounter goals =
  let scope = bodyGoalVars goals
      initState = LiftState startCounter [] []
      (st, goals') =
        mapAccumL (liftBodyGoal "__query" scope []) initState goals
   in (goals', st.liftedFunctions, st.liftErrors)

{- ---------------------------------------------------------------------------
Notes
-----------------------------------------------------------------------------

Why HNF processes 'kept' constraints before 'removed' ones: variables
that appear for the first time in a kept constraint become the canonical
binding for that name. A variable that then recurs in a removed
constraint is renamed to a fresh @_hnf_N@ and equated to the canonical
one via a 'D.GuardEqual'. Reversing the order would work just as well
mathematically but would mean the canonical binding "moves" whenever a
rule is rewritten from simpagation to simplification/propagation, which
the paper's scheme avoids.

Why there are three different fresh-variable prefixes:

  * @_hnf_N@   — HNF-introduced variables for duplicated or non-variable
                head arguments ('normalizeHead', 'decomposeCompound').
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
'D.BodyFunctionCall', not through the constraint dispatch table, so they
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
@Xs@. Those names are no longer visible from @eq.params@ (which only
contains the top-level @_hnf_N@), but they are valid references from
the RHS — including from inside a lambda. The lambda-lifter therefore
has to see them too, otherwise the lambda would be lifted without
capturing them and the reference would dangle at runtime. Test:
@"Desugar.lambda-lift.lambda captures HNF-bound pattern variable"@.
--------------------------------------------------------------------------- -}
