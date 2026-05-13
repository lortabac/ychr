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
--    'D.BodyFunctionCall', 'D.BodyConstraint', or 'D.BodyTrue').
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

import Data.List (mapAccumL)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Effectful (Eff, runPureEff, (:>))
import Effectful.State.Static.Local (State, evalState, get, modify)
import Effectful.Writer.Static.Local (Writer, runWriter, tell)
import YCHR.Desugared qualified as D
import YCHR.Diagnostic (Diagnostic (..), noDiag)
import YCHR.PExpr (PExpr (Atom))
import YCHR.Parsed (AnnP (..), noAnnP)
import YCHR.Parsed qualified as P
import YCHR.Resolved qualified as R
import YCHR.Types

data DesugarError
  = UnexpectedBodyTerm Term
  | InvalidLambdaParam Term
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

-- | Quote a term so it becomes ground: all 'VarTerm' names become
-- 'AtomTerm' values, and 'Wildcard' becomes @AtomTerm "_"@. Used to
-- embed the original lambda source form in the closure term without
-- introducing variable references.
quoteTerm :: Term -> Term
quoteTerm (VarTerm v) = AtomTerm v
quoteTerm Wildcard = AtomTerm "_"
quoteTerm (CompoundTerm n args) = CompoundTerm n (map quoteTerm args)
quoteTerm t = t -- IntTerm, AtomTerm, TextTerm are already ground

-- | The primary entry point: converts a resolved program to a desugared program.
desugarProgram :: R.Program -> Either [Diagnostic DesugarError] D.Program
desugarProgram rprog =
  let funSet = Set.map qualifiedToName rprog.functionNames
      (result, errs) = runPureEff . runWriter $ do
        rules <- traverse (desugarRule funSet) rprog.rules
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
extractSymbolTable :: D.Program -> SymbolTable
extractSymbolTable prog =
  let rules = prog.rules
      allIds =
        Set.fromList
          [ qualifiedNameToIdentifier c.name (length c.args)
          | r <- rules,
            c <- getRuleConstraints r
          ]
   in mkSymbolTable (zip (Set.toList allIds) (map ConstraintType [0 ..]))

-- | Helper to find every constraint instance in a desugared rule.
getRuleConstraints :: D.Rule -> [QualifiedConstraint]
getRuleConstraints r =
  let AnnP {node = rHead} = r.head
      AnnP {node = rBody} = r.body
   in map headConstraintToConstraint rHead.kept
        ++ map headConstraintToConstraint rHead.removed
        ++ [c | D.BodyConstraint c <- rBody]

-- | Desugar one resolved rule: classify its body goals, desugar its user
-- guards, flatten the head kind, and run HNF on the head. HNF-emitted
-- guards are prepended to the user guards so they run first.
desugarRule :: Set Name -> R.Rule -> Eff '[Writer [Diagnostic DesugarError]] D.Rule
desugarRule funSet r = do
  let ruleLabel = fmap (\ann -> "rule " <> ann.node) r.name
  ruleBody <- desugarBodyGoals funSet ruleLabel r.body.sourceLoc r.body.parsed r.body.node
  userGuards <- traverse (desugarGuard r.guard.sourceLoc) r.guard.node
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
                guards = D.GuardEqual (VarTerm v) (VarTerm fresh) : guards
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
            guards = D.GuardEqual (VarTerm fresh) term : guards
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
  let matchGuard = D.GuardMatch (VarTerm parentVar) cname (length cargs)
      st' = HnfState {counter, seen, guards = matchGuard : guards}
   in foldl' (\s (i, arg) -> decomposeArg s parentVar i arg) st' (zip [0 ..] cargs)

-- | Decompose a single argument of a compound term.
decomposeArg :: HnfState -> Text -> Int -> Term -> HnfState
decomposeArg HnfState {counter, seen, guards} parentVar i (VarTerm v)
  | Set.member v seen =
      -- Duplicate variable: extract and check equality
      let fresh = hnfPrefix <> T.pack (show counter)
          getGuard = D.GuardGetArg fresh (VarTerm parentVar) i
          eqGuard = D.GuardEqual (VarTerm v) (VarTerm fresh)
       in HnfState
            { counter = counter + 1,
              seen,
              guards = eqGuard : getGuard : guards
            }
  | otherwise =
      -- First occurrence: extract and bind
      let getGuard = D.GuardGetArg v (VarTerm parentVar) i
       in HnfState
            { counter,
              seen = Set.insert v seen,
              guards = getGuard : guards
            }
decomposeArg st _ _ Wildcard = st
decomposeArg HnfState {counter, seen, guards} parentVar i (CompoundTerm cname cargs) =
  -- Nested compound: extract then recursively decompose
  let fresh = hnfPrefix <> T.pack (show counter)
      getGuard = D.GuardGetArg fresh (VarTerm parentVar) i
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
      getGuard = D.GuardGetArg fresh (VarTerm parentVar) i
      eqGuard = D.GuardEqual (VarTerm fresh) term
   in HnfState
        { counter = counter + 1,
          seen,
          guards = eqGuard : getGuard : guards
        }

-- | Desugar a resolved function definition: HNF-normalize its equation
-- patterns and produce a 'D.Function'.
desugarFunctionDef :: R.FunctionDef -> Eff '[Writer [Diagnostic DesugarError]] D.Function
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
  Eff '[Writer [Diagnostic DesugarError]] D.Equation
desugarResolvedEquation annEq = desugarEquation' annEq.node

desugarEquation' :: R.FunctionEquation -> Eff '[Writer [Diagnostic DesugarError]] D.Equation
desugarEquation' eq = do
  let initState = HnfState 0 Set.empty []
      (st, normalizedArgs) = mapAccumL normalizeArg initState eq.args
      guards = reverse st.guards
  userGuards <- traverse (desugarGuard eq.guard.sourceLoc) eq.guard.node
  pure
    D.Equation
      { params = normalizedArgs,
        guards = guards ++ userGuards,
        rhs = eq.rhs.node
      }

-- | Classify a parsed guard term into a 'D.Guard'.
--
-- Every term is accepted as a 'D.GuardExpr'. Type errors (e.g. a
-- non-boolean guard) are deferred to a future typechecker.
desugarGuard :: P.SourceLoc -> Term -> Eff '[Writer [Diagnostic DesugarError]] D.Guard
desugarGuard _ t = pure $ D.GuardExpr t

-- | Desugar a list of query goal terms into 'BodyGoal's.
-- Returns 'Left' if any desugaring errors occur.
desugarQueryGoals :: Set Name -> [Term] -> Either [Diagnostic DesugarError] [D.BodyGoal]
desugarQueryGoals funSet goals =
  let (results, errs) =
        runPureEff . runWriter $
          desugarBodyGoals funSet Nothing P.dummyLoc (Atom "") goals
   in if null errs then Right results else Left errs

-- ---------------------------------------------------------------------------
-- VarNameSupply: fresh variable generation for desugaring
-- ---------------------------------------------------------------------------

freshVarName :: (State Int :> es) => Eff es Text
freshVarName = do
  n <- get @Int
  modify @Int (+ 1)
  pure (isPrefix <> T.pack (show n))

runVarNameSupply :: Eff (State Int : es) a -> Eff es a
runVarNameSupply = evalState (0 :: Int)

-- | Desugar a list of body terms, flattening any multi-goal expansions
-- (e.g. non-variable @is@ LHS).
desugarBodyGoals ::
  (Writer [Diagnostic DesugarError] :> es) =>
  Set Name ->
  Maybe Text ->
  P.SourceLoc ->
  PExpr ->
  [Term] ->
  Eff es [D.BodyGoal]
desugarBodyGoals funSet label loc origin terms =
  runVarNameSupply $ concat <$> traverse (desugarBodyGoal funSet label loc origin) terms

-- | Classify a parsed body term into 'D.BodyGoal's.
--
-- Pattern priority (order matters):
--
-- 1. @X = Y@ -> 'D.BodyUnify'
-- 2. @X is Expr@ (variable LHS) -> 'D.BodyIs'
-- 3. @T is Expr@ (non-variable LHS) -> @R is Expr, R = T@ with fresh @R@
-- 4. @host:f(…)@ -> 'D.BodyHostStmt'
-- 5. Qualified name in function set -> 'D.BodyFunctionCall'
-- 6. Other qualified name -> 'D.BodyConstraint'
-- 7. @'$call'(F, …)@ -> 'D.BodyFunctionCall' — @$call@ stays
--    'Unqualified' (it is reserved by the renamer), so it would
--    otherwise fall into the unqualified-compound error case below.
-- 8. @true@ -> 'D.BodyTrue'
-- 9. Unqualified compound (renamer should have caught this) -> error
-- 10. Anything else (bare variable, integer, atom, …) -> error
desugarBodyGoal ::
  (State Int :> es, Writer [Diagnostic DesugarError] :> es) =>
  Set Name ->
  Maybe Text ->
  P.SourceLoc ->
  PExpr ->
  Term ->
  Eff es [D.BodyGoal]
desugarBodyGoal funSet label loc origin t = case t of
  CompoundTerm (Unqualified "=") [l, r] -> pure [D.BodyUnify l r]
  CompoundTerm (Unqualified "is") [VarTerm v, expr] ->
    pure [D.BodyIs v expr]
  CompoundTerm (Unqualified "is") [lhs, expr] -> do
    v <- freshVarName
    pure [D.BodyIs v expr, D.BodyUnify (VarTerm v) lhs]
  CompoundTerm (Qualified "host" f) args ->
    pure [D.BodyHostStmt f args]
  -- Canonicalized prelude:true reaching body position is a no-op
  -- (renamer rewrites bare `true` to its qualified form; the body's
  -- "do nothing" sentinel must still resolve to BodyTrue).
  CompoundTerm (Qualified "prelude" "true") [] -> pure [D.BodyTrue]
  CompoundTerm name@(Qualified _ _) args
    | Set.member name funSet ->
        pure [D.BodyFunctionCall name args]
  CompoundTerm (Qualified m b) args ->
    pure [D.BodyConstraint (QualifiedConstraint (QualifiedName m b) args)]
  CompoundTerm (Unqualified "$call") args
    | length args >= 2 ->
        pure [D.BodyFunctionCall (Unqualified "$call") args]
  AtomTerm "true" -> pure [D.BodyTrue]
  CompoundTerm (Unqualified _) _ -> do
    tell [Diagnostic label (AnnP (UnexpectedBodyTerm t) loc origin)]
    pure [D.BodyTrue]
  _ -> do
    tell [Diagnostic label (AnnP (UnexpectedBodyTerm t) loc origin)]
    pure [D.BodyTrue]

-- ---------------------------------------------------------------------------
-- Lambda lifting
-- ---------------------------------------------------------------------------

-- | Threaded state for the lambda-lifter: a counter that supplies fresh
-- @__lambda_N@ names, and the list of top-level functions that have
-- already been lifted out (in reverse discovery order).
data LiftState = LiftState
  { counter :: !Int,
    liftedFunctions :: [D.Function],
    errors :: [Diagnostic DesugarError]
  }

-- | Convert a parsed lambda parameter to a 'HeadArg'. Returns
-- 'Nothing' when the term is neither a variable nor a wildcard;
-- those are reported as 'InvalidLambdaParam'.
termToHeadArg :: Term -> Maybe HeadArg
termToHeadArg (VarTerm v) = Just (HeadVar v)
termToHeadArg Wildcard = Just HeadWildcard
termToHeadArg _ = Nothing

-- | Collect all variable names from a term.
termVars :: Term -> Set.Set Text
termVars (VarTerm v) = Set.singleton v
termVars (CompoundTerm _ args) = Set.unions (map termVars args)
termVars _ = Set.empty

-- | Extract parameters and body from a @fun(X, Y) -> body@ lambda term.
-- Parameters are kept as 'Term' values ('VarTerm' or 'Wildcard').
extractLambdaParams :: Term -> ([Term], Term)
extractLambdaParams
  ( CompoundTerm
      (Unqualified "->")
      [ CompoundTerm (Unqualified "fun") params,
        body
        ]
    ) =
    (params, body)
extractLambdaParams t = ([], t)

-- | Lift lambdas in a single term. Each @fun(...) -> ...@ is replaced
-- by a /self-describing closure/ of the form
-- @__closure(LambdaId, SourceForm, F1, …, Fn)@, where @LambdaId@ is
-- an atom identifying the lifted function, @SourceForm@ is a quoted
-- copy of the original lambda term (for pretty-printing), and
-- @F1 .. Fn@ are the captured free variables; the lambda body itself
-- is lifted into a fresh top-level 'D.Function'. Returns the updated
-- state and the rewritten term.
--
-- The @parentRequiring@ argument is the enclosing bounded
-- declaration's @requiring@ clause (or @[]@ when the lambda's parent
-- is unbounded). Every lifted lambda inherits this clause so that
-- bound-named operations inside the lambda body resolve against the
-- same ambient signatures as in the parent's equation. Nested lambdas
-- inherit recursively.
liftTerm ::
  Text ->
  P.SourceLoc ->
  PExpr ->
  Set.Set Text ->
  [BoundSig] ->
  LiftState ->
  Term ->
  ( LiftState,
    Term
  )
liftTerm modName loc origin scope parentRequiring st term = case term of
  CompoundTerm (Unqualified "->") [CompoundTerm (Unqualified "fun") _, _] ->
    let (params, body) = extractLambdaParams term
        badParams = [p | p <- params, termToHeadArg p == Nothing]
        -- Convert valid params; invalid ones get a 'HeadWildcard'
        -- placeholder so the rest of this branch can still build a
        -- (discarded) function value. The 'InvalidLambdaParam'
        -- diagnostic recorded below causes 'liftAllLambdas' to return
        -- 'Left', so the placeholder is never seen by downstream
        -- passes.
        paramHeadArgs =
          map (\p -> maybe HeadWildcard id (termToHeadArg p)) params
        paramVarNames = Set.fromList [v | HeadVar v <- paramHeadArgs]
        bodyVars = termVars body
        freeVars =
          Set.toAscList
            ( bodyVars
                `Set.intersection` scope
                `Set.difference` paramVarNames
            )
        innerScope = scope `Set.union` paramVarNames
        (st', liftedBody) = liftTerm modName loc origin innerScope parentRequiring st body
        idx = st'.counter
        lambdaName = lambdaPrefix <> T.pack (show idx)
        qualName = QualifiedName modName lambdaName
        allParams = map HeadVar freeVars ++ paramHeadArgs
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
                        rhs = liftedBody
                      }
                  ]
            }
        newErrors = map (\p -> noDiag (AnnP (InvalidLambdaParam p) loc origin)) badParams
        st'' =
          st'
            { counter = idx + 1,
              liftedFunctions = func : st'.liftedFunctions,
              errors = newErrors ++ st'.errors
            }
        lambdaId = modName <> "__" <> lambdaName
        closureArgs = [AtomTerm lambdaId, quoteTerm term] ++ map VarTerm freeVars
     in (st'', CompoundTerm (Unqualified closureFunctor) closureArgs)
  CompoundTerm name args ->
    let (st', args') = mapAccumL (liftTerm modName loc origin scope parentRequiring) st args
     in (st', CompoundTerm name args')
  _ -> (st, term)

-- | Lift lambdas in a body goal.
liftBodyGoal ::
  Text ->
  P.SourceLoc ->
  PExpr ->
  Set.Set Text ->
  [BoundSig] ->
  LiftState ->
  D.BodyGoal ->
  (LiftState, D.BodyGoal)
liftBodyGoal modName loc origin scope parentRequiring st goal = case goal of
  D.BodyIs v expr ->
    let (st', expr') = liftTerm modName loc origin scope parentRequiring st expr
     in (st', D.BodyIs v expr')
  D.BodyFunctionCall name args ->
    let (st', args') = mapAccumL (liftTerm modName loc origin scope parentRequiring) st args
     in (st', D.BodyFunctionCall name args')
  D.BodyConstraint (QualifiedConstraint cname cargs) ->
    let (st', cargs') = mapAccumL (liftTerm modName loc origin scope parentRequiring) st cargs
     in (st', D.BodyConstraint (QualifiedConstraint cname cargs'))
  D.BodyUnify t1 t2 ->
    let (st', t1') = liftTerm modName loc origin scope parentRequiring st t1
        (st'', t2') = liftTerm modName loc origin scope parentRequiring st' t2
     in (st'', D.BodyUnify t1' t2')
  D.BodyHostStmt f args ->
    let (st', args') = mapAccumL (liftTerm modName loc origin scope parentRequiring) st args
     in (st', D.BodyHostStmt f args')
  D.BodyTrue -> (st, D.BodyTrue)

-- | Lift lambdas in a guard.
liftGuard ::
  Text ->
  P.SourceLoc ->
  PExpr ->
  Set.Set Text ->
  [BoundSig] ->
  LiftState ->
  D.Guard ->
  (LiftState, D.Guard)
liftGuard modName loc origin scope parentRequiring st (D.GuardExpr term) =
  let (st', term') = liftTerm modName loc origin scope parentRequiring st term
   in (st', D.GuardExpr term')
liftGuard _ _ _ _ _ st g = (st, g)

-- | Lift lambdas in a function equation. The scope visible to the RHS
-- (and therefore to any lambda captured inside it) includes the pattern
-- parameters /and/ the variables introduced by HNF guards — most
-- importantly 'D.GuardGetArg', which binds the user-written components
-- of a compound pattern like @maplist(F, [X|Xs]) -> ...@.
liftEquation ::
  Text ->
  P.SourceLoc ->
  PExpr ->
  [BoundSig] ->
  LiftState ->
  D.Equation ->
  ( LiftState,
    D.Equation
  )
liftEquation modName loc origin parentRequiring st eq =
  let scope =
        Set.unions (map headArgVars eq.params)
          `Set.union` guardVars eq.guards
      (st', guards') =
        mapAccumL
          (liftGuard modName loc origin scope parentRequiring)
          st
          eq.guards
      (st'', rhs') = liftTerm modName loc origin scope parentRequiring st' eq.rhs
   in (st'', eq {D.guards = guards', D.rhs = rhs'})

-- | Lift lambdas in a function definition. The function's own
-- @requiring@ clause is the @parentRequiring@ propagated to every
-- lambda lifted out of its equations.
liftFunction :: LiftState -> D.Function -> (LiftState, D.Function)
liftFunction st func =
  let modName = func.name.moduleName
      loc = func.equations.sourceLoc
      origin = func.equations.parsed
      (st', eqs') =
        mapAccumL
          (liftEquation modName loc origin func.requiring)
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
    goalVars (D.BodyIs v expr) = Set.insert v (termVars expr)
    goalVars (D.BodyFunctionCall _ args) = Set.unions (map termVars args)
    goalVars (D.BodyConstraint (QualifiedConstraint _ args)) = Set.unions (map termVars args)
    goalVars (D.BodyUnify t1 t2) = termVars t1 `Set.union` termVars t2
    goalVars (D.BodyHostStmt _ args) = Set.unions (map termVars args)
    goalVars D.BodyTrue = Set.empty

-- | Collect all variables from a list of guards.
guardVars :: [D.Guard] -> Set.Set Text
guardVars = Set.unions . map gVars
  where
    gVars (D.GuardExpr t) = termVars t
    gVars (D.GuardEqual t1 t2) = termVars t1 `Set.union` termVars t2
    gVars (D.GuardGetArg v t _) = Set.insert v (termVars t)
    gVars (D.GuardMatch t _ _) = termVars t

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
      guardLoc = rule.guard.sourceLoc
      guardOrigin = rule.guard.parsed
      bodyLoc = rule.body.sourceLoc
      bodyOrigin = rule.body.parsed
      (st', guards') =
        mapAccumL
          (liftGuard modName guardLoc guardOrigin scope [])
          st
          rule.guard.node
      (st'', body') =
        mapAccumL
          (liftBodyGoal modName bodyLoc bodyOrigin scope [])
          st'
          rule.body.node
   in ( st'',
        rule
          { D.guard = rule.guard {node = guards'},
            D.body = rule.body {node = body'}
          }
      )

-- | Post-desugaring pass: lift all lambda expressions into top-level functions.
liftAllLambdas :: D.Program -> Either [Diagnostic DesugarError] D.Program
liftAllLambdas prog =
  let initState = LiftState 0 [] []
      (st1, functions') = mapAccumL liftFunction initState prog.functions
      (st2, rules') = mapAccumL liftRule st1 prog.rules
   in if null st2.errors
        then
          Right
            prog
              { D.functions = functions' ++ st2.liftedFunctions,
                D.rules = rules'
              }
        else Left (reverse st2.errors)

-- | Lift lambdas from query body goals. Returns the rewritten goals
-- and any generated function definitions (to be compiled on the fly).
-- Uses @\"__query\"@ as the module name for lifted lambdas, and starts
-- the counter high enough to avoid collisions with program lambdas.
-- Query lambdas inherit no @requiring@ clause: the top-level goal has
-- no enclosing bounded declaration whose bound could propagate.
liftQueryLambdas ::
  Int ->
  P.SourceLoc ->
  PExpr ->
  [D.BodyGoal] ->
  Either [Diagnostic DesugarError] ([D.BodyGoal], [D.Function])
liftQueryLambdas startCounter loc origin goals =
  let scope = bodyGoalVars goals
      initState = LiftState startCounter [] []
      (st, goals') = mapAccumL (liftBodyGoal "__query" loc origin scope []) initState goals
   in if null st.errors
        then Right (goals', st.liftedFunctions)
        else Left (reverse st.errors)

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

Why 'extractSymbolTable' only scans rules and not functions: the symbol
table is used by the VM for CHR constraint dispatch (array-indexed
activation of rule-head occurrences). Functions are invoked by name
through 'D.BodyFunctionCall', not through the constraint dispatch table,
so they do not need numeric IDs.

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
