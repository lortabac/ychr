{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Desugar
-- Description : Erases module boundaries and flattens CHR rules into an internal AST.
--
-- The Desugarer is the final transformation pass before code generation. Its
-- responsibilities include:
--
-- 1. Module Erasure: Flattens a collection of 'YCHR.Parsed.Module' objects into
--    a single 'YCHR.Desugared.Program'.
-- 2. Goal Classification: Uses the 'Name' sum-type (populated by the Renamer)
--    to partition rule bodies into CHR Constraints, Host Statements,
--    Unifications, or Host Calls.
-- 3. Head Normalization: Maps the various surface rule types (Simplification,
--    Propagation, Simpagation) into a uniform 'Kept/Removed' head structure.
-- 4. Symbol Table Generation: Performs a whole-program scan to assign
--    unique, sequential 0-indexed integers to every 'Qualified' CHR constraint,
--    enabling efficient array-based dispatch in the VM.
--
-- By the end of this pass, the program is no longer a set of human-readable
-- files, but a structured list of instructions and a numeric symbol map.
module YCHR.Desugar
  ( DesugarError (..),
    desugarProgram,
    desugarQueryGoals,
    liftAllLambdas,
    liftQueryLambdas,
    SymbolTable,
    extractSymbolTable,
  )
where

import Data.List (mapAccumL)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Effectful (Eff, runPureEff, (:>))
import Effectful.State.Static.Local (State, evalState, get, modify)
import Effectful.Writer.Static.Local (Writer, runWriter, tell)
import YCHR.Desugared qualified as D
import YCHR.Parsed qualified as P
import YCHR.Pretty (AnnP (..), PrettyE (..))
import YCHR.Types

data DesugarError
  = UnexpectedBodyTerm P.SourceLoc Term
  | UnexpectedGuardTerm P.SourceLoc Term
  deriving (Eq, Show)

isFunctionDecl :: P.Declaration -> Bool
isFunctionDecl P.FunctionDecl {} = True
isFunctionDecl _ = False

-- | Collect all declared function names (fully qualified) from a set of modules.
buildFunctionSet :: [P.Module] -> Set.Set Name
buildFunctionSet mods =
  Set.fromList
    [ Qualified m.name d.name
    | m <- mods,
      P.Ann d _ <- m.decls,
      isFunctionDecl d
    ]

-- | The primary entry point: converts parsed modules to a desugared program.
desugarProgram :: [P.Module] -> Either [DesugarError] D.Program
desugarProgram mods =
  let funSet = buildFunctionSet mods
      conTypes = collectConstraintTypes mods
      typeDefs = [td.node | m <- mods, td <- m.typeDecls]
      (result, errs) = runPureEff . runWriter $ do
        rules <- traverse (desugarRule funSet) [r | m <- mods, r <- m.rules]
        functions <- desugarFunctions mods
        pure (D.Program rules functions conTypes typeDefs)
   in if null errs then Right result else Left errs

-- | Collect typed constraint declarations into a map from qualified name to arg types.
collectConstraintTypes :: [P.Module] -> Map.Map Name [TypeExpr]
collectConstraintTypes mods =
  Map.fromList
    [ (Qualified m.name d.name, ts)
    | m <- mods,
      P.Ann d _ <- m.decls,
      P.ConstraintDecl {} <- [d],
      Just ts <- [d.argTypes]
    ]

-- | Scans a desugared program and builds the optimization map.
-- It ensures that all Qualified names get a sequential ID starting from 0.
extractSymbolTable :: D.Program -> SymbolTable
extractSymbolTable prog =
  let rules = prog.rules
      allIds = Set.fromList [Identifier c.name (length c.args) | r <- rules, c <- getRuleConstraints r]
      qualifiedIds = [i | i@(Identifier (Qualified _ _) _) <- Set.toList allIds]
   in mkSymbolTable (zip qualifiedIds (map ConstraintType [0 ..]))

-- | Helper to find every constraint instance in a desugared rule.
getRuleConstraints :: D.Rule -> [Constraint]
getRuleConstraints r =
  let AnnP {node = rHead} = r.head
      AnnP {node = rBody} = r.body
   in rHead.kept
        ++ rHead.removed
        ++ [c | D.BodyConstraint c <- rBody]

desugarRule :: Set.Set Name -> P.Rule -> Eff '[Writer [DesugarError]] D.Rule
desugarRule funSet r = do
  ruleBody <- desugarBodyGoals funSet r.body.sourceLoc r.body.node
  userGuards <- traverse (desugarGuard r.guard.sourceLoc) r.guard.node
  let rawHead = desugarHead r.head.node
      (hnfGuards, normalizedHead) = normalizeHead rawHead
  pure
    D.Rule
      { name = fmap (.node) r.name,
        head = AnnP normalizedHead r.head.sourceLoc (PrettyE r.head.node),
        guard = AnnP (hnfGuards ++ userGuards) r.guard.sourceLoc (PrettyE r.guard.node),
        body = AnnP ruleBody r.body.sourceLoc (PrettyE r.body.node)
      }

desugarHead :: P.Head -> D.Head
desugarHead h = case h of
  P.Simplification rs -> D.Head [] rs
  P.Propagation ks -> D.Head ks []
  P.Simpagation ks rs -> D.Head ks rs

-- Head Normal Form (HNF) transformation
-- All head arguments become distinct variables; duplicate variables and
-- non-variable terms are replaced with fresh variables and explicit
-- GuardEqual guards are generated.

data HnfState = HnfState
  { hnfCounter :: !Int,
    hnfSeen :: Set.Set Text,
    hnfGuards :: [D.Guard] -- accumulated in reverse
  }

normalizeHead :: D.Head -> ([D.Guard], D.Head)
normalizeHead h =
  let initState = HnfState 0 Set.empty []
      (st1, kept') = mapAccumL normalizeConstraint initState h.kept
      (st2, removed') = mapAccumL normalizeConstraint st1 h.removed
   in (reverse st2.hnfGuards, D.Head kept' removed')

normalizeConstraint :: HnfState -> Constraint -> (HnfState, Constraint)
normalizeConstraint st (Constraint cname cargs) =
  let (st', args') = mapAccumL normalizeArg st cargs
   in (st', Constraint cname args')

normalizeArg :: HnfState -> Term -> (HnfState, Term)
normalizeArg st (VarTerm v)
  | Set.member v st.hnfSeen =
      let fresh = "_hnf_" <> T.pack (show st.hnfCounter)
       in ( st
              { hnfCounter = st.hnfCounter + 1,
                hnfGuards = D.GuardEqual (VarTerm v) (VarTerm fresh) : st.hnfGuards
              },
            VarTerm fresh
          )
  | otherwise =
      (st {hnfSeen = Set.insert v st.hnfSeen}, VarTerm v)
-- Wildcards pass through unchanged: they match anything, are never referenced,
-- and cannot duplicate, so no fresh variable or guard is needed.
normalizeArg st Wildcard = (st, Wildcard)
normalizeArg st (CompoundTerm cname cargs) =
  let fresh = "_hnf_" <> T.pack (show st.hnfCounter)
      st' = st {hnfCounter = st.hnfCounter + 1}
      st'' = decomposeCompound st' fresh cname cargs
   in (st'', VarTerm fresh)
normalizeArg st term =
  let fresh = "_hnf_" <> T.pack (show st.hnfCounter)
   in ( st
          { hnfCounter = st.hnfCounter + 1,
            hnfGuards = D.GuardEqual (VarTerm fresh) term : st.hnfGuards
          },
        VarTerm fresh
      )

-- | Decompose a compound term into match and extraction guards.
decomposeCompound :: HnfState -> Text -> Name -> [Term] -> HnfState
decomposeCompound st parentVar cname cargs =
  let matchGuard = D.GuardMatch (VarTerm parentVar) cname (length cargs)
      st' = st {hnfGuards = matchGuard : st.hnfGuards}
   in foldl' (\s (i, arg) -> decomposeArg s parentVar i arg) st' (zip [0 ..] cargs)

-- | Decompose a single argument of a compound term.
decomposeArg :: HnfState -> Text -> Int -> Term -> HnfState
decomposeArg st parentVar i (VarTerm v)
  | Set.member v st.hnfSeen =
      -- Duplicate variable: extract and check equality
      let fresh = "_hnf_" <> T.pack (show st.hnfCounter)
          getGuard = D.GuardGetArg fresh (VarTerm parentVar) i
          eqGuard = D.GuardEqual (VarTerm v) (VarTerm fresh)
       in st
            { hnfCounter = st.hnfCounter + 1,
              hnfGuards = eqGuard : getGuard : st.hnfGuards
            }
  | otherwise =
      -- First occurrence: extract and bind
      let getGuard = D.GuardGetArg v (VarTerm parentVar) i
       in st
            { hnfGuards = getGuard : st.hnfGuards,
              hnfSeen = Set.insert v st.hnfSeen
            }
decomposeArg st _ _ Wildcard = st
decomposeArg st parentVar i (CompoundTerm cname cargs) =
  -- Nested compound: extract then recursively decompose
  let fresh = "_hnf_" <> T.pack (show st.hnfCounter)
      getGuard = D.GuardGetArg fresh (VarTerm parentVar) i
      st' =
        st
          { hnfCounter = st.hnfCounter + 1,
            hnfGuards = getGuard : st.hnfGuards
          }
   in decomposeCompound st' fresh cname cargs
decomposeArg st parentVar i term =
  -- Ground term (atom, integer, string): extract and check equality
  let fresh = "_hnf_" <> T.pack (show st.hnfCounter)
      getGuard = D.GuardGetArg fresh (VarTerm parentVar) i
      eqGuard = D.GuardEqual (VarTerm fresh) term
   in st
        { hnfCounter = st.hnfCounter + 1,
          hnfGuards = eqGuard : getGuard : st.hnfGuards
        }

-- | Desugar function equations: group by name, normalize patterns via HNF.
desugarFunctions :: [P.Module] -> Eff '[Writer [DesugarError]] [D.Function]
desugarFunctions mods =
  traverse
    (\(m, d) -> desugarFunction m.name d.name d.arity d.argTypes d.returnType [eq | P.Ann eq _ <- m.equations, eq.funName == d.name])
    [(m, d) | m <- mods, P.Ann d _ <- m.decls, isFunctionDecl d]

desugarFunction :: Text -> Text -> Int -> Maybe [TypeExpr] -> Maybe TypeExpr -> [P.FunctionEquation] -> Eff '[Writer [DesugarError]] D.Function
desugarFunction modName funName arity argTys retTy eqs = do
  desugaredEqs <- traverse desugarEquation eqs
  pure
    D.Function
      { name = Qualified modName funName,
        arity = arity,
        argTypes = argTys,
        returnType = retTy,
        equations = desugaredEqs
      }

desugarEquation :: P.FunctionEquation -> Eff '[Writer [DesugarError]] D.Equation
desugarEquation eq = do
  let initState = HnfState 0 Set.empty []
      (st, normalizedArgs) = mapAccumL normalizeArg initState eq.args
      hnfGuards = reverse st.hnfGuards
  userGuards <- traverse (desugarGuard eq.guard.sourceLoc) eq.guard.node
  pure
    D.Equation
      { params = normalizedArgs,
        guards = hnfGuards ++ userGuards,
        rhs = eq.rhs.node
      }

-- | Classify a parsed guard term into a 'D.Guard'.
--
-- * @true@ -> 'D.GoalTrue'
-- * Compound terms -> 'D.GuardExpr' (equality checks, host calls, etc.)
-- * Anything else (bare variable, integer, atom, …) -> error
desugarGuard :: P.SourceLoc -> Term -> Eff '[Writer [DesugarError]] D.Guard
desugarGuard _ (AtomTerm "true") = pure $ D.GuardCommon D.GoalTrue
desugarGuard _ t@(CompoundTerm _ _) = pure $ D.GuardExpr t
desugarGuard loc t = do
  tell [UnexpectedGuardTerm loc t]
  pure $ D.GuardCommon D.GoalTrue

-- | Desugar a list of query goal terms into 'BodyGoal's.
-- Returns 'Left' if any desugaring errors occur.
desugarQueryGoals :: [P.Module] -> [Term] -> Either [DesugarError] [D.BodyGoal]
desugarQueryGoals mods goals =
  let funSet = buildFunctionSet mods
      (results, errs) =
        runPureEff . runWriter $
          desugarBodyGoals funSet P.dummyLoc goals
   in if null errs then Right results else Left errs

-- ---------------------------------------------------------------------------
-- VarNameSupply: fresh variable generation for desugaring
-- ---------------------------------------------------------------------------

freshVarName :: (State Int :> es) => Eff es Text
freshVarName = do
  n <- get @Int
  modify @Int (+ 1)
  pure ("__is_" <> T.pack (show n))

runVarNameSupply :: Eff (State Int : es) a -> Eff es a
runVarNameSupply = evalState (0 :: Int)

-- | Desugar a list of body terms, flattening any multi-goal expansions
-- (e.g. non-variable @is@ LHS).
desugarBodyGoals ::
  (Writer [DesugarError] :> es) =>
  Set.Set Name ->
  P.SourceLoc ->
  [Term] ->
  Eff es [D.BodyGoal]
desugarBodyGoals funSet loc terms =
  runVarNameSupply $ concat <$> traverse (desugarBodyGoal funSet loc) terms

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
-- 7. @true@ -> 'D.GoalTrue'
-- 8. Unqualified compound (renamer should have caught this) -> error
-- 9. Anything else (bare variable, integer, atom, …) -> error
desugarBodyGoal ::
  (State Int :> es, Writer [DesugarError] :> es) =>
  Set.Set Name ->
  P.SourceLoc ->
  Term ->
  Eff es [D.BodyGoal]
desugarBodyGoal funSet loc t = case t of
  CompoundTerm (Unqualified "=") [l, r] -> pure [D.BodyUnify l r]
  CompoundTerm (Unqualified "is") [VarTerm v, expr] ->
    pure [D.BodyIs v expr]
  CompoundTerm (Unqualified "is") [lhs, expr] -> do
    v <- freshVarName
    pure [D.BodyIs v expr, D.BodyUnify (VarTerm v) lhs]
  CompoundTerm (Qualified "host" f) args ->
    pure [D.BodyHostStmt f args]
  CompoundTerm name@(Qualified _ _) args
    | Set.member name funSet ->
        pure [D.BodyFunctionCall name args]
  CompoundTerm name@(Qualified _ _) args ->
    pure [D.BodyConstraint (Constraint name args)]
  CompoundTerm (Unqualified "call_fun") args
    | length args >= 2 ->
        pure [D.BodyFunctionCall (Unqualified "call_fun") args]
  AtomTerm "true" -> pure [D.BodyCommon D.GoalTrue]
  CompoundTerm (Unqualified _) _ -> do
    tell [UnexpectedBodyTerm loc t]
    pure [D.BodyCommon D.GoalTrue]
  _ -> do
    tell [UnexpectedBodyTerm loc t]
    pure [D.BodyCommon D.GoalTrue]

-- ---------------------------------------------------------------------------
-- Lambda lifting
-- ---------------------------------------------------------------------------

data LiftState = LiftState
  { liftCounter :: !Int,
    liftedFunctions :: [D.Function]
  }

-- | Collect all variable names from a term.
termVars :: Term -> Set.Set Text
termVars (VarTerm v) = Set.singleton v
termVars (CompoundTerm _ args) = Set.unions (map termVars args)
termVars _ = Set.empty

-- | Extract parameters and body from a @fun(X, Y) -> body@ lambda term.
-- Parameters are kept as 'Term' values ('VarTerm' or 'Wildcard').
extractLambdaParams :: Term -> ([Term], Term)
extractLambdaParams (CompoundTerm (Unqualified "->") [CompoundTerm (Unqualified "fun") params, body]) =
  (params, body)
extractLambdaParams t = ([], t)

-- | Lift lambdas in a single term.  Returns the updated state and the
-- rewritten term (with @^@ replaced by closure compound terms).
liftTerm :: Text -> Set.Set Text -> LiftState -> Term -> (LiftState, Term)
liftTerm modName scope st term = case term of
  CompoundTerm (Unqualified "->") [CompoundTerm (Unqualified "fun") _, _] ->
    let (params, body) = extractLambdaParams term
        paramVarNames = Set.fromList [v | VarTerm v <- params]
        bodyVars = termVars body
        freeVars = Set.toAscList (bodyVars `Set.intersection` scope `Set.difference` paramVarNames)
        innerScope = scope `Set.union` paramVarNames
        (st', liftedBody) = liftTerm modName innerScope st body
        idx = st'.liftCounter
        lambdaName = "__lambda_" <> T.pack (show idx)
        qualName = Qualified modName lambdaName
        allParams = map VarTerm freeVars ++ params
        func =
          D.Function
            { name = qualName,
              arity = length allParams,
              argTypes = Nothing,
              returnType = Nothing,
              equations =
                [ D.Equation
                    { params = allParams,
                      guards = [],
                      rhs = liftedBody
                    }
                ]
            }
        st'' = st' {liftCounter = idx + 1, liftedFunctions = func : st'.liftedFunctions}
     in (st'', CompoundTerm (Qualified modName lambdaName) (map VarTerm freeVars))
  CompoundTerm name args ->
    let (st', args') = mapAccumL (liftTerm modName scope) st args
     in (st', CompoundTerm name args')
  _ -> (st, term)

-- | Lift lambdas in a body goal.
liftBodyGoal :: Text -> Set.Set Text -> LiftState -> D.BodyGoal -> (LiftState, D.BodyGoal)
liftBodyGoal modName scope st goal = case goal of
  D.BodyIs v expr ->
    let (st', expr') = liftTerm modName scope st expr
     in (st', D.BodyIs v expr')
  D.BodyFunctionCall name args ->
    let (st', args') = mapAccumL (liftTerm modName scope) st args
     in (st', D.BodyFunctionCall name args')
  D.BodyConstraint (Constraint cname cargs) ->
    let (st', cargs') = mapAccumL (liftTerm modName scope) st cargs
     in (st', D.BodyConstraint (Constraint cname cargs'))
  D.BodyUnify t1 t2 ->
    let (st', t1') = liftTerm modName scope st t1
        (st'', t2') = liftTerm modName scope st' t2
     in (st'', D.BodyUnify t1' t2')
  D.BodyHostStmt f args ->
    let (st', args') = mapAccumL (liftTerm modName scope) st args
     in (st', D.BodyHostStmt f args')
  D.BodyCommon g -> (st, D.BodyCommon g)

-- | Lift lambdas in a guard.
liftGuard :: Text -> Set.Set Text -> LiftState -> D.Guard -> (LiftState, D.Guard)
liftGuard modName scope st (D.GuardExpr term) =
  let (st', term') = liftTerm modName scope st term
   in (st', D.GuardExpr term')
liftGuard _ _ st g = (st, g)

-- | Lift lambdas in a function equation.
liftEquation :: Text -> LiftState -> D.Equation -> (LiftState, D.Equation)
liftEquation modName st eq =
  let scope = Set.unions (map termVars eq.params)
      (st', guards') = mapAccumL (liftGuard modName scope) st eq.guards
      (st'', rhs') = liftTerm modName scope st' eq.rhs
   in (st'', eq {D.guards = guards', D.rhs = rhs'})

-- | Lift lambdas in a function definition.
liftFunction :: LiftState -> D.Function -> (LiftState, D.Function)
liftFunction st func =
  let modName = case func.name of
        Qualified m _ -> m
        Unqualified _ -> ""
      (st', eqs') = mapAccumL (liftEquation modName) st func.equations
   in (st', func {D.equations = eqs'})

-- | Extract all variables from a rule head (kept + removed constraints).
ruleHeadVars :: D.Head -> Set.Set Text
ruleHeadVars h =
  Set.unions
    [ termVars arg
    | c <- h.kept ++ h.removed,
      arg <- c.args
    ]

-- | Extract the module name from a rule's head constraints.
ruleModName :: D.Head -> Text
ruleModName h = case h.kept ++ h.removed of
  (Constraint (Qualified m _) _ : _) -> m
  _ -> ""

-- | Collect all variables from a list of body goals.
bodyGoalVars :: [D.BodyGoal] -> Set.Set Text
bodyGoalVars = Set.unions . map goalVars
  where
    goalVars (D.BodyIs v expr) = Set.insert v (termVars expr)
    goalVars (D.BodyFunctionCall _ args) = Set.unions (map termVars args)
    goalVars (D.BodyConstraint (Constraint _ args)) = Set.unions (map termVars args)
    goalVars (D.BodyUnify t1 t2) = termVars t1 `Set.union` termVars t2
    goalVars (D.BodyHostStmt _ args) = Set.unions (map termVars args)
    goalVars (D.BodyCommon _) = Set.empty

-- | Collect all variables from a list of guards.
guardVars :: [D.Guard] -> Set.Set Text
guardVars = Set.unions . map gVars
  where
    gVars (D.GuardExpr t) = termVars t
    gVars (D.GuardEqual t1 t2) = termVars t1 `Set.union` termVars t2
    gVars (D.GuardGetArg v t _) = Set.insert v (termVars t)
    gVars (D.GuardMatch t _ _) = termVars t
    gVars (D.GuardCommon _) = Set.empty

-- | Lift lambdas in a rule. The scope includes all variables from the
-- entire rule (head, guard, and body).
liftRule :: LiftState -> D.Rule -> (LiftState, D.Rule)
liftRule st rule =
  let headNode = rule.head.node
      scope =
        ruleHeadVars headNode
          `Set.union` guardVars rule.guard.node
          `Set.union` bodyGoalVars rule.body.node
      modName = ruleModName headNode
      (st', guards') = mapAccumL (liftGuard modName scope) st rule.guard.node
      (st'', body') = mapAccumL (liftBodyGoal modName scope) st' rule.body.node
   in ( st'',
        rule
          { D.guard = rule.guard {node = guards'},
            D.body = rule.body {node = body'}
          }
      )

-- | Post-desugaring pass: lift all lambda expressions into top-level functions.
liftAllLambdas :: D.Program -> D.Program
liftAllLambdas prog =
  let initState = LiftState 0 []
      (st1, functions') = mapAccumL liftFunction initState prog.functions
      (st2, rules') = mapAccumL liftRule st1 prog.rules
   in prog
        { D.functions = functions' ++ st2.liftedFunctions,
          D.rules = rules'
        }

-- | Lift lambdas from query body goals. Returns the rewritten goals
-- and any generated function definitions (to be compiled on the fly).
-- Uses @\"__query\"@ as the module name for lifted lambdas, and starts
-- the counter high enough to avoid collisions with program lambdas.
liftQueryLambdas :: Int -> [D.BodyGoal] -> ([D.BodyGoal], [D.Function])
liftQueryLambdas startCounter goals =
  let scope = bodyGoalVars goals
      initState = LiftState startCounter []
      (st, goals') = mapAccumL (liftBodyGoal "__query" scope) initState goals
   in (goals', st.liftedFunctions)
