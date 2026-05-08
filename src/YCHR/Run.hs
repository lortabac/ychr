{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

-- | Top-level orchestration: compile a program, then run goals or
-- multi-goal queries against it. The CHR session machinery lives in
-- "YCHR.Runtime.Session"; the compilation pipeline lives in
-- "YCHR.Compile.Pipeline". This module ties the two together and
-- adds the query-time goal evaluator used by 'runProgramWithQuery'
-- and the live REPL session in "YCHR.Repl".
module YCHR.Run
  ( -- * Compilation (re-exported from "YCHR.Compile.Pipeline")
    Error (..),
    Warning (..),
    CompiledProgram (..),
    ExportResolution (..),
    ConstraintType,
    compileModules,
    compileFiles,
    compileParsedModules,

    -- * CHR effect (re-exported from "YCHR.Runtime.Session")
    CHR,
    CHREffects,
    runCHR,
    withCHR,
    toSessionInput,
    tellConstraint,

    -- * Re-exports for embedding
    Value (..),
    newVar,
    deref,
    equal,
    unify,

    -- * Single-goal API
    resolveQueryConstraint,
    runProgramWithGoalDSL,
    runProgramWithGoal,
    prepareGoal,
    runPreparedGoal,

    -- * Multi-goal query API
    PreparedQuery (..),
    prepareQuery,
    executePreparedQuery,
    runProgramWithQuery,
  )
where

import Control.Exception (throwIO)
import Control.Monad (unless, void, when)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Effectful
import Effectful.Dispatch.Static
import Effectful.State.Static.Local (State, evalState, get, modify)
import Effectful.Writer.Static.Local (listen, runWriter)
import YCHR.Compile
  ( buildFunctionSet,
    compileFunctionDef,
    funcProcName,
    genCallFunDispatches,
    tellProcName,
    vmName,
  )
import YCHR.Compile.Pipeline
  ( CompiledProgram (..),
    Error (..),
    ExportResolution (..),
    Warning (..),
    compileFiles,
    compileModules,
    compileParsedModules,
  )
import YCHR.Desugar (desugarQueryGoals, liftQueryLambdas)
import YCHR.Desugared qualified as D
import YCHR.Meta (valueToTerm)
import YCHR.PExpr (PExpr (Atom))
import YCHR.Parsed (SourceLoc (..))
import YCHR.Parser (parseConstraint, parseQueryWith)
import YCHR.Pretty (prettyTerm)
import YCHR.Rename (renameQueryArgs, renameQueryGoals)
import YCHR.Runtime.Error (CallStack)
import YCHR.Runtime.Interpreter (HostCallFn (..), HostCallRegistry, callProc)
import YCHR.Runtime.Reactivation (drainQueue, enqueue)
import YCHR.Runtime.Session
  ( CHR,
    CHREffects,
    ProcMap,
    StaticRep (CHRRep),
    runCHR,
    tellConstraint,
    toSessionInput,
    withCHR,
    withCHRExtra,
  )
import YCHR.Runtime.Store (CHRStore, aliveConstraint)
import YCHR.Runtime.Types (CallVal (..), Value (..))
import YCHR.Runtime.Var (Unify, deref, equal, newVar, unify)
import YCHR.TypeCheck (typeCheckGoals)
import YCHR.Types (Constraint (..), ConstraintType, Term (..))
import YCHR.Types qualified as Types
import YCHR.VM (Name (..), Procedure (..), Program (..))

-- ---------------------------------------------------------------------------
-- Single-goal API
-- ---------------------------------------------------------------------------

-- | Resolve a query constraint against the export map. The resolved
-- form is a 'Types.QualifiedConstraint' since name resolution always
-- produces a fully-qualified name.
resolveQueryConstraint ::
  CompiledProgram ->
  Constraint ->
  Either String Types.QualifiedConstraint
resolveQueryConstraint cp (Constraint cname cargs) = case cname of
  Types.Unqualified n ->
    let arity = length cargs
     in case Map.lookup (Types.UnqualifiedIdentifier n arity) cp.exportMap of
          Just (UniqueExport (Types.Qualified m b)) ->
            Right (Types.QualifiedConstraint (Types.QualifiedName m b) cargs)
          Just (UniqueExport (Types.Unqualified _)) ->
            Left ("Unqualified export resolution for " ++ T.unpack n)
          Just (AmbiguousExport ms) ->
            Left
              ( "Ambiguous constraint: "
                  ++ T.unpack n
                  ++ "/"
                  ++ show arity
                  ++ ", exported by: "
                  ++ intercalate ", " (map T.unpack ms)
              )
          Nothing -> Left ("Unknown constraint: " ++ T.unpack n ++ "/" ++ show arity)
  Types.Qualified m n ->
    let arity = length cargs
     in if Set.member (Types.QualifiedIdentifier m n arity) cp.exportedSet
          then Right (Types.QualifiedConstraint (Types.QualifiedName m n) cargs)
          else
            Left
              ( "Constraint not exported: "
                  ++ T.unpack m
                  ++ ":"
                  ++ T.unpack n
                  ++ "/"
                  ++ show arity
              )

-- | Run a single CHR constraint against a compiled program.
--
-- Reuses 'withCHR' for session setup so that the runtime effect stack
-- lives in one place ("YCHR.Runtime.Session"). The query-scope
-- variable map is layered on top via 'evalState'.
runProgramWithGoalDSL ::
  CompiledProgram ->
  HostCallRegistry ->
  Constraint ->
  IO
    ( Value,
      Map Text Term
    )
runProgramWithGoalDSL cp hostCalls constraint = do
  resolved <- case resolveQueryConstraint cp constraint of
    Left err -> fail err
    Right c -> pure c
  let procMap = Map.fromList [(p.name, p) | p <- cp.program.procedures]
      tellName = tellProcName (Types.qualifiedToName resolved.name) (length resolved.args)
  unless (Map.member tellName procMap) $
    fail ("Constraint not found: " ++ T.unpack tellName.unName)
  withCHR (toSessionInput cp) hostCalls $
    evalState (Map.empty :: Map Text Value) $ do
      argVals <- traverse termToValue resolved.args
      result <- callProc procMap hostCalls tellName (map CVal argVals)
      bindings <- get >>= Map.traverseWithKey valueToTerm
      pure (result, bindings)

-- | Parse and rename a goal, returning the canonicalized 'Constraint'
-- alongside any rename warnings. Throws on parse or rename errors.
-- Splitting this out lets the CLI surface goal-argument warnings before
-- the goal runs (notably for @--Werror@).
prepareGoal :: CompiledProgram -> Text -> IO (Constraint, [Warning])
prepareGoal cp src = case parseConstraint "<query>" src of
  Left err -> throwIO (ParseError "<query>" err)
  Right (Left validErr) -> throwIO (ParseValidationErrors [validErr])
  -- Rename the constraint's arguments so that bare data-constructor
  -- references (e.g. @[H|T]@, declared atoms) get canonicalized to
  -- the same flat-functor form the compiled head patterns expect.
  Right (Right (Constraint cname cargs)) -> do
    (renamedArgs, ws) <-
      either
        (throwIO . RenameErrors)
        pure
        (renameQueryArgs cp.allModules cargs)
    let warnings = [RenameWarnings ws | not (null ws)]
    pure (Constraint cname renamedArgs, warnings)

-- | Type-check and run a previously prepared single-goal constraint.
-- Throws 'TypeErrors' on goal-time type errors.
runPreparedGoal ::
  CompiledProgram ->
  HostCallRegistry ->
  Constraint ->
  IO (Value, Map Text Term)
runPreparedGoal cp hostCalls original = do
  -- Canonicalize the constraint name via the export map so the
  -- type-check sees the same qualified name 'tellConstraintSigs'
  -- registers. Defer name-resolution failures to 'runProgramWithGoalDSL'
  -- (which produces a clearer "constraint not found" error).
  tcErrs <- case resolveQueryConstraint cp original of
    Right qc ->
      typeCheckGoals
        cp.desugaredProgram
        (SourceLoc "<query>" 1 1)
        (Just "query")
        [D.BodyConstraint qc]
    Left _ -> pure []
  unless (null tcErrs) (throwIO (TypeErrors tcErrs))
  runProgramWithGoalDSL cp hostCalls original

-- | Like 'runProgramWithGoalDSL' but accepts a query as surface-language 'Text'.
-- Convenience wrapper: 'prepareGoal' + 'runPreparedGoal', dropping warnings.
runProgramWithGoal ::
  CompiledProgram ->
  HostCallRegistry ->
  Text ->
  IO
    ( Value,
      Map Text Term
    )
runProgramWithGoal cp hostCalls src = do
  (constraint, _ws) <- prepareGoal cp src
  runPreparedGoal cp hostCalls constraint

-- ---------------------------------------------------------------------------
-- Multi-goal query API
-- ---------------------------------------------------------------------------

-- | Result of parsing, desugaring, lambda-lifting, and type-checking
-- a query — everything that can be done before entering the CHR effect
-- stack. 'queryLambdas' is non-empty iff the query introduced anonymous
-- @fun(...) -> ... end@ expressions; 'extraProcs' must be added to the
-- 'ProcMap' before executing the query.
data PreparedQuery = PreparedQuery
  { liftedGoals :: [D.BodyGoal],
    queryLambdas :: [D.Function],
    extraProcs :: [Procedure]
  }

-- | Parse, rename, desugar, lambda-lift, and type-check a query.
-- Returns the prepared query alongside any rename warnings produced
-- while canonicalizing the goals' terms. Throws the appropriate
-- 'Error' constructor on failure.
prepareQuery :: CompiledProgram -> Text -> IO (PreparedQuery, [Warning])
prepareQuery cp src = do
  goals <-
    either
      (throwIO . ParseError "<query>")
      pure
      ( parseQueryWith
          cp.opTable
          "<query>"
          src
      )
  (renamed, renameWs) <-
    either
      (throwIO . RenameErrors)
      pure
      ( renameQueryGoals
          cp.allModules
          goals
      )
  bodyGoals <-
    either
      (throwIO . DesugarErrors)
      pure
      ( desugarQueryGoals
          cp.functionNameSet
          renamed
      )
  -- Lambda-lift query body goals and compile the generated functions
  let queryLoc = SourceLoc "<query>" 1 1
  (lifted, lambdas) <-
    either
      (throwIO . DesugarErrors)
      pure
      ( liftQueryLambdas
          cp.nextLambdaIndex
          queryLoc
          (Atom "")
          bodyGoals
      )
  -- Type-check the goals (after lambda lifting so lifted lambdas are
  -- visible as untyped functions defaulting to all-@any@). Goal-time
  -- type errors abort execution and surface as 'TypeErrors'.
  let cdp = cp.desugaredProgram
      progForCheck =
        D.Program
          cdp.rules
          (cdp.functions ++ lambdas)
          cdp.constraintTypes
          cdp.typeDefinitions
  tcErrs <- typeCheckGoals progForCheck queryLoc (Just "query") lifted
  unless (null tcErrs) (throwIO (TypeErrors tcErrs))
  let allFuns = cp.allFunctions ++ lambdas
      funSet = buildFunctionSet (D.Program [] allFuns Map.empty [])
      queryProcs = compileQueryLambdas funSet lambdas
      queryDispatches = genCallFunDispatches allFuns
      warnings = [RenameWarnings renameWs | not (null renameWs)]
  pure
    ( PreparedQuery
        { liftedGoals = lifted,
          queryLambdas = lambdas,
          extraProcs = queryProcs ++ queryDispatches
        },
      warnings
    )

-- | Execute the lifted goals of a 'PreparedQuery' inside an existing CHR
-- session. Opens its own per-query variable scope and returns the
-- resulting bindings.
executePreparedQuery ::
  (CHREffects es) =>
  HostCallRegistry ->
  [D.BodyGoal] ->
  Eff es (Map Text Term)
executePreparedQuery hostCalls lifted =
  evalState (Map.empty :: Map Text Value) $ do
    mapM_ (executeBodyGoal hostCalls) lifted
    varMap <- get
    Map.traverseWithKey valueToTerm varMap

-- | Run a multi-goal query against a compiled program.
--
-- Parses the input as a comma-separated, dot-terminated list of goals,
-- renames and desugars them like rule bodies, then executes each goal.
-- Convenience wrapper over 'prepareQuery' + 'executePreparedQuery';
-- discards rename warnings (callers that need them — e.g. the REPL
-- under @--Werror@ — should call 'prepareQuery' directly).
runProgramWithQuery :: CompiledProgram -> HostCallRegistry -> Text -> IO (Map Text Term)
runProgramWithQuery cp hostCalls src = do
  (prep, _ws) <- prepareQuery cp src
  withCHRExtra (toSessionInput cp) hostCalls prep.extraProcs $
    executePreparedQuery hostCalls prep.liftedGoals

-- ---------------------------------------------------------------------------
-- Query goal evaluator (internal)
-- ---------------------------------------------------------------------------

-- | Resolve a surface 'Term' to a 'Value' inside the per-query
-- variable scope, allocating a fresh logical variable for each new
-- 'VarTerm' the query introduces.
termToValue :: (Unify :> es, State (Map Text Value) :> es) => Term -> Eff es Value
termToValue (VarTerm n) = do
  varMap <- get
  case Map.lookup n varMap of
    Just v -> pure v
    Nothing -> do
      v <- newVar
      modify (Map.insert n v)
      pure v
termToValue (IntTerm n) = pure (VInt n)
termToValue (FloatTerm n) = pure (VFloat n)
termToValue (AtomTerm s) = pure (VAtom s)
termToValue (TextTerm s) = pure (VText s)
termToValue Wildcard = pure VWildcard
-- 'Qualified' constructors flatten to a single @vmName@-encoded
-- functor (@m__n@), matching what 'YCHR.Compile.compileTerm' emits.
-- 0-arity uses keep an empty arg vector so 'matchTerm' (which only
-- looks at 'VTerm') can dispatch on them.
termToValue (CompoundTerm name@(Types.Qualified _ _) ts) = do
  ts' <- traverse termToValue ts
  pure (VTerm (vmName name).unName ts')
termToValue (CompoundTerm name ts) = VTerm (vmName name).unName <$> traverse termToValue ts

-- | Execute a single desugared body goal in the query context.
executeBodyGoal ::
  (CHREffects es, State (Map Text Value) :> es) =>
  HostCallRegistry ->
  D.BodyGoal ->
  Eff es ()
executeBodyGoal _ D.BodyTrue = pure ()
executeBodyGoal _ (D.BodyUnify l r) = do
  v1 <- termToValue l
  v2 <- termToValue r
  CHRRep procMap hc' _ _ <- getStaticRep
  (ok, observers) <- listen (unify v1 v2)
  enqueue observers
  unless ok (raiseUnifyFailure v1 v2)
  drainReactivation procMap hc'
executeBodyGoal hc (D.BodyHostStmt f args) = do
  argVals <- traverse termToValue args
  _ <- hostCall (Map.lookup (Name f) hc) f argVals
  pure ()
executeBodyGoal hc (D.BodyIs v expr) = do
  result <- evalNestedExpr hc expr
  varMap <- get
  case Map.lookup v varMap of
    Just existing -> do
      CHRRep procMap hc' _ _ <- getStaticRep
      (ok, observers) <- listen (unify existing result)
      enqueue observers
      unless ok (raiseUnifyFailure existing result)
      drainReactivation procMap hc'
    Nothing -> modify (Map.insert v result)
executeBodyGoal _ (D.BodyConstraint c) = do
  argVals <- traverse termToValue c.args
  tellConstraint (Types.qualifiedToName c.name) argVals
executeBodyGoal hc (D.BodyFunctionCall (Types.Unqualified "$call") args) = do
  CHRRep procMap _ _ _ <- getStaticRep
  argVals <- traverse termToValue args
  let n = length args - 1
      dispatchName = Name ("call_" <> T.pack (show n))
  _ <- callProc procMap hc dispatchName (map CVal argVals)
  pure ()
executeBodyGoal hc (D.BodyFunctionCall name args) = do
  CHRRep procMap _ _ _ <- getStaticRep
  argVals <- traverse termToValue args
  _ <- callProc procMap hc (funcProcName name (length argVals)) (map CVal argVals)
  pure ()

-- | Raise a runtime error describing a failed unification.
raiseUnifyFailure :: (Unify :> es) => Value -> Value -> Eff es ()
raiseUnifyFailure v1 v2 = do
  t1 <- valueToTerm "_" v1
  t2 <- valueToTerm "_" v2
  error $
    "unification failure: cannot unify "
      ++ prettyTerm t1
      ++ " with "
      ++ prettyTerm t2

-- | Call a host function, failing with a clear message if not found.
hostCall ::
  ( Unify :> es,
    CHRStore :> es,
    IOE :> es,
    State CallStack :> es
  ) =>
  Maybe HostCallFn -> Text -> [Value] -> Eff es Value
hostCall (Just (HostCallFn f)) _ args = f args
hostCall Nothing name _ = error $ "Unknown host function: " ++ T.unpack name

-- | Drain the reactivation queue, dispatching each constraint.
drainReactivation ::
  (CHREffects es) =>
  ProcMap ->
  HostCallRegistry ->
  Eff es ()
drainReactivation procMap hc =
  drainQueue $ \sid -> do
    alive <- aliveConstraint sid
    when alive $
      void $
        callProc procMap hc (Name "reactivate_dispatch") [CId sid]

-- | Evaluate a term as a nested expression (used for @is@ RHS and guard
-- expressions). Handles host calls (@host:f(args)@), user-defined function
-- calls, @term(X)@ (quoting — delegates to 'termToValue' to suppress
-- evaluation; see the Notes in "YCHR.Compile"), and data terms.
evalNestedExpr ::
  (CHREffects es, State (Map Text Value) :> es) =>
  HostCallRegistry ->
  Term ->
  Eff es Value
evalNestedExpr _ (IntTerm n) = pure (VInt n)
evalNestedExpr _ (FloatTerm n) = pure (VFloat n)
evalNestedExpr _ (AtomTerm s) = pure (VAtom s)
evalNestedExpr _ (TextTerm s) = pure (VText s)
evalNestedExpr _ Wildcard = pure VWildcard
evalNestedExpr _ (VarTerm v) = do
  varMap <- get
  case Map.lookup v varMap of
    Just val -> deref val
    Nothing -> do
      fresh <- newVar
      modify (Map.insert v fresh)
      pure fresh
evalNestedExpr hc (CompoundTerm (Types.Unqualified "$call") args)
  | length args >= 2 = do
      CHRRep procMap _ _ _ <- getStaticRep
      argVals <- traverse (evalNestedExpr hc) args
      let n = length args - 1
          dispatchName = Name ("call_" <> T.pack (show n))
      callProc procMap hc dispatchName (map CVal argVals)
evalNestedExpr _ (CompoundTerm (Types.Unqualified "term") [arg]) =
  termToValue arg
evalNestedExpr hc (CompoundTerm (Types.Qualified "host" f) args) = do
  argVals <- traverse (evalNestedExpr hc) args
  hostCall (Map.lookup (Name f) hc) f argVals
evalNestedExpr hc (CompoundTerm name args) = do
  CHRRep procMap _ _ _ <- getStaticRep
  let fnName = funcProcName name (length args)
  if Map.member fnName procMap
    then do
      argVals <- traverse (evalNestedExpr hc) args
      callProc procMap hc fnName (map CVal argVals)
    else VTerm (vmName name).unName <$> traverse termToValue args

-- | Compile lifted query lambdas into VM procedures. Discards the
-- 'Writer' error channel: by the time this runs, 'prepareQuery' has
-- already lifted these lambdas from a desugared program that
-- compiled cleanly and has type-checked them, so any error here
-- would indicate a compiler bug rather than a user problem.
compileQueryLambdas :: Set Types.Identifier -> [D.Function] -> [Procedure]
compileQueryLambdas funSet lambdas =
  let (procs, _errs) = runPureEff . runWriter $ traverse (compileFunctionDef funSet) lambdas
   in procs
