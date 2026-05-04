{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module YCHR.Run
  ( -- * Compilation (re-exported from "YCHR.Compile.Pipeline")
    Error (..),
    Warning (..),
    CompiledProgram (..),
    ExportResolution (..),
    ConstraintType,
    compileModules,
    compileFiles,

    -- * CHR effect
    CHR,
    CHREffects,
    runCHR,
    withCHR,
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

    -- * Multi-goal query API
    runProgramWithQuery,

    -- * Live REPL session
    runLiveSession,
  )
where

import Control.Exception (SomeException, displayException, fromException, throwIO, try)
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
import Effectful.Exception qualified as Eff
import Effectful.State.Static.Local (State, evalState, get, modify)
import Effectful.Writer.Static.Local (listen, runWriter)
import System.Console.Haskeline (Settings, getInputLine, runInputT)
import System.IO (hPutStr, hPutStrLn, stderr)
import YCHR.Compile (buildFunctionSet, compileFunctionDef, funcProcName, genCallFunDispatches, tellProcName, vmName)
import YCHR.Compile.Pipeline (CompiledProgram (..), Error (..), ExportResolution (..), Warning (..), compileFiles, compileModules)
import YCHR.Desugar (desugarQueryGoals, liftQueryLambdas)
import YCHR.Desugared qualified as D
import YCHR.Display (Display (..))
import YCHR.Meta (valueToTerm)
import YCHR.PExpr (PExpr (Atom))
import YCHR.Parsed (SourceLoc (..))
import YCHR.Parser (parseConstraint, parseQueryWith)
import YCHR.Pretty (prettyQueryResult, prettyTerm)
import YCHR.Rename (renameQueryArgs, renameQueryGoals)
import YCHR.Runtime.History (runPropHistory)
import YCHR.Runtime.Interpreter (HostCallFn (..), HostCallRegistry, callProc)
import YCHR.Runtime.Reactivation (drainQueue, enqueue, runReactQueue)
import YCHR.Runtime.Session
  ( CHR,
    CHREffects,
    ProcMap,
    StaticRep (CHRRep),
    runCHR,
    tellConstraint,
    withCHR,
    withCHRExtra,
  )
import YCHR.Runtime.Store (CHRStore, aliveConstraint, runCHRStore)
import YCHR.Runtime.Types (RuntimeVal (..), SuspensionId, Value (..))
import YCHR.Runtime.Var (Unify, deref, equal, newVar, runUnify, unify)
import YCHR.TypeCheck (typeCheckGoals)
import YCHR.Types (Constraint (..), ConstraintType, Term (..))
import YCHR.Types qualified as Types
import YCHR.VM (Name (..), Procedure (..), Program (..), StackFrame)

-- | Runtime call stack for error reporting (newest first).
-- Re-exported here for use in this module's existing helpers.
type CallStack = [StackFrame]

-- ---------------------------------------------------------------------------
-- Single-goal API
-- ---------------------------------------------------------------------------

-- | Resolve a query constraint against the export map.
resolveQueryConstraint :: CompiledProgram -> Constraint -> Either String Constraint
resolveQueryConstraint cp (Constraint cname cargs) = case cname of
  Types.Unqualified n ->
    let arity = length cargs
     in case Map.lookup (Types.UnqualifiedIdentifier n arity) cp.exportMap of
          Just (UniqueExport qname) ->
            Right (Constraint qname cargs)
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
          then Right (Constraint cname cargs)
          else Left ("Constraint not exported: " ++ T.unpack m ++ ":" ++ T.unpack n ++ "/" ++ show arity)

-- | Run a single CHR constraint against a compiled program.
runProgramWithGoalDSL :: CompiledProgram -> HostCallRegistry -> Constraint -> IO (RuntimeVal, Map Text Term)
runProgramWithGoalDSL cp hostCalls constraint = do
  resolved <- case resolveQueryConstraint cp constraint of
    Left err -> fail err
    Right c -> pure c
  let prog = cp.program
      procMap = Map.fromList [(p.name, p) | p <- prog.procedures]
      tellName = tellProcName resolved.name (length resolved.args)
  unless (Map.member tellName procMap) $
    fail ("Constraint not found: " ++ T.unpack tellName.unName)
  runEff
    . runUnify
    . fmap fst
    . runWriter @[SuspensionId]
    . runCHRStore prog.typeNames
    . runPropHistory
    . runReactQueue
    . evalState @CallStack []
    . evalState (Map.empty :: Map Text Value)
    $ do
      argVals <- traverse termToValue resolved.args
      result <- callProc procMap hostCalls tellName (map RVal argVals)
      varMap <- get
      bindings <- Map.traverseWithKey valueToTerm varMap
      pure (result, bindings)

-- | Like 'runProgramWithGoalDSL' but accepts a query as surface-language 'Text'.
runProgramWithGoal :: CompiledProgram -> HostCallRegistry -> Text -> IO (RuntimeVal, Map Text Term)
runProgramWithGoal cp hostCalls src =
  case parseConstraint "<query>" src of
    Left err -> throwIO (ParseError "<query>" err)
    -- Rename the constraint's arguments so that bare data-constructor
    -- references (e.g. @[H|T]@, declared atoms) get canonicalized to
    -- the same flat-functor form the compiled head patterns expect.
    Right (Constraint cname cargs) -> do
      (renamedArgs, _warnings) <- either (throwIO . RenameErrors) pure (renameQueryArgs cp.allModules cargs)
      -- Canonicalize the constraint name via the export map so the
      -- type-check sees the same qualified name 'tellConstraintSigs'
      -- registers. Defer name-resolution failures to 'runProgramWithGoalDSL'
      -- (which produces a clearer "constraint not found" error).
      let renamed = case resolveQueryConstraint cp (Constraint cname renamedArgs) of
            Right c -> c
            Left _ -> Constraint cname renamedArgs
      tcErrs <- typeCheckGoals cp.desugaredProgram (SourceLoc "<query>" 1 1) (Just "query") [D.BodyConstraint renamed]
      unless (null tcErrs) (throwIO (TypeErrors tcErrs))
      runProgramWithGoalDSL cp hostCalls renamed

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

-- | Parse, rename, desugar, lambda-lift, and type-check a query. Throws
-- the appropriate 'Error' constructor on failure.
prepareQuery :: CompiledProgram -> Text -> IO PreparedQuery
prepareQuery cp src = do
  goals <- either (throwIO . ParseError "<query>") pure (parseQueryWith cp.opTable "<query>" src)
  (renamed, _renameWarnings) <- either (throwIO . RenameErrors) pure (renameQueryGoals cp.allModules goals)
  bodyGoals <- either (throwIO . DesugarErrors) pure (desugarQueryGoals cp.functionNameSet renamed)
  -- Lambda-lift query body goals and compile the generated functions
  let queryLoc = SourceLoc "<query>" 1 1
  (lifted, lambdas) <- either (throwIO . DesugarErrors) pure (liftQueryLambdas cp.nextLambdaIndex queryLoc (Atom "") bodyGoals)
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
  pure
    PreparedQuery
      { liftedGoals = lifted,
        queryLambdas = lambdas,
        extraProcs = queryProcs ++ queryDispatches
      }

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
runProgramWithQuery :: CompiledProgram -> HostCallRegistry -> Text -> IO (Map Text Term)
runProgramWithQuery cp hostCalls src = do
  prep <- prepareQuery cp src
  withCHRExtra cp hostCalls prep.extraProcs $
    executePreparedQuery hostCalls prep.liftedGoals

-- ---------------------------------------------------------------------------
-- Live REPL session
-- ---------------------------------------------------------------------------

-- | Outcome of executing a single live-session query.
data QueryOutcome
  = -- | Query ran to completion. Carries the resulting bindings.
    QueryOk (Map Text Term)
  | -- | A pre-execution problem (parse, type, lambdas-rejected) that
    -- left the constraint store untouched. The session can continue.
    QueryRecoverable String
  | -- | A runtime exception thrown during goal execution. The store
    -- and bindings may be inconsistent; the live session must abort.
    QueryFatal String

-- | Run an interactive live session against a compiled program. A single
-- 'withCHR' call wraps the whole session, so the constraint store,
-- propagation history, and reactivation queue persist across queries
-- entered at the @ychr live>@ prompt. The session ends when the user
-- types @:end@, hits EOF, or a runtime error aborts execution.
runLiveSession ::
  CompiledProgram ->
  HostCallRegistry ->
  Settings IO ->
  -- | Quiet mode (suppress prompt rendering).
  Bool ->
  IO ()
runLiveSession cp hostCalls settings quiet = withCHR cp hostCalls liveLoop
  where
    prompt = if quiet then "" else "ychr live> "
    liveLoop :: (CHREffects es) => Eff es ()
    liveLoop = do
      mline <- liftIO (runInputT settings (getInputLine prompt))
      case mline of
        Nothing -> pure ()
        Just line -> dispatchLine line
    dispatchLine :: (CHREffects es) => String -> Eff es ()
    dispatchLine line
      | stripped == ":end" = pure ()
      | T.null stripped = liveLoop
      | otherwise = do
          outcome <- handleLiveQuery cp hostCalls (T.pack line)
          case outcome of
            QueryOk bindings -> do
              liftIO (putStr (prettyQueryResult bindings))
              liveLoop
            QueryRecoverable msg -> do
              liftIO (hPutStr stderr msg)
              liveLoop
            QueryFatal msg -> liftIO $ do
              hPutStr stderr msg
              hPutStrLn stderr "live session aborted due to runtime error."
      where
        stripped = T.strip (T.pack line)

-- | Handle one query inside an existing live session: parse / typecheck
-- in 'IO' (catching 'Error'), reject lifted lambdas (live sessions
-- cannot grow the procedure map), then execute and catch any runtime
-- exception as a fatal outcome.
handleLiveQuery ::
  (CHREffects es) =>
  CompiledProgram ->
  HostCallRegistry ->
  Text ->
  Eff es QueryOutcome
handleLiveQuery cp hostCalls src = do
  prepResult <- liftIO (try @SomeException (prepareQuery cp src))
  case prepResult of
    Left exc -> pure (classifyAsRecoverable exc)
    Right prep
      | not (null prep.queryLambdas) ->
          pure (QueryRecoverable (displayMsg LambdasInLiveQuery))
      | otherwise -> do
          execResult <- Eff.try @SomeException (executePreparedQuery hostCalls prep.liftedGoals)
          case execResult of
            Left exc -> pure (QueryFatal (renderFatal exc))
            Right bindings -> pure (QueryOk bindings)
  where
    classifyAsRecoverable exc = case fromException exc :: Maybe Error of
      Just err -> QueryRecoverable (displayMsg err)
      Nothing -> QueryFatal (renderFatal exc)
    renderFatal exc = displayException exc ++ "\n"

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
  _ <- hostCall (Map.lookup (Name f) hc) f (map RVal argVals)
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
  tellConstraint c.name argVals
executeBodyGoal hc (D.BodyFunctionCall (Types.Unqualified "$call") args) = do
  CHRRep procMap _ _ _ <- getStaticRep
  argVals <- traverse termToValue args
  let n = length args - 1
      dispatchName = Name ("call_" <> T.pack (show n))
  _ <- callProc procMap hc dispatchName (map RVal argVals)
  pure ()
executeBodyGoal hc (D.BodyFunctionCall name args) = do
  CHRRep procMap _ _ _ <- getStaticRep
  argVals <- traverse termToValue args
  _ <- callProc procMap hc (funcProcName name (length argVals)) (map RVal argVals)
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
hostCall :: (Unify :> es, CHRStore :> es, IOE :> es) => Maybe HostCallFn -> Text -> [RuntimeVal] -> Eff es RuntimeVal
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
        callProc procMap hc (Name "reactivate_dispatch") [RConstraint sid]

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
      result <- callProc procMap hc dispatchName (map RVal argVals)
      case result of
        RVal val -> pure val
        _ -> error "call returned non-value"
evalNestedExpr _ (CompoundTerm (Types.Unqualified "term") [arg]) =
  termToValue arg
evalNestedExpr hc (CompoundTerm (Types.Qualified "host" f) args) = do
  argVals <- traverse (evalNestedExpr hc) args
  result <- hostCall (Map.lookup (Name f) hc) f (map RVal argVals)
  case result of
    RVal val -> pure val
    _ -> error "host call returned non-value in expression position"
evalNestedExpr hc (CompoundTerm name args) = do
  CHRRep procMap _ _ _ <- getStaticRep
  let fnName = funcProcName name (length args)
  if Map.member fnName procMap
    then do
      argVals <- traverse (evalNestedExpr hc) args
      result <- callProc procMap hc fnName (map RVal argVals)
      case result of
        RVal val -> pure val
        _ -> error "function call returned non-value in expression position"
    else VTerm (vmName name).unName <$> traverse termToValue args

-- | Compile lifted lambda functions for use in queries.
compileQueryLambdas :: Set Types.Identifier -> [D.Function] -> [Procedure]
compileQueryLambdas funSet lambdas =
  let (procs, _errs) = runPureEff . runWriter $ traverse (compileFunctionDef funSet) lambdas
   in procs
