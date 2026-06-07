{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Haskell interpreter for CHR VM programs.
--
-- Executes VM programs directly using the 'Chr' runtime monad. The
-- 'Chr' monad reads a 'SessionEnv' that bundles the constraint store,
-- propagation history, reactivation queue, unification-variable
-- counter, interpreter call stack, the procedure map and the host-call
-- registry. Per-procedure-call local variables ('Env') live in a
-- mutable 'IORef' read through a thin 'ReaderT' layer so exception-driven
-- non-local jumps preserve state across catches.
--
-- Non-local control flow ('Return', labelled 'Continue', 'Break') is
-- implemented with real 'Control.Exception' exceptions thrown in 'IO':
-- 'try' delimits each procedure invocation and each 'Foreach' body.
module YCHR.Runtime.Interpreter
  ( -- * Public API
    interpret,
    HostCallFn (..),
    HostCallRegistry,
    baseHostCallRegistry,

    -- * Deep-eval walker (shared with the query-time evaluator)
    deepEvalValue,

    -- * Tracing helpers (shared with the query-time driver)
    emitTrace,
    snapshotValue,
    snapshotValues,
    suspensionView,
    constraintTypeLabel,
    lookupRuleName,

    -- * Internal (for testing)
    callProc,
    bindParams,
    unit,
  )
where

import Control.Exception
  ( Exception,
    SomeAsyncException,
    SomeException,
    bracket,
    displayException,
    fromException,
    throwIO,
    try,
  )
import Control.Monad (unless)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ReaderT, ask, runReaderT)
import Data.Foldable (toList, traverse_)
import Data.IORef
  ( IORef,
    atomicModifyIORef',
    modifyIORef',
    newIORef,
    readIORef,
    writeIORef,
  )
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Meta (valueToTerm)
import YCHR.Pretty (prettyTerm)
import YCHR.Runtime.Error (RuntimeErrorThrown, runtimeError', runtimeErrorS)
import YCHR.Runtime.History (addHistory, notInHistory)
import YCHR.Runtime.Monad
  ( Chr,
    HostCallFn (..),
    HostCallRegistry,
    SessionEnv (..),
    initSessionEnv,
    runChr,
  )
import YCHR.Runtime.Reactivation (drainQueue, enqueue)
import YCHR.Runtime.Registry
  ( baseHostCallRegistry,
    unit,
  )
import YCHR.Runtime.Store
  ( Suspension (..),
    aliveConstraint,
    createConstraint,
    getConstraintArg,
    getConstraintType,
    getStoreSnapshot,
    idEqual,
    isConstraintType,
    isSuspAlive,
    killConstraint,
    lookupSusp,
    storeConstraint,
    suspArg,
  )
import YCHR.Runtime.Trace (TraceEvent (..))
import YCHR.Runtime.Types (CallVal (..), SuspensionId, Value (..))
import YCHR.Runtime.Var
  ( deref,
    equal,
    getArg,
    makeTerm,
    matchTerm,
    newVar,
    unify,
  )
import YCHR.Types (Term)
import YCHR.Types qualified as Types
import YCHR.VM

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

-- | Local variable environment for a procedure call. Split by kind:
-- value-bound names live in 'envValues', id-bound names in 'envIds'.
-- The IR ensures each name appears in only one map.
data Env = Env
  { envValues :: !(Map Name Value),
    envIds :: !(Map Name SuspensionId)
  }

emptyEnv :: Env
emptyEnv = Env Map.empty Map.empty

insertVal :: Name -> Value -> Env -> Env
insertVal n v e = e {envValues = Map.insert n v e.envValues}

insertId :: Name -> SuspensionId -> Env -> Env
insertId n s e = e {envIds = Map.insert n s e.envIds}

-- | Maximum number of call stack frames to keep.
maxCallStackDepth :: Int
maxCallStackDepth = 10

-- | Non-local control flow signals. Thrown as exceptions to escape
-- the current procedure or 'Foreach' loop and caught at the matching
-- boundary. 'CFReturn' is caught by 'callProc'; 'CFContinue' / 'CFBreak'
-- by 'execForeach' on its labelled loop.
data ControlFlow
  = CFReturn Value
  | CFContinue Label
  | CFBreak Label

instance Show ControlFlow where
  show (CFReturn _) = "CFReturn <val>"
  show (CFContinue l) = "CFContinue " ++ T.unpack l.unLabel
  show (CFBreak l) = "CFBreak " ++ T.unpack l.unLabel

instance Exception ControlFlow

-- | The interpreter's local stack: an 'IORef Env' threaded above 'Chr'.
-- Using a ref lets exception-driven jumps preserve any state changes
-- made before the jump, matching the original effectful-static-Local
-- 'runError'-with-outer-state semantics.
type InterpM = ReaderT (IORef Env) Chr

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

-- | Interpret a VM program by calling a named procedure with the given
-- value arguments. Builds a fresh 'SessionEnv' for the program and
-- runs the call inside it.
interpret :: Program -> HostCallRegistry -> Name -> [Value] -> IO Value
interpret prog hostCalls entryName args = do
  let procMap = Map.fromList [(p.name, p) | p <- prog.procedures]
      evaluableMap = Map.fromList prog.evaluables
  env <-
    initSessionEnv
      prog.typeNames
      prog.ruleNames
      procMap
      hostCalls
      evaluableMap
      Map.empty
      mempty
  runChr (callProc entryName (map CVal args)) env

-- ---------------------------------------------------------------------------
-- Env helpers
-- ---------------------------------------------------------------------------

getEnv :: InterpM Env
getEnv = do
  ref <- ask
  liftIO (readIORef ref)

modifyEnv :: (Env -> Env) -> InterpM ()
modifyEnv f = do
  ref <- ask
  liftIO (modifyIORef' ref f)

withFreshEnv :: Env -> InterpM a -> Chr a
withFreshEnv env action = do
  ref <- liftIO (newIORef env)
  runReaderT action ref

-- ---------------------------------------------------------------------------
-- Session helpers
-- ---------------------------------------------------------------------------

lookupProc :: Name -> Chr (Maybe Procedure)
lookupProc name = do
  SessionEnv {procMap} <- ask
  pm <- liftIO (readIORef procMap)
  pure (Map.lookup name pm)

lookupHostCall :: Name -> Chr (Maybe HostCallFn)
lookupHostCall name = do
  SessionEnv {hostCalls} <- ask
  pure (Map.lookup name hostCalls)

pushFrame :: StackFrame -> Chr ()
pushFrame frame = do
  SessionEnv {callStack} <- ask
  liftIO $
    atomicModifyIORef' callStack $ \stack ->
      (take maxCallStackDepth (frame : stack), ())

-- | Save the call stack, run @action@, and restore the saved frames
-- on the way out — whether @action@ returns normally or throws. The
-- restore-on-throw matters because the REPL's outer @try@ may catch
-- a 'RuntimeErrorThrown' that escapes a procedure call; without
-- bracketing, frames pushed during the failed call would leak into
-- the next operation that observes the same 'SessionEnv'.
withSavedCallStack :: Chr a -> Chr a
withSavedCallStack action = do
  env@SessionEnv {callStack} <- ask
  liftIO $
    bracket
      (readIORef callStack)
      (writeIORef callStack)
      (\_ -> runChr action env)

-- | Catch a 'ControlFlow' exception thrown inside a 'Chr' action.
-- Uses 'try' at the 'IO' layer so the action's state changes (in
-- 'SessionEnv' refs and in any 'InterpM' env ref currently in scope)
-- survive the catch.
tryControlFlow :: Chr a -> Chr (Either ControlFlow a)
tryControlFlow m = do
  env <- ask
  liftIO (try (runChr m env))

-- ---------------------------------------------------------------------------
-- Tracing helpers
-- ---------------------------------------------------------------------------

-- | Emit a 'TraceEvent' if a handler is installed. The event is built
-- lazily — when tracing is off, the action passed in is not run, so
-- callers can place expensive snapshotValues (e.g. 'valueToTerm' walks)
-- inside it without paying the cost when tracing is disabled.
emitTrace :: Chr TraceEvent -> Chr ()
emitTrace mkEv = do
  env <- ask
  mh <- liftIO (readIORef env.traceHandler)
  case mh of
    Nothing -> pure ()
    Just h -> do
      ev <- mkEv
      depth <- liftIO (readIORef env.traceDepth)
      liftIO (h depth ev)
{-# INLINE emitTrace #-}

-- | Run @action@ at depth @depth + 1@, restoring the previous depth
-- on the way out (including on exception). No-op when tracing is off.
withTraceDepth :: Chr a -> Chr a
withTraceDepth action = do
  env <- ask
  mh <- liftIO (readIORef env.traceHandler)
  case mh of
    Nothing -> action
    Just _ -> do
      let depthRef = env.traceDepth
      liftIO $
        bracket
          (atomicModifyIORef' depthRef (\d -> (d + 1, ())))
          (\() -> atomicModifyIORef' depthRef (\d -> (d - 1, ())))
          (\() -> runChr action env)

-- | Snapshot a 'Value' as a 'Term' for inclusion in a trace event.
-- Wraps 'valueToTerm' with an empty alias map — trace events do not
-- need the per-query alias-class machinery; raw variable names are
-- fine for inspection.
snapshotValue :: Value -> Chr Term
snapshotValue = valueToTerm Map.empty

snapshotValues :: [Value] -> Chr [Term]
snapshotValues = traverse snapshotValue

-- | Look up a suspension by id and return its constraint-type and
-- argument values. Used by trace-event builders that need both.
suspensionView :: SuspensionId -> Chr (ConstraintType, [Value])
suspensionView sid = do
  susp <- lookupSusp sid
  pure (susp.suspType, susp.args)

-- | Look up a rule's display name from the session-cached
-- 'ruleNames' table. Falls back to @__rule_N@ on miss.
lookupRuleName :: SessionEnv -> RuleId -> Text
lookupRuleName env (RuleId i) =
  case IntMap.lookup i env.ruleNames of
    Just n -> n
    Nothing -> T.pack ("__rule_" ++ show i)

-- ---------------------------------------------------------------------------
-- Core interpreter
-- ---------------------------------------------------------------------------

-- | Call a procedure. Creates a fresh local 'Env' with parameter
-- bindings, executes the body, and catches 'CFReturn'. Default
-- return: 'VBool False'. Emits trace events at entry (and on return
-- for user functions / lambdas) when tracing is on; uses the
-- procedure's 'procKind' tag to label the event and decide whether
-- to bump the trace indentation.
callProc :: Name -> [CallVal] -> Chr Value
callProc name args = do
  mproc <- lookupProc name
  case mproc of
    Nothing -> runtimeError' "callProc: unknown procedure " name.unName
    Just proc -> do
      env <- case bindParams name proc.params args of
        Right e -> pure e
        Left msg -> runtimeErrorS msg
      traceEntry proc args
      let runBody = withSavedCallStack $ do
            result <- tryControlFlow (withFreshEnv env (execStmts proc.body))
            case result of
              Right () -> pure (VBool False)
              Left (CFReturn v) -> pure v
              Left (CFContinue l) -> runtimeError' "callProc: uncaught Continue " l.unLabel
              Left (CFBreak l) -> runtimeError' "callProc: uncaught Break " l.unLabel
      result <-
        if bumpDepthFor proc.procKind
          then withTraceDepth runBody
          else runBody
      traceExit proc.procKind result
      pure result

-- | Should entering a procedure of this kind increase trace
-- indentation? Tells, activates, occurrences, reactivate-dispatch,
-- and user functions/lambdas do; the @$call@ dispatcher is a thin
-- router and would just add noise.
bumpDepthFor :: ProcKind -> Bool
bumpDepthFor PKTell {} = True
bumpDepthFor PKActivate {} = True
bumpDepthFor PKOccurrence {} = True
bumpDepthFor PKReactivateDispatch = True
bumpDepthFor PKFunction {} = True
bumpDepthFor PKCallDispatch {} = False

-- | Emit the entry-time event for a procedure call, if tracing is on.
-- Reactivation events are emitted at the per-suspension boundary
-- inside 'DrainReactivationQueue' (where the constraint id is in
-- hand), not here.
traceEntry :: Procedure -> [CallVal] -> Chr ()
traceEntry proc args = case proc.procKind of
  PKTell ct -> emitTrace $ do
    ctName <- constraintTypeLabel ct
    ts <- snapshotValues [v | CVal v <- args]
    pure (TETell ctName ts)
  PKActivate _ -> emitTrace $ do
    let sid = activateSuspensionId args
    (ct, vs) <- suspensionView sid
    ctName <- constraintTypeLabel ct
    ts <- snapshotValues vs
    pure (TEActivate ctName sid ts)
  PKOccurrence ct n _ display -> emitTrace $ do
    ctName <- constraintTypeLabel ct
    pure (TETryOccurrence ctName n display)
  PKReactivateDispatch -> pure ()
  PKCallDispatch _ -> pure ()
  PKFunction qn _ -> emitTrace $ do
    let fname = Types.flattenName (Types.qualifiedToName qn)
    ts <- snapshotValues [v | CVal v <- args]
    pure (TECallFunction fname ts)

-- | Emit a 'TEReturn' event for procedures whose return value is
-- user-meaningful: user functions and lambdas. The framework
-- procedures (tell / activate / occurrence) return a boolean control
-- flag that has no surface meaning; the depth dedent alone makes
-- their completion visible.
traceExit :: ProcKind -> Value -> Chr ()
traceExit (PKFunction _ _) v = emitTrace $ do
  t <- snapshotValue v
  pure (TEReturn t)
traceExit _ _ = pure ()

-- | Render a 'ConstraintType' as its source name using the session's
-- 'storeTypeNames' table. Falls back to @c#type_N@ when the type is
-- unknown (which should never happen for compiler-generated code).
constraintTypeLabel :: ConstraintType -> Chr Text
constraintTypeLabel ct = do
  env <- ask
  let i = ct.unConstraintType
  case IntMap.lookup i env.storeTypeNames of
    Just name -> pure (Types.flattenName name)
    Nothing -> pure (T.pack ("c#type_" ++ show i))

-- | Pull the leading suspension id out of an activate / occurrence /
-- reactivate-dispatch procedure's argument list. The compiler always
-- emits the id as the first parameter.
activateSuspensionId :: [CallVal] -> SuspensionId
activateSuspensionId (CId s : _) = s
activateSuspensionId _ = error "activateSuspensionId: expected leading id argument"

-- | Bind procedure parameters into the appropriate environment slot
-- based on the runtime tag of each argument.
bindParams :: Name -> [Name] -> [CallVal] -> Either String Env
bindParams pname params args
  | length params /= length args =
      Left $
        "bindParams: arity mismatch in "
          ++ T.unpack pname.unName
          ++ ": "
          ++ show (length params)
          ++ " params, "
          ++ show (length args)
          ++ " args"
  | otherwise = Right (foldl' step emptyEnv (zip params args))
  where
    step e (p, CVal v) = insertVal p v e
    step e (p, CId s) = insertId p s e

-- | Execute a list of statements sequentially.
execStmts :: [Stmt] -> InterpM ()
execStmts = traverse_ execStmt

-- | Execute a single statement. Mutates the local 'Env' for binders,
-- delegates control-flow stmts to the throw-and-catch machinery, and
-- routes store / history / reactivation effects through 'Chr'.
execStmt :: Stmt -> InterpM ()
execStmt (LetVal name expr) = do
  v <- evalValExpr expr
  modifyEnv (insertVal name v)
execStmt (LetId name expr) = do
  s <- evalIdExpr expr
  modifyEnv (insertId name s)
execStmt (AssignVal name expr) = do
  v <- evalValExpr expr
  modifyEnv (insertVal name v)
execStmt (AssignId name expr) = do
  s <- evalIdExpr expr
  modifyEnv (insertId name s)
execStmt (If cond thenBranch elseBranch) = do
  b <- evalBoolExpr cond
  if b then execStmts thenBranch else execStmts elseBranch
execStmt (Foreach lbl cType suspVar conditions body) = do
  snapshot <- lift (getStoreSnapshot cType)
  let susps = toList snapshot
  execForeach lbl suspVar conditions body susps
execStmt (Continue lbl) = liftIO (throwIO (CFContinue lbl))
execStmt (Break lbl) = liftIO (throwIO (CFBreak lbl))
execStmt (Return expr) = do
  v <- evalValExpr expr
  liftIO (throwIO (CFReturn v))
execStmt (ExprStmt expr) = do
  _ <- evalValExpr expr
  pure ()
execStmt (BoolExprStmt expr) = do
  _ <- evalBoolExpr expr
  pure ()
execStmt (Store expr) = do
  sid <- evalIdExpr expr
  lift $ do
    storeConstraint sid
    emitTrace $ do
      (ct, vs) <- suspensionView sid
      ctName <- constraintTypeLabel ct
      ts <- snapshotValues vs
      pure (TEStore sid ctName ts)
execStmt (Kill expr) = do
  sid <- evalIdExpr expr
  lift $ do
    killConstraint sid
    emitTrace (pure (TEKill sid))
execStmt (AddHistory ruleId exprs) = do
  sids <- traverse evalIdExpr exprs
  lift $ do
    emitTrace $ do
      env <- ask
      let rn = lookupRuleName env ruleId
      pure (TEFire rn sids)
    addHistory ruleId sids
execStmt (DrainReactivationQueue suspVar body) = do
  envRef <- ask
  lift $
    drainQueue $ \sid -> do
      alive <- aliveConstraint sid
      if alive
        then do
          emitTrace $ do
            (ct, vs) <- suspensionView sid
            ctName <- constraintTypeLabel ct
            ts <- snapshotValues vs
            pure (TEReactivate sid ctName ts)
          liftIO (modifyIORef' envRef (insertId suspVar sid))
          runReaderT (execStmts body) envRef
        else pure ()
execStmt (PushFrame frame) = lift (pushFrame frame)

-- ---------------------------------------------------------------------------
-- Foreach implementation
-- ---------------------------------------------------------------------------

-- | Iterate the body of a 'Foreach' over a snapshot of candidate
-- suspensions. Dead suspensions and suspensions failing the index
-- conditions are skipped without entering the body. Labelled
-- 'CFContinue' / 'CFBreak' are caught here; non-matching labels and
-- 'CFReturn' propagate to the next outer handler.
execForeach ::
  Label ->
  Name ->
  [(ArgIndex, ValExpr)] ->
  [Stmt] ->
  [Suspension] ->
  InterpM ()
execForeach _ _ _ _ [] = pure ()
execForeach lbl suspVar conditions body (susp : rest) = do
  alive <- lift (isSuspAlive susp)
  if not alive
    then execForeach lbl suspVar conditions body rest
    else do
      ok <- checkConditions susp conditions
      if not ok
        then execForeach lbl suspVar conditions body rest
        else do
          lift $ emitTrace $ do
            ctName <- constraintTypeLabel susp.suspType
            ts <- snapshotValues susp.args
            pure (TEPartner ctName susp.suspId ts)
          modifyEnv (insertId suspVar susp.suspId)
          envRef <- ask
          result <- lift (withTraceDepth (tryControlFlow (runReaderT (execStmts body) envRef)))
          case result of
            Right () -> execForeach lbl suspVar conditions body rest
            Left (CFContinue l)
              | l == lbl -> execForeach lbl suspVar conditions body rest
              | otherwise -> liftIO (throwIO (CFContinue l))
            Left (CFBreak l)
              | l == lbl -> pure ()
              | otherwise -> liftIO (throwIO (CFBreak l))
            Left cf@(CFReturn _) -> liftIO (throwIO cf)

checkConditions :: Suspension -> [(ArgIndex, ValExpr)] -> InterpM Bool
checkConditions _ [] = pure True
checkConditions susp ((ArgIndex i, expr) : rest) = do
  v <- evalValExpr expr
  let argVal = suspArg susp i
  eq <- lift (equal v argVal)
  if eq
    then checkConditions susp rest
    else pure False

-- ---------------------------------------------------------------------------
-- Value-expression evaluator (normal mode)
-- ---------------------------------------------------------------------------

-- | Evaluate a 'ValExpr' in normal (non-deep) mode. Variable references
-- return whatever value is currently bound; chains are not followed.
-- 'EvalDeep' delegates to 'evalValExprDeep'.
evalValExpr :: ValExpr -> InterpM Value
evalValExpr (Var name) = do
  env <- getEnv
  case Map.lookup name env.envValues of
    Just v -> pure v
    Nothing -> lift (runtimeError' "evalValExpr: unbound variable " name.unName)
evalValExpr (Lit (IntLit n)) = pure (VInt n)
evalValExpr (Lit (FloatLit n)) = pure (VFloat n)
evalValExpr (Lit (AtomLit s)) = pure (VAtom s)
evalValExpr (Lit (TextLit s)) = pure (VText s)
evalValExpr (Lit (BoolLit b)) = pure (VBool b)
evalValExpr (Lit WildcardLit) = pure VWildcard
evalValExpr (CallExpr name args) = do
  argVals <- traverse evalCallArg args
  lift (callProc name argVals)
evalValExpr (HostCall name args) = do
  argVals <- traverse evalValExpr args
  derefedVals <- lift (traverse deref argVals)
  lift (invokeHostCall name derefedVals)
evalValExpr NewVar = lift newVar
evalValExpr (MakeTerm functor args) = do
  argVals <- traverse evalValExpr args
  pure $ makeTerm functor.unName argVals
evalValExpr (GetArg expr idx) = do
  v <- evalValExpr expr
  lift (getArg v idx)
evalValExpr (FieldArg expr (ArgIndex i)) = do
  sid <- evalIdExpr expr
  lift (getConstraintArg sid i)
evalValExpr (FieldType expr) = do
  sid <- evalIdExpr expr
  ct <- lift (getConstraintType sid)
  pure (VInt (fromIntegral ct.unConstraintType))
evalValExpr (EvalDeep expr) = evalValExprDeep expr
-- 'EvalIs' is the @is@-with-variable-RHS marker. The compiler only
-- emits it for @R is X@ where @X@ is syntactically a variable; the
-- inner expression is therefore always a 'Var'. We evaluate that
-- 'Var', dereference, and then walk the resulting value with
-- 'deepEvalValue' so a bound compound whose functor is a declared
-- function actually evaluates (matching SWI Prolog's @is@ on a
-- variable). Other 'EvalDeep' use sites (guards, non-variable @is@
-- RHSes) do not invoke the walker.
evalValExpr (EvalIs expr) = do
  v <- evalValExprDeep expr
  lift (deepEvalValue v)

-- ---------------------------------------------------------------------------
-- Bool-expression evaluator (normal mode)
-- ---------------------------------------------------------------------------

-- | Evaluate a 'BoolExpr' in normal (non-deep) mode. Logical connectives
-- short-circuit. 'BEvalDeep' delegates to 'evalBoolExprDeep'.
evalBoolExpr :: BoolExpr -> InterpM Bool
evalBoolExpr (BLit b) = pure b
evalBoolExpr (BNot e) = not <$> evalBoolExpr e
evalBoolExpr (BAnd e1 e2) = do
  b1 <- evalBoolExpr e1
  if b1 then evalBoolExpr e2 else pure False
evalBoolExpr (BOr e1 e2) = do
  b1 <- evalBoolExpr e1
  if b1 then pure True else evalBoolExpr e2
evalBoolExpr (BMatchTerm expr functor arity) = do
  v <- evalValExpr expr
  lift (matchTerm v functor.unName arity)
evalBoolExpr (BEqual e1 e2) = do
  v1 <- evalValExpr e1
  v2 <- evalValExpr e2
  lift (equal v1 v2)
evalBoolExpr (BIdEqual e1 e2) = do
  s1 <- evalIdExpr e1
  s2 <- evalIdExpr e2
  pure (idEqual s1 s2)
evalBoolExpr (BAlive expr) = do
  sid <- evalIdExpr expr
  lift (aliveConstraint sid)
evalBoolExpr (BIsConstraintType expr cType) = do
  sid <- evalIdExpr expr
  lift (isConstraintType sid cType)
evalBoolExpr (BNotInHistory ruleId args) = do
  sids <- traverse evalIdExpr args
  ok <- lift (notInHistory ruleId sids)
  unless ok $
    lift $
      emitTrace $ do
        env <- ask
        let rn = lookupRuleName env ruleId
        pure (TEHistoryHit rn sids)
  pure ok
evalBoolExpr (BUnify e1 e2) = do
  v1 <- evalValExpr e1
  v2 <- evalValExpr e2
  lift $ do
    env <- ask
    mh <- liftIO (readIORef env.traceHandler)
    case mh of
      Nothing -> unifyOrError v1 v2
      Just _ -> do
        t1 <- snapshotValue v1
        t2 <- snapshotValue v2
        beforeLen <- liftIO (Seq.length <$> readIORef env.reactQueue)
        ok <- unifyOrError v1 v2
        afterLen <- liftIO (Seq.length <$> readIORef env.reactQueue)
        emitTrace (pure (TEUnify t1 t2 (afterLen - beforeLen)))
        pure ok
evalBoolExpr (BFromVal expr) = do
  v <- evalValExpr expr
  case v of
    VBool b -> pure b
    _ -> lift (runtimeErrorS "BFromVal: expected boolean")
evalBoolExpr (BEvalDeep expr) = evalBoolExprDeep expr

-- ---------------------------------------------------------------------------
-- Id-expression evaluator
-- ---------------------------------------------------------------------------

-- | Evaluate an 'IdExpr' to a 'SuspensionId': either a lookup in the
-- id slot of the local 'Env', or a fresh suspension created from a
-- 'CreateConstraint' (not yet 'Store'd).
evalIdExpr :: IdExpr -> InterpM SuspensionId
evalIdExpr (IdVar name) = do
  env <- getEnv
  case Map.lookup name env.envIds of
    Just s -> pure s
    Nothing -> lift (runtimeError' "evalIdExpr: unbound id variable " name.unName)
evalIdExpr (CreateConstraint cType args) = do
  argVals <- traverse evalValExpr args
  lift (createConstraint cType argVals)

-- ---------------------------------------------------------------------------
-- Call-arg evaluator
-- ---------------------------------------------------------------------------

evalCallArg :: CallArg -> InterpM CallVal
evalCallArg (AVal e) = CVal <$> evalValExpr e
evalCallArg (AId e) = CId <$> evalIdExpr e

-- ---------------------------------------------------------------------------
-- Host call dispatch
-- ---------------------------------------------------------------------------

-- | Dispatch a host call by name. Only synchronous, non-control-flow
-- exceptions thrown by the host body get wrapped as runtime errors:
-- 'ControlFlow' (interpreter-internal: Return/Continue/Break) and
-- async exceptions (Ctrl+C, thread kill) must keep their identity so
-- they reach their intended handler; 'RuntimeErrorThrown' is re-thrown
-- verbatim so nested host calls preserve the original message and
-- stack frames.
invokeHostCall :: Name -> [Value] -> Chr Value
invokeHostCall name argVals = do
  mfn <- lookupHostCall name
  case mfn of
    Just (HostCallFn f) -> do
      env <- ask
      result <- liftIO (try @SomeException (runChr (f argVals) env))
      case result of
        Right v -> do
          emitTrace $ do
            argTs <- snapshotValues argVals
            resT <- snapshotValue v
            pure (TECallHost name.unName argTs resT)
          pure v
        Left exc
          | Just (cf :: ControlFlow) <- fromException exc ->
              liftIO (throwIO cf)
          | Just (ae :: SomeAsyncException) <- fromException exc ->
              liftIO (throwIO ae)
          | Just (rte :: RuntimeErrorThrown) <- fromException exc ->
              liftIO (throwIO rte)
          | otherwise ->
              runtimeErrorS $
                "host call " ++ T.unpack name.unName ++ ": " ++ displayException exc
    Nothing -> runtimeError' "invokeHostCall: unknown host call " name.unName

-- | Unify two already-evaluated values (tell semantics). Enqueues
-- observers of any variables affected by the unification — including
-- on failure, where partial bindings may still have produced
-- observers worth reactivating. Raises a runtime error with both
-- operands pretty-printed when unification fails.
unifyOrError :: Value -> Value -> Chr Bool
unifyOrError v1 v2 = do
  (ok, observers) <- unify v1 v2
  enqueue observers
  if ok
    then pure True
    else do
      t1 <- valueToTerm Map.empty v1
      t2 <- valueToTerm Map.empty v2
      runtimeErrorS $
        "unification failure: cannot unify "
          ++ prettyTerm t1
          ++ " with "
          ++ prettyTerm t2

-- ---------------------------------------------------------------------------
-- Value-expression evaluator (deep deref mode)
-- ---------------------------------------------------------------------------

-- | Evaluate a value expression with automatic dereferencing: variable
-- references follow binding chains before use, and this mode propagates
-- into sub-expressions. Used to implement 'EvalDeep' (guards and @is@ RHS).
--
-- This evaluator dereferences 'Var' references once. The
-- 'EvalDeep' case at 'evalValExpr' is responsible for the additional
-- value-side walk that evaluates a dereferenced compound term —
-- it applies only when the outer 'EvalDeep' is a bare 'Var', so that
-- @R is X@ (RHS is a variable) walks @X@'s bound term but
-- @R is copy_term(term(X))@ (RHS is a host call) leaves @X@'s bound
-- compound symbolic for the host call's benefit. This intentionally
-- mirrors the type checker's rule: only @R is X@ widens the LHS to
-- @any@.
evalValExprDeep :: ValExpr -> InterpM Value
evalValExprDeep (Var name) = do
  v <- evalValExpr (Var name)
  lift (deref v)
evalValExprDeep (HostCall name args) = do
  argVals <- traverse evalValExprDeep args
  lift (invokeHostCall name argVals)
evalValExprDeep (CallExpr name args) = do
  argVals <- traverse evalCallArgDeep args
  lift (callProc name argVals)
evalValExprDeep (MakeTerm functor args) = do
  argVals <- traverse evalValExprDeep args
  pure $ makeTerm functor.unName argVals
evalValExprDeep expr = evalValExpr expr

-- | Walk a runtime 'Value', evaluating any compound subterm whose
-- @(functor, arity)@ names a declared host call or a compiled user
-- function. Atomic values pass through. Unbound variables are
-- dereferenced once and then re-walked, so a chain of bindings
-- ending in a compound triggers full evaluation. Functors that do
-- not name an evaluable declaration (constructors, undeclared
-- atoms, arity mismatches with the host-call registry) raise a
-- runtime error — mirroring SWI Prolog's @type_error(evaluable, F\/N)@.
--
-- 'MakeTerm' callers do /not/ funnel through this walker — the
-- @term/1@ quoting form must continue to produce the symbolic
-- compound it was asked to build.
deepEvalValue :: Value -> Chr Value
deepEvalValue v = do
  v' <- deref v
  case v' of
    VTerm functor args -> do
      args' <- traverse deepEvalValue args
      let key = EvaluableKey {functor = Name functor, arity = length args}
      invokeByKey key args'
    _ -> pure v'

-- | Dispatch a value-side deep-evaluation step: prefer a user-defined
-- function (resolved through the compiler-emitted 'evaluables' table),
-- fall back to the host-call registry, and raise a runtime error if
-- neither matches. The two-tier order lets a user shadow a prelude
-- host call by declaring a function of the same name and arity.
invokeByKey :: EvaluableKey -> [Value] -> Chr Value
invokeByKey key args = do
  SessionEnv {evaluables, hostCalls} <- ask
  case Map.lookup key evaluables of
    Just procName -> callProc procName (map CVal args)
    Nothing ->
      case Map.lookup key.functor hostCalls of
        Just _ -> invokeHostCall key.functor args
        Nothing ->
          runtimeError'
            "is: functor is not evaluable: "
            (key.functor.unName <> "/" <> T.pack (show key.arity))

evalCallArgDeep :: CallArg -> InterpM CallVal
evalCallArgDeep (AVal e) = CVal <$> evalValExprDeep e
evalCallArgDeep (AId e) = CId <$> evalIdExpr e

-- ---------------------------------------------------------------------------
-- Bool-expression evaluator (deep deref mode)
-- ---------------------------------------------------------------------------

-- | Deep-deref evaluation for 'BoolExpr'. Mirrors 'evalValExprDeep':
-- propagates deep mode into 'ValExpr' and 'IdExpr' payloads.
evalBoolExprDeep :: BoolExpr -> InterpM Bool
evalBoolExprDeep (BNot e) = not <$> evalBoolExprDeep e
evalBoolExprDeep (BAnd e1 e2) = do
  b1 <- evalBoolExprDeep e1
  if b1 then evalBoolExprDeep e2 else pure False
evalBoolExprDeep (BOr e1 e2) = do
  b1 <- evalBoolExprDeep e1
  if b1 then pure True else evalBoolExprDeep e2
evalBoolExprDeep (BMatchTerm expr functor arity) = do
  v <- evalValExprDeep expr
  lift (matchTerm v functor.unName arity)
evalBoolExprDeep (BEqual e1 e2) = do
  v1 <- evalValExprDeep e1
  v2 <- evalValExprDeep e2
  lift (equal v1 v2)
evalBoolExprDeep (BUnify e1 e2) = do
  v1 <- evalValExprDeep e1
  v2 <- evalValExprDeep e2
  lift (unifyOrError v1 v2)
evalBoolExprDeep (BFromVal expr) = do
  v <- evalValExprDeep expr
  case v of
    VBool b -> pure b
    _ -> lift (runtimeErrorS "BFromVal: expected boolean")
evalBoolExprDeep (BEvalDeep expr) = evalBoolExprDeep expr
evalBoolExprDeep expr = evalBoolExpr expr
