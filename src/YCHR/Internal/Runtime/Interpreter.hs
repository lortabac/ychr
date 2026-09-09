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
-- mutable 'IORef' read through a thin 'ReaderT' layer so state changes
-- survive the exception-driven catches that remain ('BSoftGuard').
--
-- Non-local control flow ('Return', labelled 'Continue', 'Break') is
-- implemented /without/ exceptions: statement execution returns an
-- explicit 'Signal', 'execStmts' short-circuits on a non-'SFall'
-- signal, 'execForeach' consumes the labels it owns, and 'callProc'
-- consumes 'SRet'. Only genuine errors ('RuntimeErrorThrown') and
-- asynchronous exceptions still unwind through 'IO'.
module YCHR.Internal.Runtime.Interpreter
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
  ( SomeException,
    bracket,
    displayException,
    throwIO,
    try,
  )
import Control.Monad (unless, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ReaderT, ask, runReaderT)
import Data.Foldable (toList)
import Data.IORef
  ( IORef,
    atomicModifyIORef',
    modifyIORef',
    newIORef,
    readIORef,
    writeIORef,
  )
import Data.IntMap.Strict qualified as IntMap
import Data.List qualified as List
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Meta (valueToTerm)
import YCHR.Internal.Pretty (prettyTerm)
import YCHR.Internal.Runtime.Error
  ( RuntimeErrorKind (..),
    RuntimeErrorThrown (..),
    instantiationErrorS,
    isControlException,
    runtimeError',
    runtimeErrorS,
  )
import YCHR.Internal.Runtime.History (addHistory, notInHistory)
import YCHR.Internal.Runtime.Monad
  ( Chr,
    HostCallFn (..),
    HostCallRegistry,
    SessionEnv (..),
    initSessionEnv,
    runChr,
  )
import YCHR.Internal.Runtime.Reactivation (drainQueue, enqueueObservers)
import YCHR.Internal.Runtime.Registry
  ( baseHostCallRegistry,
    isVar,
    unit,
  )
import YCHR.Internal.Runtime.Store
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
import YCHR.Internal.Runtime.Trace (TraceEvent (..))
import YCHR.Internal.Runtime.Types (CallVal (..), SuspensionId, Value (..))
import YCHR.Internal.Runtime.Var
  ( deref,
    equal,
    getArg,
    makeTerm,
    matchTerm,
    newVar,
    unify,
  )
import YCHR.Internal.Types (Term)
import YCHR.Internal.Types qualified as Types
import YCHR.Internal.VM

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

-- | How a statement (or a statement list) finished.
--
-- 'SFall' means "fell through to the next statement"; the other three
-- are the VM's non-local jumps. They are returned, not thrown:
-- 'execStmts' stops at the first non-'SFall' signal and hands it
-- outwards, 'execForeach' consumes the 'SCont' / 'SBrk' carrying its
-- own label, and 'callProc' consumes 'SRet'. A signal that reaches
-- 'callProc' without an owner is a compiler bug and becomes a runtime
-- error.
data Signal
  = SFall
  | SRet !Value
  | SCont !Label
  | SBrk !Label

-- | The interpreter's local stack: an 'IORef Env' threaded above 'Chr'.
-- Using a ref lets the state changes made before a 'BSoftGuard'
-- failure survive the catch, matching the original
-- effectful-static-Local 'runError'-with-outer-state semantics.
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
      prog.inertTypes
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

-- | Push a frame onto the session call stack. Deliberately does /not/
-- truncate: see 'maxCallStackDepth', which is applied where the stack
-- is read instead.
pushFrame :: StackFrame -> Chr ()
pushFrame frame = do
  SessionEnv {callStack} <- ask
  liftIO $ modifyIORef' callStack (frame :)

-- | Save the call stack, run @action@, and restore the saved frames
-- on the normal exit path.
--
-- The restore is /not/ exception-safe, on purpose: a @bracket@ here
-- costs a mask plus a handler frame on every single procedure call,
-- which is the interpreter's hottest path. What matters instead is
-- that every place which catches a 'RuntimeErrorThrown' and keeps
-- using the same 'SessionEnv' restores the stack itself:
--
--   * 'catchInstantiation' (backing 'BSoftGuard') snapshots and
--     restores around its own @try@. This is the only catch that
--     genuinely resumes execution in the same session, so it is the
--     only one where the restore is load-bearing.
--   * @YCHR.Run.convertRuntimeErrorChr@ restores at the query
--     boundary, as defence in depth — see its own note.
--   * @YCHR.Internal.Runtime.Search.hostRunChrSession@ needs
--     nothing: the forked session has its own @callStack@ ref.
--
-- Everywhere else a caught runtime error ends the session outright.
-- An asynchronous exception may leave frames behind, but the
-- computation it interrupts is dying anyway.
withSavedCallStack :: Chr a -> Chr a
withSavedCallStack action = do
  SessionEnv {callStack} <- ask
  saved <- liftIO (readIORef callStack)
  r <- action
  liftIO (writeIORef callStack saved)
  pure r

{- Note [Soft guard catch safety]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
'catchInstantiation' turns an instantiation failure raised anywhere
inside a rule-occurrence guard into 'False'. Swallowing an exception is
only sound because of three properties of that position:

  * Guard residuals do not tell (see dev-docs/INVARIANTS.md §4). No
    'BUnify', 'Store', 'Kill' or 'AddHistory' is reachable from a
    guard — not directly, and not through a called function, whose
    body has no tell forms either. So a guard abandoned half-way
    leaves the store, the propagation history and the reactivation
    queue exactly as it found them. There is nothing to undo.

    This covers the runtime's own bookkeeping, which is what the catch
    depends on. It does not cover a 'HostCall' in the guard: a host
    function gets the session and can bind shared logical-variable
    cells, and @run_chr_session\/1@ does. But such a binding survives a
    guard that merely evaluates to 'False' just the same, so the catch
    adds no exposure that guard failure did not already have.

  * The call stack is restored. 'withSavedCallStack' only restores on
    the normal exit path, so 'catchInstantiation' snapshots and
    restores the stack around its own @try@; the frames pushed by a
    guard call that threw are gone by the time the handler returns.

  * The propagation history is untouched. 'AddHistory' is emitted
    inside the fire block, after the guard, so a soft-failed guard
    leaves nothing that would block the retry after reactivation.

'run_chr_session' keeps its own, wider boundary: it runs an isolated
sub-session and maps every failure to 'False', rolling the sub-session
back as it does. That is unrelated to this catch and unaffected by it.
-}

-- | Evaluate a boolean action under a soft-failure boundary: an
-- 'InstantiationError' becomes 'False' and every other runtime error
-- propagates. Backs the 'BSoftGuard' VM form; see
-- @Note [Soft guard catch safety]@ for why the catch is sound.
--
-- Uses 'try' at the 'IO' layer so state changes made before the throw
-- survive the catch. The call stack is snapshotted and restored here,
-- because this is the one catch that resumes in the same session and
-- 'withSavedCallStack' does not restore on the exceptional path.
catchInstantiation :: Chr Bool -> Chr Bool
catchInstantiation m = do
  env <- ask
  saved <- liftIO (readIORef env.callStack)
  r <- liftIO (try (runChr m env))
  case r of
    Right b -> pure b
    Left e@(RuntimeErrorThrown kind _ _)
      | kind == InstantiationError -> do
          liftIO (writeIORef env.callStack saved)
          pure False
      | otherwise -> liftIO (throwIO e)

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
-- on the way out (including on exception — 'RuntimeErrorThrown' still
-- unwinds through here, and a soft guard may resume afterwards). The
-- bracket costs nothing when tracing is off, which is the only case
-- that matters for throughput: the whole function is a no-op then.
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
-- bindings, executes the body, and consumes its 'SRet' signal. Default
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
            sig <- withFreshEnv env (execStmts proc.body)
            case sig of
              SFall -> pure (VBool False)
              SRet v -> pure v
              _ -> uncaughtSignal "callProc" sig
      result <-
        if bumpDepthFor proc.procKind
          then withTraceDepth runBody
          else runBody
      traceExit proc.procKind result
      pure result

-- | Report a jump signal that reached a boundary with no owner: a
-- 'Continue' or 'Break' whose label names no enclosing 'Foreach' in
-- the same procedure, or any jump out of a 'DrainReactivationQueue'
-- body. The compiler never emits either, so this is a compiler bug
-- surfaced as a runtime error.
--
-- The 'SFall' arm exists only to keep the match total: both callers
-- handle 'SFall' before delegating here.
uncaughtSignal :: String -> Signal -> Chr a
uncaughtSignal ctx = \case
  SFall -> runtimeErrorS (ctx ++ ": uncaught fall-through")
  SRet _ -> runtimeErrorS (ctx ++ ": uncaught Return")
  SCont l -> runtimeError' (ctx ++ ": uncaught Continue ") l.unLabel
  SBrk l -> runtimeError' (ctx ++ ": uncaught Break ") l.unLabel

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
  | otherwise = Right (List.foldl' step emptyEnv (zip params args))
  where
    step e (p, CVal v) = insertVal p v e
    step e (p, CId s) = insertId p s e

-- | Execute a list of statements sequentially, stopping at the first
-- statement that signals a non-local jump and handing that signal to
-- the caller.
execStmts :: [Stmt] -> InterpM Signal
execStmts [] = pure SFall
execStmts (s : rest) = do
  sig <- execStmt s
  case sig of
    SFall -> execStmts rest
    _ -> pure sig

-- | Execute a single statement. Mutates the local 'Env' for binders,
-- returns the 'Signal' produced by control-flow stmts, and routes
-- store / history / reactivation effects through 'Chr'.
execStmt :: Stmt -> InterpM Signal
execStmt (LetVal name expr) = do
  v <- evalValExpr expr
  modifyEnv (insertVal name v)
  pure SFall
execStmt (LetId name expr) = do
  s <- evalIdExpr expr
  modifyEnv (insertId name s)
  pure SFall
execStmt (AssignVal name expr) = do
  v <- evalValExpr expr
  modifyEnv (insertVal name v)
  pure SFall
execStmt (AssignId name expr) = do
  s <- evalIdExpr expr
  modifyEnv (insertId name s)
  pure SFall
execStmt (If cond thenBranch elseBranch) = do
  b <- evalBoolExpr cond
  if b then execStmts thenBranch else execStmts elseBranch
execStmt (Foreach lbl cType suspVar conditions body) = do
  snapshot <- lift (getStoreSnapshot cType)
  let susps = toList snapshot
  execForeach lbl suspVar conditions body susps
execStmt (Continue lbl) = pure (SCont lbl)
execStmt (Break lbl) = pure (SBrk lbl)
execStmt (Return expr) = SRet <$> evalValExpr expr
execStmt (ExprStmt expr) = do
  _ <- evalValExpr expr
  pure SFall
execStmt (BoolExprStmt expr) = do
  _ <- evalBoolExpr expr
  pure SFall
execStmt (Store expr) = do
  sid <- evalIdExpr expr
  lift $ do
    didStore <- storeConstraint sid
    -- 'Store' is idempotent and, under Late Storage, reachable more
    -- than once for the same suspension; only the one that took
    -- effect is a trace event.
    when didStore $ emitTrace $ do
      (ct, vs) <- suspensionView sid
      ctName <- constraintTypeLabel ct
      ts <- snapshotValues vs
      pure (TEStore sid ctName ts)
  pure SFall
execStmt (Kill expr) = do
  sid <- evalIdExpr expr
  lift $ do
    killConstraint sid
    emitTrace (pure (TEKill sid))
  pure SFall
execStmt (AddHistory ruleId exprs) = do
  sids <- traverse evalIdExpr (historyIdsList exprs)
  lift $ do
    emitTrace $ do
      env <- ask
      let rn = lookupRuleName env ruleId
      pure (TEFire rn sids)
    addHistory ruleId sids
  pure SFall
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
          -- The compiler fixes this body to a single dispatch call
          -- ('ExprStmt'), which cannot jump; anything else would have
          -- no owner here, since the drain is not a labelled loop and
          -- 'drainQueue' has no way to return a value.
          sig <- runReaderT (execStmts body) envRef
          case sig of
            SFall -> pure ()
            _ -> uncaughtSignal "DrainReactivationQueue" sig
        else pure ()
  pure SFall
execStmt (PushFrame frame) = do
  lift (pushFrame frame)
  pure SFall

-- ---------------------------------------------------------------------------
-- Foreach implementation
-- ---------------------------------------------------------------------------

-- | Iterate the body of a 'Foreach' over a snapshot of candidate
-- suspensions. Dead suspensions and suspensions failing the index
-- conditions are skipped without entering the body. An 'SCont' /
-- 'SBrk' carrying /this/ loop's label is consumed here; every other
-- signal (a foreign label, an 'SRet') is handed further out.
execForeach ::
  Label ->
  Name ->
  [(ArgIndex, ValExpr)] ->
  [Stmt] ->
  [Suspension] ->
  InterpM Signal
execForeach _ _ _ _ [] = pure SFall
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
          sig <- lift (withTraceDepth (runReaderT (execStmts body) envRef))
          case sig of
            SFall -> execForeach lbl suspVar conditions body rest
            SCont l
              | l == lbl -> execForeach lbl suspVar conditions body rest
            SBrk l
              | l == lbl -> pure SFall
            _ -> pure sig

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

-- | The runtime check behind 'BFromVal': a value used in boolean
-- position must be a 'VBool'.
--
-- The two failure modes are diagnosed apart, because a boolean
-- position /demands/ a value. An unbound variable means the answer is
-- not knowable yet — an instantiation failure, which a rule guard
-- catches and retries after reactivation. A bound non-boolean (an
-- integer, an atom) is a definite mistake and stays a general error.
--
-- 'BFromVal' also appears in generated dispatch code and at the
-- early-drop check, where the wrapped expression always produces a
-- boolean, so neither branch is reachable from those uses.
boolFromValue :: Value -> Chr Bool
boolFromValue v = do
  v' <- deref v
  case v' of
    VBool b -> pure b
    _
      | isVar v' ->
          instantiationErrorS
            "guard is not sufficiently instantiated (unbound variable)"
      | otherwise -> runtimeErrorS "guard did not evaluate to a boolean"

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
  sids <- traverse evalIdExpr (historyIdsList args)
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
      Nothing -> fst <$> unifyOrError v1 v2
      Just _ -> do
        t1 <- snapshotValue v1
        t2 <- snapshotValue v2
        (ok, enqueued) <- unifyOrError v1 v2
        emitTrace (pure (TEUnify t1 t2 enqueued))
        pure ok
evalBoolExpr (BFromVal expr) = do
  v <- evalValExpr expr
  lift (boolFromValue v)
evalBoolExpr (BEvalDeep expr) = evalBoolExprDeep expr
evalBoolExpr (BSoftGuard expr) = softGuard (evalBoolExpr expr)

-- | Run a nested boolean evaluation under the soft-guard boundary.
-- Delegates to 'catchInstantiation' at the 'Chr' level; the local
-- 'Env' is an 'IORef', so bindings introduced before the failure
-- survive the catch.
softGuard :: InterpM Bool -> InterpM Bool
softGuard m = do
  ref <- ask
  lift (catchInstantiation (runReaderT m ref))

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

-- | Dispatch a host call by name. Synchronous exceptions thrown by the
-- host body get wrapped as runtime errors, with two exceptions: async
-- exceptions (Ctrl+C, thread kill) must keep their identity so they
-- reach their intended handler, and 'RuntimeErrorThrown' is re-thrown
-- verbatim so nested host calls preserve the original message and
-- stack frames. The VM's own non-local jumps never appear here — they
-- are 'Signal' values returned by 'execStmt', not exceptions.
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
          | isControlException exc -> liftIO (throwIO exc)
          | otherwise ->
              runtimeErrorS $
                "host call " ++ T.unpack name.unName ++ ": " ++ displayException exc
    Nothing -> runtimeError' "invokeHostCall: unknown host call " name.unName

-- | Unify two already-evaluated values (tell semantics). Enqueues
-- observers of any variables affected by the unification — including
-- on failure, where partial bindings may still have produced
-- observers worth reactivating. Raises a runtime error with both
-- operands pretty-printed when unification fails.
--
-- Also returns how many constraints the enqueue actually queued,
-- which is the number the tracer reports for a unification. Reading
-- it back off the queue would be a second derivation of the same
-- figure, and one that quietly stops matching if anything else ever
-- touches the queue in between.
unifyOrError :: Value -> Value -> Chr (Bool, Int)
unifyOrError v1 v2 = do
  (ok, observers) <- unify v1 v2
  enqueued <- enqueueObservers observers
  if ok
    then pure (True, enqueued)
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
-- @R is copy_term(quote(X))@ (RHS is a host call) leaves @X@'s bound
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
-- atoms) raise a runtime error — mirroring SWI Prolog's
-- @type_error(evaluable, F\/N)@.
--
-- Caveat: the host-call fallback below looks up @key.functor@ only,
-- discarding the arity, because 'HostCallRegistry' is keyed by name
-- alone. So @X = '-'(1), R is X@ reports the arity mismatch from
-- inside the @-@ primitive rather than as
-- @is: functor is not evaluable: -\/1@. The Scheme runtime keys its
-- equivalent table by @(name, arity)@ and so reports the latter — a
-- known divergence, tracked in @dev-docs\/SCHEME_BACKEND_GAPS.md@.
--
-- 'MakeTerm' callers do /not/ funnel through this walker — the
-- @quote/1@ quoting form must continue to produce the symbolic
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
  lift (fst <$> unifyOrError v1 v2)
evalBoolExprDeep (BFromVal expr) = do
  v <- evalValExprDeep expr
  lift (boolFromValue v)
evalBoolExprDeep (BEvalDeep expr) = evalBoolExprDeep expr
evalBoolExprDeep (BSoftGuard expr) = softGuard (evalBoolExprDeep expr)
evalBoolExprDeep expr = evalBoolExpr expr
