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

    -- * Closure application (shared with the query-time driver)
    applyClosure,

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
import Control.Monad (unless, void, when)
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
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Meta (valueToTerm)
import YCHR.Internal.Pretty (prettyTerm)
import YCHR.Internal.Runtime.Error
  ( RuntimeErrorKind (..),
    RuntimeErrorThrown (..),
    closureNoMatchError,
    closureUnboundError,
    instantiationErrorS,
    isControlException,
    runtimeError',
    runtimeErrorS,
  )
import YCHR.Internal.Runtime.History (addHistory, notInHistory)
import YCHR.Internal.Runtime.Index (GroundKey, indexablePositions)
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
import YCHR.Internal.Runtime.Slots
  ( Slot,
    SlotBoolExpr (..),
    SlotCallArg (..),
    SlotIdExpr (..),
    SlotProc (..),
    SlotProgram (..),
    SlotStmt (..),
    SlotValExpr (..),
    lowerProgram,
  )
import YCHR.Internal.Runtime.Store
  ( Suspension (..),
    aliveConstraint,
    candidateSuspensions,
    createConstraint,
    getConstraintArg,
    getConstraintType,
    getStoreSnapshot,
    idEqual,
    indexedPositionsFor,
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
    groundKey,
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
-- value-bound slots live in 'envValues', id-bound slots in 'envIds'.
-- The VM IR guarantees a local is bound in only one of the two, and the
-- slot phase ("YCHR.Internal.Runtime.Slots") numbers both kinds from one
-- per-procedure counter, so the two maps are keyed by the same space.
data Env = Env
  { envValues :: !(IntMap Value),
    envIds :: !(IntMap SuspensionId)
  }

emptyEnv :: Env
emptyEnv = Env IntMap.empty IntMap.empty

insertVal :: Slot -> Value -> Env -> Env
insertVal slot v e = e {envValues = IntMap.insert slot v e.envValues}

insertId :: Slot -> SuspensionId -> Env -> Env
insertId slot s e = e {envIds = IntMap.insert slot s e.envIds}

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
-- Lifting
-- ---------------------------------------------------------------------------

-- | Run a 'Chr' action in 'InterpM'. The single lift this stack needs;
-- named so call sites read as "do this in the session".
liftChr :: Chr a -> InterpM a
liftChr = lift
{-# INLINE liftChr #-}

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

-- | Interpret a VM program by calling a named procedure with the given
-- value arguments. Builds a fresh 'SessionEnv' for the program and
-- runs the call inside it.
--
-- The program is lowered into the interpreter's slot phase here. Entry
-- points that go through 'YCHR.Internal.Runtime.Session.withCHR' lower
-- once per compiled program instead ('CompiledProgram.slotProgram');
-- this one lowers per call, which is what the test-facing signature
-- buys and what a hand-built 'Program' in a test expects.
interpret :: Program -> HostCallRegistry -> Name -> [Value] -> IO Value
interpret prog hostCalls entryName args = do
  let procMap = (lowerProgram prog).slotProcedures
      evaluableMap = Map.fromList prog.evaluables
      callableMap = Map.fromList prog.callables
  env <-
    initSessionEnv
      prog.typeNames
      prog.ruleNames
      prog.inertTypes
      (indexablePositions prog)
      procMap
      hostCalls
      evaluableMap
      callableMap
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

lookupProc :: Name -> Chr (Maybe SlotProc)
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

-- | 'snapshotValue' over a list of values, in order.
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
      env <- case bindParams name proc.slotProcArity args of
        Right e -> pure e
        Left msg -> runtimeErrorS msg
      traceEntry proc args
      let runBody = withSavedCallStack $ do
            sig <- withFreshEnv env (execStmts proc.slotProcBody)
            case sig of
              SFall -> pure (VBool False)
              SRet v -> pure v
              _ -> uncaughtSignal "callProc" sig
      result <-
        if bumpDepthFor proc.slotProcKind
          then withTraceDepth runBody
          else runBody
      traceExit proc.slotProcKind result
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
-- and user functions/lambdas do.
bumpDepthFor :: ProcKind -> Bool
bumpDepthFor PKTell {} = True
bumpDepthFor PKActivate {} = True
bumpDepthFor PKOccurrence {} = True
bumpDepthFor PKReactivateDispatch = True
bumpDepthFor PKFunction {} = True

-- | Emit the entry-time event for a procedure call, if tracing is on.
-- Reactivation events are emitted at the per-suspension boundary
-- inside 'DrainReactivationQueue' (where the constraint id is in
-- hand), not here.
traceEntry :: SlotProc -> [CallVal] -> Chr ()
traceEntry proc args = case proc.slotProcKind of
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

-- | Bind procedure arguments into the environment slot they were
-- declared at, based on the runtime tag of each argument. Parameters
-- occupy slots @0 .. arity - 1@ in declaration order
-- ("YCHR.Internal.Runtime.Slots"), so this is a single walk of the
-- argument list with no name lookup and no rebalancing. The count is
-- the callee's, since the slot phase carries an arity rather than a
-- parameter-name list.
bindParams :: Name -> Int -> [CallVal] -> Either String Env
bindParams pname arity args
  | arity /= length args =
      Left $
        "bindParams: arity mismatch in "
          ++ T.unpack pname.unName
          ++ ": "
          ++ show arity
          ++ " params, "
          ++ show (length args)
          ++ " args"
  | otherwise = Right (List.foldl' step emptyEnv (zip [0 ..] args))
  where
    step e (slot, CVal v) = insertVal slot v e
    step e (slot, CId s) = insertId slot s e

-- | Execute a list of statements sequentially, stopping at the first
-- statement that signals a non-local jump and handing that signal to
-- the caller.
execStmts :: [SlotStmt] -> InterpM Signal
execStmts [] = pure SFall
execStmts (s : rest) = do
  sig <- execStmt s
  case sig of
    SFall -> execStmts rest
    _ -> pure sig

-- | Execute a single statement. Mutates the local 'Env' for binders,
-- returns the 'Signal' produced by control-flow stmts, and routes
-- store / history / reactivation effects through 'Chr'.
execStmt :: SlotStmt -> InterpM Signal
execStmt (SLetVal slot expr) = do
  v <- evalValExpr expr
  modifyEnv (insertVal slot v)
  pure SFall
execStmt (SLetId slot expr) = do
  s <- evalIdExpr expr
  modifyEnv (insertId slot s)
  pure SFall
execStmt (SAssignVal slot expr) = do
  v <- evalValExpr expr
  modifyEnv (insertVal slot v)
  pure SFall
execStmt (SAssignId slot expr) = do
  s <- evalIdExpr expr
  modifyEnv (insertId slot s)
  pure SFall
execStmt (SIf cond thenBranch elseBranch) = do
  b <- evalBoolExpr cond
  if b then execStmts thenBranch else execStmts elseBranch
execStmt (SForeach lbl cType suspSlot conditions body) = do
  susps <- foreachCandidates cType conditions
  execForeach lbl suspSlot conditions body susps
execStmt (SContinue lbl) = pure (SCont lbl)
execStmt (SBreak lbl) = pure (SBrk lbl)
execStmt (SReturn expr) = SRet <$> evalValExpr expr
execStmt (SExprStmt expr) = do
  _ <- evalValExpr expr
  pure SFall
execStmt (SBoolExprStmt expr) = do
  _ <- evalBoolExpr expr
  pure SFall
execStmt (SStore expr) = do
  sid <- evalIdExpr expr
  liftChr $ do
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
execStmt (SKill expr) = do
  sid <- evalIdExpr expr
  liftChr $ do
    killConstraint sid
    emitTrace (pure (TEKill sid))
  pure SFall
execStmt (SAddHistory ruleId exprs) = do
  sids <- traverse evalIdExpr exprs
  liftChr $ do
    emitTrace $ do
      env <- ask
      let rn = lookupRuleName env ruleId
      pure (TEFire rn sids)
    addHistory ruleId sids
  pure SFall
execStmt (SDrainReactivationQueue suspSlot body) = do
  envRef <- ask
  liftChr $
    drainQueue $ \sid -> do
      alive <- aliveConstraint sid
      if alive
        then do
          emitTrace $ do
            (ct, vs) <- suspensionView sid
            ctName <- constraintTypeLabel ct
            ts <- snapshotValues vs
            pure (TEReactivate sid ctName ts)
          liftIO (modifyIORef' envRef (insertId suspSlot sid))
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
execStmt (SPushFrame frame) = do
  liftChr (pushFrame frame)
  pure SFall

-- ---------------------------------------------------------------------------
-- Foreach implementation
-- ---------------------------------------------------------------------------

-- | The candidate suspension list for a 'Foreach' loop.
--
-- The default is the whole type bucket, which is what this was before
-- the store grew indexes. When one of the loop's index conditions can
-- drive a store index, the list narrows to what that condition could
-- select: the bucket for the condition's value plus the position's
-- non-ground fallback set. See "YCHR.Internal.Runtime.Index" for why
-- the narrowed list is still a superset of the matches; 'driverKey'
-- holds the two guards that keep the narrowing invisible to a
-- program's behaviour.
foreachCandidates :: ConstraintType -> [(ArgIndex, SlotValExpr)] -> InterpM [Suspension]
foreachCandidates cType conditions = do
  mIndexed <- liftChr (indexedPositionsFor cType)
  case mIndexed of
    Nothing -> liftChr (toList <$> getStoreSnapshot cType)
    Just indexed -> do
      mDriver <- driverKey indexed conditions
      case mDriver of
        Nothing -> liftChr (toList <$> getStoreSnapshot cType)
        Just (pos, key) -> liftChr (candidateSuspensions cType pos key)

-- | The first index condition that can drive the store index, as its
-- argument position together with the ground key of the condition's
-- value.
--
-- Two guards make the narrowing both sound and unobservable. The
-- condition's value must be /non-raising/ by construction
-- ('nonRaising'), so moving its evaluation to loop entry cannot fail
-- where evaluating it per candidate would have succeeded — today a loop
-- with no candidates evaluates no condition at all. And the value must
-- dereference to a fully ground term, because only a ground value's key
-- is stable for the loop's duration. Anything else — including a
-- compound term holding an unbound variable — falls through to the
-- unindexed path, which evaluates the condition per candidate exactly
-- as before.
driverKey :: IntSet -> [(ArgIndex, SlotValExpr)] -> InterpM (Maybe (Int, GroundKey))
driverKey _ [] = pure Nothing
driverKey indexed ((ArgIndex pos, expr) : rest)
  | nonRaising expr,
    IntSet.member pos indexed = do
      value <- evalValExpr expr
      mkey <- liftChr (groundKey value)
      case mkey of
        Just key -> pure (Just (pos, key))
        Nothing -> driverKey indexed rest
  | otherwise = driverKey indexed rest

-- | Whether evaluating an expression is total.
--
-- A store index is consulted once, before the loop body runs, so a
-- condition it drives must not be able to raise: an index-driven lookup
-- that evaluated one eagerly could turn a working query into an
-- instantiation error where the old code, having no candidate to check,
-- never evaluated it. The constructors below are what the compiler
-- emits for a guard's expected value — a head variable, a literal, or a
-- compound built from them. Everything else (a host call, a user
-- function, @is@, a field or term accessor) is left to the per-candidate
-- check.
--
-- The set is deliberately narrow, and it is the compiler's business to
-- keep it so: 'classifyEqual' only lifts the operands of a @GuardEqual@
-- that HNF produced, which are a head variable or a literal, so a
-- condition this accepts is a variable read or a term construction and
-- nothing else. A future compiler that lifted an allocating or
-- effectful expression here would make the loop-entry evaluation pay
-- something the per-candidate one only paid when a candidate existed.
nonRaising :: SlotValExpr -> Bool
nonRaising (SVar _ _) = True
nonRaising (SLit _) = True
nonRaising SNewVar = True
nonRaising (SMakeTerm _ args) = all nonRaising args
nonRaising _ = False

-- | Iterate the body of a 'Foreach' over a snapshot of candidate
-- suspensions. Dead suspensions and suspensions failing the index
-- conditions are skipped without entering the body. An 'SCont' /
-- 'SBrk' carrying /this/ loop's label is consumed here; every other
-- signal (a foreign label, an 'SRet') is handed further out.
execForeach ::
  Label ->
  Slot ->
  [(ArgIndex, SlotValExpr)] ->
  [SlotStmt] ->
  [Suspension] ->
  InterpM Signal
execForeach _ _ _ _ [] = pure SFall
execForeach lbl suspSlot conditions body (susp : rest) = do
  alive <- liftChr (isSuspAlive susp)
  if not alive
    then execForeach lbl suspSlot conditions body rest
    else do
      ok <- checkConditions susp conditions
      if not ok
        then execForeach lbl suspSlot conditions body rest
        else do
          liftChr $ emitTrace $ do
            ctName <- constraintTypeLabel susp.suspType
            ts <- snapshotValues susp.args
            pure (TEPartner ctName susp.suspId ts)
          modifyEnv (insertId suspSlot susp.suspId)
          envRef <- ask
          sig <- liftChr (withTraceDepth (runReaderT (execStmts body) envRef))
          case sig of
            SFall -> execForeach lbl suspSlot conditions body rest
            SCont l
              | l == lbl -> execForeach lbl suspSlot conditions body rest
            SBrk l
              | l == lbl -> pure SFall
            _ -> pure sig

checkConditions :: Suspension -> [(ArgIndex, SlotValExpr)] -> InterpM Bool
checkConditions _ [] = pure True
checkConditions susp ((ArgIndex i, expr) : rest) = do
  v <- evalValExpr expr
  let argVal = suspArg susp i
  eq <- liftChr (equal v argVal)
  if eq
    then checkConditions susp rest
    else pure False

-- ---------------------------------------------------------------------------
-- Value-expression evaluator (normal mode)
-- ---------------------------------------------------------------------------

-- | Evaluate a 'SlotValExpr' in normal (non-deep) mode. Variable
-- references return whatever value is currently bound; chains are not
-- followed. 'SEvalDeep' delegates to 'evalValExprDeep'.
evalValExpr :: SlotValExpr -> InterpM Value
evalValExpr (SVar slot name) = do
  env <- getEnv
  case IntMap.lookup slot env.envValues of
    Just v -> pure v
    Nothing -> liftChr (runtimeError' "evalValExpr: unbound variable " name.unName)
evalValExpr (SLit (IntLit n)) = pure (VInt n)
evalValExpr (SLit (FloatLit n)) = pure (VFloat n)
evalValExpr (SLit (AtomLit s)) = pure (VAtom s)
evalValExpr (SLit (TextLit s)) = pure (VText s)
evalValExpr (SLit (BoolLit b)) = pure (VBool b)
evalValExpr (SCallExpr name args) = do
  argVals <- traverse evalCallArg args
  liftChr (callProc name argVals)
evalValExpr (SHostCall name args) = do
  argVals <- traverse evalValExpr args
  derefedVals <- liftChr (traverse deref argVals)
  liftChr (invokeHostCall name derefedVals)
evalValExpr SNewVar = liftChr newVar
evalValExpr (SMakeTerm functor args) = do
  argVals <- traverse evalValExpr args
  pure $ makeTerm functor.unName argVals
evalValExpr (SGetArg expr idx) = do
  v <- evalValExpr expr
  liftChr (getArg v idx)
evalValExpr (SFieldArg expr (ArgIndex i)) = do
  sid <- evalIdExpr expr
  liftChr (getConstraintArg sid i)
evalValExpr (SFieldType expr) = do
  sid <- evalIdExpr expr
  ct <- liftChr (getConstraintType sid)
  pure (VInt (fromIntegral ct.unConstraintType))
evalValExpr (SEvalDeep expr) = evalValExprDeep expr
-- 'SEvalIs' is the @is@-with-variable-RHS marker. The compiler only
-- emits it for @R is X@ where @X@ is syntactically a variable; the
-- inner expression is therefore always a 'SVar'. We evaluate that
-- reference, dereference, and then walk the resulting value with
-- 'deepEvalValue' so a bound compound whose functor is a declared
-- function actually evaluates (matching SWI Prolog's @is@ on a
-- variable). Other 'SEvalDeep' use sites (guards, non-variable @is@
-- RHSes) do not invoke the walker.
evalValExpr (SEvalIs expr) = do
  v <- evalValExprDeep expr
  liftChr (deepEvalValue v)
evalValExpr (SApplyClosure f args) = do
  fv <- evalValExpr f
  argVals <- traverse evalValExpr args
  liftChr (applyClosure fv argVals)

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

-- | Evaluate a 'SlotBoolExpr' in normal (non-deep) mode. Logical
-- connectives short-circuit. 'SBEvalDeep' delegates to
-- 'evalBoolExprDeep'.
evalBoolExpr :: SlotBoolExpr -> InterpM Bool
evalBoolExpr (SBLit b) = pure b
evalBoolExpr (SBNot e) = not <$> evalBoolExpr e
evalBoolExpr (SBAnd e1 e2) = do
  b1 <- evalBoolExpr e1
  if b1 then evalBoolExpr e2 else pure False
evalBoolExpr (SBOr e1 e2) = do
  b1 <- evalBoolExpr e1
  if b1 then pure True else evalBoolExpr e2
evalBoolExpr (SBMatchTerm expr functor arity) = do
  v <- evalValExpr expr
  liftChr (matchTerm v functor.unName arity)
evalBoolExpr (SBEqual e1 e2) = do
  v1 <- evalValExpr e1
  v2 <- evalValExpr e2
  liftChr (equal v1 v2)
evalBoolExpr (SBIdEqual e1 e2) = do
  s1 <- evalIdExpr e1
  s2 <- evalIdExpr e2
  pure (idEqual s1 s2)
evalBoolExpr (SBAlive expr) = do
  sid <- evalIdExpr expr
  liftChr (aliveConstraint sid)
evalBoolExpr (SBIsConstraintType expr cType) = do
  sid <- evalIdExpr expr
  liftChr (isConstraintType sid cType)
evalBoolExpr (SBNotInHistory ruleId args) = do
  sids <- traverse evalIdExpr args
  ok <- liftChr (notInHistory ruleId sids)
  unless ok $
    liftChr $
      emitTrace $ do
        env <- ask
        let rn = lookupRuleName env ruleId
        pure (TEHistoryHit rn sids)
  pure ok
evalBoolExpr (SBUnify e1 e2) = do
  v1 <- evalValExpr e1
  v2 <- evalValExpr e2
  liftChr $ do
    env <- ask
    mh <- liftIO (readIORef env.traceHandler)
    case mh of
      Nothing -> void (unifyOrError v1 v2)
      Just _ -> do
        t1 <- snapshotValue v1
        t2 <- snapshotValue v2
        enqueued <- unifyOrError v1 v2
        emitTrace (pure (TEUnify t1 t2 enqueued))
    -- 'unifyOrError' raises on failure, so a 'SBUnify' that reaches
    -- this point has succeeded: the boolean position is always true.
    pure True
evalBoolExpr (SBFromVal expr) = do
  v <- evalValExpr expr
  liftChr (boolFromValue v)
evalBoolExpr (SBEvalDeep expr) = evalBoolExprDeep expr
evalBoolExpr (SBSoftGuard expr) = softGuard (evalBoolExpr expr)

-- | Run a nested boolean evaluation under the soft-guard boundary.
-- Delegates to 'catchInstantiation' at the 'Chr' level; the local
-- 'Env' is an 'IORef', so bindings introduced before the failure
-- survive the catch.
softGuard :: InterpM Bool -> InterpM Bool
softGuard m = do
  ref <- ask
  liftChr (catchInstantiation (runReaderT m ref))

-- ---------------------------------------------------------------------------
-- Id-expression evaluator
-- ---------------------------------------------------------------------------

-- | Evaluate a 'SlotIdExpr' to a 'SuspensionId': either a lookup in
-- the id slot of the local 'Env', or a fresh suspension created from a
-- 'SCreateConstraint' (not yet 'Store'd).
evalIdExpr :: SlotIdExpr -> InterpM SuspensionId
evalIdExpr (SIdVar slot name) = do
  env <- getEnv
  case IntMap.lookup slot env.envIds of
    Just s -> pure s
    Nothing -> liftChr (runtimeError' "evalIdExpr: unbound id variable " name.unName)
evalIdExpr (SCreateConstraint cType args) = do
  argVals <- traverse evalValExpr args
  liftChr (createConstraint cType argVals)

-- ---------------------------------------------------------------------------
-- Call-arg evaluator
-- ---------------------------------------------------------------------------

evalCallArg :: SlotCallArg -> InterpM CallVal
evalCallArg (SCallVal e) = CVal <$> evalValExpr e
evalCallArg (SCallId e) = CId <$> evalIdExpr e

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
-- operands pretty-printed when unification fails, so returning at all
-- means success.
--
-- Returns how many constraints the enqueue actually queued,
-- which is the number the tracer reports for a unification. Reading
-- it back off the queue would be a second derivation of the same
-- figure, and one that quietly stops matching if anything else ever
-- touches the queue in between.
unifyOrError :: Value -> Value -> Chr Int
unifyOrError v1 v2 = do
  (ok, observers) <- unify v1 v2
  enqueued <- enqueueObservers observers
  if ok
    then pure enqueued
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
evalValExprDeep :: SlotValExpr -> InterpM Value
evalValExprDeep (SVar slot name) = do
  v <- evalValExpr (SVar slot name)
  liftChr (deref v)
evalValExprDeep (SHostCall name args) = do
  argVals <- traverse evalValExprDeep args
  liftChr (invokeHostCall name argVals)
evalValExprDeep (SCallExpr name args) = do
  argVals <- traverse evalCallArgDeep args
  liftChr (callProc name argVals)
evalValExprDeep (SApplyClosure f args) = do
  fv <- evalValExprDeep f
  argVals <- traverse evalValExprDeep args
  liftChr (applyClosure fv argVals)
evalValExprDeep (SMakeTerm functor args) = do
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

evalCallArgDeep :: SlotCallArg -> InterpM CallVal
evalCallArgDeep (SCallVal e) = CVal <$> evalValExprDeep e
evalCallArgDeep (SCallId e) = CId <$> evalIdExpr e

-- ---------------------------------------------------------------------------
-- Closure application
-- ---------------------------------------------------------------------------

-- | Apply a first-class callable to arguments: the whole of
-- @'$call'(F, A1, …, An)@.
--
-- The closure is dereferenced and turned into a 'CallableKey' by
-- 'closureKey'; the key selects a procedure from the session's
-- callables table, and that procedure is called with any captured
-- values the closure carries, followed by the arguments. One map
-- lookup replaces the per-arity dispatcher chain this used to be,
-- whose length grew with the number of same-arity functions and
-- lifted lambdas the program defines.
--
-- The failure modes, and their kinds, are the dispatchers': an unbound
-- closure is an instantiation error, so a rule guard soft-fails and
-- retries the occurrence once reactivation binds the variable;
-- everything else is a general error.
applyClosure :: Value -> [Value] -> Chr Value
applyClosure closure args = do
  v <- deref closure
  v' <- derefClosureHeader v
  case closureKey (length args) v' of
    Just (key, captures) -> do
      SessionEnv {callables} <- ask
      case Map.lookup key callables of
        Just procName -> callProc procName (map CVal (captures <> args))
        Nothing -> closureNoMatchError
    Nothing
      | isVar v -> closureUnboundError
      | otherwise -> closureNoMatchError

-- | Read a closure's two header fields through their bindings.
--
-- The generated dispatchers compared those fields with @BEqual@, which
-- dereferences its operands, so a function-reference term whose name or
-- declared-arity field was a /bound variable/ still dispatched. Reading
-- them here keeps that behaviour. Only the header is read: the captures
-- are handed to the callee exactly as @GetArg@ handed them, so a
-- capture that is an unbound variable stays the very cell the callee
-- observes.
--
-- The common case — both header fields already literals, which is what
-- the compiler's @MakeTerm@ produces — returns the value untouched and
-- allocates nothing. This runs on every dynamic call, so it has to be
-- cheap on the path that matters.
derefClosureHeader :: Value -> Chr Value
derefClosureHeader (VTerm f (field0 : field1 : rest))
  | isVar field0 || isVar field1 = do
      field0' <- deref field0
      field1' <- deref field1
      pure (VTerm f (field0' : field1' : rest))
derefClosureHeader v = pure v

-- | The dispatch key of a closure value applied at @n@ arguments,
-- together with the captured values to pass before those arguments.
--
-- See 'CallableKey' for the shape a closure value has and why the key
-- is what it is. Two details preserve the old dispatchers' behaviour:
--
--   * a function reference is looked up at the arity it records, and
--     an application at any other arity is a mismatch. Without that
--     check @'$call'('fun call\/2', 1, 2, 3)@ would resolve to
--     @call\/3@, which is a different function;
--   * a lifted lambda is looked up at the arity it is /applied/ at,
--     because its closure does not record the arity its source lambda
--     declared. The table holds only the declared arity, so any other
--     arity misses the lookup.
--
-- Captures are the closure's fields after the two header fields
-- (identity and quoted source form), passed through un-dereferenced —
-- exactly what @GetArg@ handed the dispatched procedure. The header
-- itself is dereferenced before this runs (see 'derefClosureHeader').
closureKey :: Int -> Value -> Maybe (CallableKey, [Value])
closureKey n v = case v of
  VTerm f (VAtom ident : rest)
    | f == funRefFunctor.unName,
      [VInt declared] <- rest,
      fromIntegral declared == n ->
        Just
          ( CallableKey
              { functor = funRefFunctor,
                identity = Name ident,
                arity = fromIntegral declared
              },
            []
          )
    | f == lambdaClosureFunctor.unName,
      _sourceForm : captures <- rest ->
        Just
          ( CallableKey
              { functor = lambdaClosureFunctor,
                identity = Name ident,
                arity = n
              },
            captures
          )
  _ -> Nothing

-- ---------------------------------------------------------------------------
-- Bool-expression evaluator (deep deref mode)
-- ---------------------------------------------------------------------------

-- | Deep-deref evaluation for 'SlotBoolExpr'. Mirrors
-- 'evalValExprDeep': propagates deep mode into the value and id
-- payloads.
evalBoolExprDeep :: SlotBoolExpr -> InterpM Bool
evalBoolExprDeep (SBNot e) = not <$> evalBoolExprDeep e
evalBoolExprDeep (SBAnd e1 e2) = do
  b1 <- evalBoolExprDeep e1
  if b1 then evalBoolExprDeep e2 else pure False
evalBoolExprDeep (SBOr e1 e2) = do
  b1 <- evalBoolExprDeep e1
  if b1 then pure True else evalBoolExprDeep e2
evalBoolExprDeep (SBMatchTerm expr functor arity) = do
  v <- evalValExprDeep expr
  liftChr (matchTerm v functor.unName arity)
evalBoolExprDeep (SBEqual e1 e2) = do
  v1 <- evalValExprDeep e1
  v2 <- evalValExprDeep e2
  liftChr (equal v1 v2)
evalBoolExprDeep (SBUnify e1 e2) = do
  v1 <- evalValExprDeep e1
  v2 <- evalValExprDeep e2
  liftChr (void (unifyOrError v1 v2))
  pure True
evalBoolExprDeep (SBFromVal expr) = do
  v <- evalValExprDeep expr
  liftChr (boolFromValue v)
evalBoolExprDeep (SBEvalDeep expr) = evalBoolExprDeep expr
evalBoolExprDeep (SBSoftGuard expr) = softGuard (evalBoolExprDeep expr)
evalBoolExprDeep expr = evalBoolExpr expr
