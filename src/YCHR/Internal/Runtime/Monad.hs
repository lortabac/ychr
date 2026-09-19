{-# LANGUAGE OverloadedRecordDot #-}

-- | The 'Chr' monad and the 'SessionEnv' it reads from.
--
-- 'Chr' is the host-side runtime monad: a 'ReaderT' over a record of
-- mutable references that hold the constraint store, propagation
-- history, reactivation queue, unification-variable counter, the
-- interpreter call stack, the procedure map, and immutable references
-- to the host-call registry and export-resolution maps.
--
-- The compiler never sees 'Chr'; it only emits VM code. 'Chr' is the
-- shape of the *interpreter* that executes that VM code, plus the
-- query-time driver that calls into the interpreter.
module YCHR.Internal.Runtime.Monad
  ( -- * The Chr monad
    Chr,
    runChr,

    -- * Session environment
    SessionEnv (..),
    initSessionEnv,
    forkSearchSessionEnv,

    -- * Auxiliary types
    CallStack,
    ProcMap,
    HostCallFn (..),
    HostCallRegistry,
    EvaluableRegistry,
  )
where

import Control.Monad.Trans.Reader (ReaderT, runReaderT)
import Data.IORef
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
-- Qualified because 'TrailState (..)' is imported, putting its 'length'
-- selector in scope next to the list function (dev-docs/MICROHS_GAPS.md, gap 1).
import Data.List qualified as List
import Data.Map.Strict (Map)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import YCHR.Internal.Compile.Pipeline (ExportResolution)
import YCHR.Internal.Runtime.Trace (TraceHandler)
import YCHR.Internal.Runtime.Types
  ( Suspension,
    SuspensionId,
    Trail (..),
    TrailState (..),
    Value,
    VarId (..),
  )
import YCHR.Internal.Types qualified as Types
import YCHR.Internal.VM (EvaluableKey, Procedure, RuleId, StackFrame)
import YCHR.Internal.VM qualified as VM

-- | The runtime call stack (newest frame first), used for error reporting.
type CallStack = [StackFrame]

-- | Map from procedure name to its VM definition.
type ProcMap = Map VM.Name Procedure

-- | Registry of host-language functions callable from compiled code.
type HostCallRegistry = Map VM.Name HostCallFn

-- | Registry of user-defined functions that the deep-evaluator can
-- dispatch to. Maps a @(functor, arity)@ key (as seen on a 'VTerm')
-- to the mangled 'ProcMap' key that resolves the corresponding
-- compiled procedure.
type EvaluableRegistry = Map EvaluableKey VM.Name

-- | The host-side runtime monad.
type Chr = ReaderT SessionEnv IO

-- | A host call function. Operates inside 'Chr' so it can read mutable
-- runtime state (logical variables, the store, the call stack) the
-- same way the interpreter does.
newtype HostCallFn = HostCallFn
  { runHostCall :: [Value] -> Chr Value
  }

-- | The mutable session state plus the immutable program-level lookups
-- the runtime needs. All long-lived state lives here; per-procedure
-- locals live above 'Chr' in the interpreter's own 'ReaderT' over an
-- 'IORef' holding its per-call environment record, which is what lets
-- the writes made before a soft-guard failure survive the catch. See
-- @Note [Soft guard catch safety]@ in
-- "YCHR.Internal.Runtime.Interpreter".
data SessionEnv = SessionEnv
  { -- | Counter for fresh logical-variable IDs.
    varCounter :: !(IORef VarId),
    -- | Type-indexed store: one append-only sequence per constraint
    -- type, keyed by the integer wrapped in 'ConstraintType'.
    storeByType :: !(IORef (IntMap (Seq Suspension))),
    -- | Source names parallel to 'storeByType', indexed by
    -- 'ConstraintType'.
    storeTypeNames :: !(IntMap Types.Name),
    -- | The constraint types the compiler marked inert
    -- ('YCHR.Internal.VM.Program'.'inertTypes'), as the set of their
    -- 'Types.ConstraintType' indices. A suspension of one of these
    -- types is not registered as an observer of the variables in its
    -- arguments, because reactivating it could do nothing.
    inertTypes :: !IntSet,
    -- | Display names of rules, indexed by 'RuleId'. Carried so the
    -- tracer can label 'AddHistory' / 'BNotInHistory' events
    -- without a second lookup into the original 'Program'.
    ruleNames :: !(IntMap Text),
    -- | Map from suspension id to the suspension record. Populated on
    -- 'createConstraint'.
    storeById :: !(IORef (IntMap Suspension)),
    -- | Counter for the next suspension id.
    storeNextId :: !(IORef Int),
    -- | Propagation history: which rules have fired with which id tuples.
    history :: !(IORef (Set (RuleId, [SuspensionId]))),
    -- | Queue of constraint ids pending reactivation (filled by 'unify',
    -- drained by 'DrainReactivationQueue').
    reactQueue :: !(IORef (Seq SuspensionId)),
    -- | Interpreter call stack (newest first), capped in length.
    callStack :: !(IORef CallStack),
    -- | All known procedures. Mutable so query-time lambdas can be
    -- inserted without rebuilding the env.
    procMap :: !(IORef ProcMap),
    -- | Host-call registry.
    hostCalls :: !HostCallRegistry,
    -- | Deep-evaluator dispatch table for the @is@ operator.
    -- Populated from the compiler's user-defined-function list at
    -- session init.
    evaluables :: !EvaluableRegistry,
    -- | Export map from the compiler — used to resolve unqualified
    -- constraint names at 'tellConstraint' time.
    exportMap :: !(Map Types.UnqualifiedIdentifier ExportResolution),
    -- | The set of all qualified identifiers exported by the program.
    exportedSet :: !(Set Types.QualifiedIdentifier),
    -- | Optional tracing sink. When 'Just', the interpreter emits a
    -- 'TraceEvent' at each ωr step and at function / host-call
    -- boundaries. Stored as an 'IORef' so the REPL can swap a
    -- handler in for the duration of one @:trace@ query inside an
    -- otherwise-untraced live session.
    traceHandler :: !(IORef (Maybe TraceHandler)),
    -- | Undo log for search, or 'Nothing' when no search is active —
    -- which is the case at the top level and stays the case for a
    -- program that never enters a search. While it is
    -- 'Nothing' nothing is recorded, so the cost to an ordinary
    -- session is one field read per variable and flag write.
    --
    -- Installed by 'forkSearchSessionEnv' and shared, not copied, by
    -- every fork underneath it; see 'Trail' for why one trail must
    -- span nested searches.
    trail :: !(Maybe Trail),
    -- | Current indentation depth for the tracer. Only meaningful
    -- when 'traceHandler' is 'Just'; the interpreter bumps it on
    -- entry to ωr procedures (activate / occurrence / reactivate
    -- dispatch) and on user-function / lambda entry, via @bracket@
    -- so an unwinding runtime error still pops it.
    traceDepth :: !(IORef Int)
  }

-- | Build a fresh 'SessionEnv' for a compiled program.
initSessionEnv ::
  [Types.Name] ->
  [Text] ->
  [Types.ConstraintType] ->
  ProcMap ->
  HostCallRegistry ->
  EvaluableRegistry ->
  Map Types.UnqualifiedIdentifier ExportResolution ->
  Set Types.QualifiedIdentifier ->
  IO SessionEnv
initSessionEnv typeNames rNames inert pm hc ev expMap expSet = do
  vc <- newIORef (VarId 0)
  let typeCount = List.length typeNames
      emptyStore = IntMap.fromList [(i, Seq.empty) | i <- [0 .. typeCount - 1]]
      typeNameMap = IntMap.fromList (zip [0 ..] typeNames)
      ruleNameMap = IntMap.fromList (zip [0 ..] rNames)
  bt <- newIORef emptyStore
  bi <- newIORef IntMap.empty
  ni <- newIORef 0
  hi <- newIORef Set.empty
  rq <- newIORef Seq.empty
  cs <- newIORef []
  pmRef <- newIORef pm
  th <- newIORef Nothing
  td <- newIORef 0
  pure
    SessionEnv
      { varCounter = vc,
        storeByType = bt,
        storeTypeNames = typeNameMap,
        inertTypes = IntSet.fromList [i | Types.ConstraintType i <- inert],
        ruleNames = ruleNameMap,
        storeById = bi,
        storeNextId = ni,
        history = hi,
        reactQueue = rq,
        callStack = cs,
        procMap = pmRef,
        hostCalls = hc,
        evaluables = ev,
        exportMap = expMap,
        exportedSet = expSet,
        trail = Nothing,
        traceHandler = th,
        traceDepth = td
      }

-- | A fresh session of the same program, ready to run a search: same
-- procedures, constraint types, rule names, host calls and exports,
-- but its own store, history, reactivation queue and call stack, and
-- with a trail guaranteed to be installed. The procedure map is
-- copied into a new 'IORef', so the fork may add procedures without
-- the original seeing them.
--
-- Every fork goes through here, because every entry point that opens
-- one — @solve\/1@, @find_all\/2@, @fold_solutions\/4@ and
-- @run_chr_session\/1@ — is the search driver.
--
-- The variable and suspension-id counters are /shared/, so a fork's
-- ids never collide with its parent's: a cross-session observer leak
-- then hits an unknown 'SuspensionId' instead of silently reactivating
-- an unrelated constraint that reused the id. The trace state is
-- shared too, so a traced query shows the fork's steps.
--
-- Unlike building one from scratch with 'initSessionEnv', this reuses
-- the program-level maps as they are instead of rebuilding them from
-- lists — which matters because a fork can be per-iteration work (the
-- type-checker's overload search opens one search per function
-- equation).
--
-- A fresh trail is installed only when the parent has none. A nested
-- search /shares/ its parent's, so that entries an inner search
-- commits stay visible to the outer driver: variable cells are shared
-- across forks even though store references are not, and an outer
-- branch that later fails must be able to undo bindings an inner
-- search made. Marks, not trails, are what delimit an undo.
forkSearchSessionEnv :: SessionEnv -> IO SessionEnv
forkSearchSessionEnv env = do
  pm <- readIORef env.procMap
  bt <- newIORef (IntMap.map (const Seq.empty) env.storeTypeNames)
  bi <- newIORef IntMap.empty
  hi <- newIORef Set.empty
  rq <- newIORef Seq.empty
  cs <- newIORef []
  pmRef <- newIORef pm
  tr <- case env.trail of
    Just t -> pure (Just t)
    Nothing -> Just . Trail <$> newIORef (TrailState {entries = [], length = 0})
  pure
    env
      { storeByType = bt,
        storeById = bi,
        history = hi,
        reactQueue = rq,
        callStack = cs,
        procMap = pmRef,
        trail = tr
      }

-- | Run a 'Chr' action against a built 'SessionEnv'. Thin alias around
-- 'runReaderT' so callers don't need to import the transformer module.
runChr :: Chr a -> SessionEnv -> IO a
runChr = runReaderT
