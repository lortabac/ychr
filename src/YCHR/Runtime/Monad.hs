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
module YCHR.Runtime.Monad
  ( -- * The Chr monad
    Chr,
    runChr,

    -- * Session environment
    SessionEnv (..),
    initSessionEnv,

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
import Data.Map.Strict (Map)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
import YCHR.Compile.Pipeline (ExportResolution)
import YCHR.Runtime.Types (Suspension, SuspensionId, Value, VarId (..))
import YCHR.Types qualified as Types
import YCHR.VM (EvaluableKey, Procedure, RuleId, StackFrame)
import YCHR.VM qualified as VM

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
-- locals (e.g. 'Env') stay layered in a 'StateT' above 'Chr' where
-- they belong.
data SessionEnv = SessionEnv
  { -- | Counter for fresh logical-variable IDs.
    varCounter :: !(IORef VarId),
    -- | Type-indexed store: one append-only sequence per constraint
    -- type, keyed by the integer wrapped in 'ConstraintType'.
    storeByType :: !(IORef (IntMap (Seq Suspension))),
    -- | Source names parallel to 'storeByType', indexed by
    -- 'ConstraintType'.
    storeTypeNames :: !(IntMap Types.Name),
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
    exportedSet :: !(Set Types.QualifiedIdentifier)
  }

-- | Build a fresh 'SessionEnv' for a compiled program.
initSessionEnv ::
  [Types.Name] ->
  ProcMap ->
  HostCallRegistry ->
  EvaluableRegistry ->
  Map Types.UnqualifiedIdentifier ExportResolution ->
  Set Types.QualifiedIdentifier ->
  IO SessionEnv
initSessionEnv typeNames pm hc ev expMap expSet = do
  vc <- newIORef (VarId 0)
  let typeCount = length typeNames
      emptyStore = IntMap.fromList [(i, Seq.empty) | i <- [0 .. typeCount - 1]]
      typeNameMap = IntMap.fromList (zip [0 ..] typeNames)
  bt <- newIORef emptyStore
  bi <- newIORef IntMap.empty
  ni <- newIORef 0
  hi <- newIORef Set.empty
  rq <- newIORef Seq.empty
  cs <- newIORef []
  pmRef <- newIORef pm
  pure
    SessionEnv
      { varCounter = vc,
        storeByType = bt,
        storeTypeNames = typeNameMap,
        storeById = bi,
        storeNextId = ni,
        history = hi,
        reactQueue = rq,
        callStack = cs,
        procMap = pmRef,
        hostCalls = hc,
        evaluables = ev,
        exportMap = expMap,
        exportedSet = expSet
      }

-- | Run a 'Chr' action against a built 'SessionEnv'. Thin alias around
-- 'runReaderT' so callers don't need to import the transformer module.
runChr :: Chr a -> SessionEnv -> IO a
runChr = runReaderT
