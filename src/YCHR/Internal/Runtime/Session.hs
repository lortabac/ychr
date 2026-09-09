{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

-- | The CHR session: a running interpreter state for a compiled
-- program (constraint store, propagation history, reactivation queue,
-- unification variables, call stack), packaged as the 'Chr' monad.
--
-- Lives in its own module so the type-checker can open a CHR session
-- without depending on "YCHR.Run" (which would otherwise form a cycle
-- once "YCHR.Run" calls into the type-checker for goal-time checks).
module YCHR.Internal.Runtime.Session
  ( -- * The CHR monad (re-exported)
    Chr,
    SessionEnv (..),
    initSessionEnv,
    runChr,

    -- * Session input
    SessionInput (..),
    toSessionInput,

    -- * Reactivation
    drainReactivation,

    -- * Session setup
    withCHR,
    withCHRExtra,
    withCHRExtraTraced,
    withTraceHandler,

    -- * Telling constraints
    tellConstraint,
    tellResolvedConstraint,

    -- * Name resolution (shared with "YCHR.Internal.Runtime.Goal")
    resolveByExport,
  )
where

import Control.Exception (bracket_)
import Control.Monad (unless, void, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask)
import Data.IORef (readIORef, writeIORef)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text qualified as T
import YCHR.Internal.Compile (tellProcName)
import YCHR.Internal.Compile.Names (reactivateDispatchName)
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..), ExportResolution (..))
import YCHR.Internal.Runtime.Error (runtimeErrorS)
import YCHR.Internal.Runtime.Interpreter
  ( HostCallRegistry,
    callProc,
    constraintTypeLabel,
    emitTrace,
    snapshotValues,
    suspensionView,
  )
import YCHR.Internal.Runtime.Monad
  ( Chr,
    SessionEnv (..),
    initSessionEnv,
    runChr,
  )
import YCHR.Internal.Runtime.Reactivation (drainQueue)
import YCHR.Internal.Runtime.Store (aliveConstraint)
import YCHR.Internal.Runtime.Trace (TraceEvent (..), TraceHandler)
import YCHR.Internal.Runtime.Types (CallVal (..), Value (..))
import YCHR.Internal.Types qualified as Types
import YCHR.Internal.VM (Name (..), Procedure (..), Program (..))

-- | The narrow slice of a compiled program that 'withCHR' /
-- 'withCHRExtra' need: the VM 'Program' and the export-resolution maps
-- used by 'tellConstraint' to canonicalize unqualified constraint
-- names. A 'CompiledProgram' projects to one via 'toSessionInput'; the
-- pre-compiled type-checker bundle is a 'SessionInput' directly.
data SessionInput = SessionInput
  { program :: Program,
    -- | 'program''s procedures, keyed by name. Taken from the
    -- 'CompiledProgram' rather than rebuilt here, so that every
    -- session run against one compiled program shares the table
    -- instead of paying for it per query.
    procIndex :: Map Name Procedure,
    exportMap :: Map Types.UnqualifiedIdentifier ExportResolution,
    exportedSet :: Set Types.QualifiedIdentifier
  }
  deriving ()

-- | Project a 'CompiledProgram' down to the slice 'withCHR' /
-- 'withCHRExtra' actually read.
toSessionInput :: CompiledProgram -> SessionInput
toSessionInput cp =
  SessionInput
    { program = cp.program,
      procIndex = cp.procIndex,
      exportMap = cp.exportMap,
      exportedSet = cp.exportedSet
    }

-- | Run a CHR action in a fresh session for a compiled program. All
-- runtime state (constraint store, propagation history, reactivation
-- queue, unification variables, call stack) is initialised and
-- persists for the duration of the computation.
withCHR :: SessionInput -> HostCallRegistry -> Chr a -> IO a
withCHR si hc action = withCHRExtra si hc [] action

-- | Like 'withCHR' but merges extra procedures (e.g. query-time lambda
-- compilations and updated call dispatches) into the procedure map
-- visible to the action.
withCHRExtra ::
  SessionInput ->
  HostCallRegistry ->
  [Procedure] ->
  Chr a ->
  IO a
withCHRExtra si hc extraProcs action = do
  let extraProcMap = Map.fromList [(p.name, p) | p <- extraProcs]
      procMap = extraProcMap `Map.union` si.procIndex
  let evaluableMap = Map.fromList si.program.evaluables
  env <-
    initSessionEnv
      si.program.typeNames
      si.program.ruleNames
      si.program.inertTypes
      procMap
      hc
      evaluableMap
      si.exportMap
      si.exportedSet
  runChr action env

-- | Like 'withCHRExtra' but also installs a trace handler so that the
-- interpreter emits 'TraceEvent's at each canonical ωr step (plus
-- function and host-call boundaries). Used by the REPL's @:trace@
-- one-shot dispatch. The handler is bound for the duration of the
-- action; the session and its mutable state are fresh, so no clear-up
-- on the way out is needed.
withCHRExtraTraced ::
  SessionInput ->
  HostCallRegistry ->
  [Procedure] ->
  TraceHandler ->
  Chr a ->
  IO a
withCHRExtraTraced si hc extraProcs handler action =
  withCHRExtra si hc extraProcs $ do
    env <- ask
    liftIO $ do
      writeIORef env.traceHandler (Just handler)
      writeIORef env.traceDepth 0
    action

-- | Install a trace handler around a 'Chr' action inside an existing
-- session, restoring the previous handler (and depth) on the way out
-- — including on exceptions. Used by the REPL's live-mode @:trace@
-- so that one query traces without affecting subsequent untraced
-- queries against the same persistent store.
withTraceHandler :: TraceHandler -> Chr a -> Chr a
withTraceHandler handler action = do
  env <- ask
  liftIO $ do
    prevHandler <- readIORef env.traceHandler
    prevDepth <- readIORef env.traceDepth
    bracket_
      ( do
          writeIORef env.traceHandler (Just handler)
          writeIORef env.traceDepth 0
      )
      ( do
          writeIORef env.traceHandler prevHandler
          writeIORef env.traceDepth prevDepth
      )
      (runChr action env)

-- | Drain the reactivation queue, dispatching each live constraint to
-- @reactivate_dispatch@ and emitting the per-suspension
-- 'TEReactivate' event for the tracer.
--
-- This is the host-side mirror of the VM's
-- 'YCHR.Internal.VM.DrainReactivationQueue' statement, for the two
-- drivers that have to do the same work outside compiled code: the
-- query-time evaluator after a goal unification ("YCHR.Run"), and the
-- search driver after binding a choice point
-- ("YCHR.Internal.Runtime.Search"). It lives here because this is the
-- lowest module both of them already import.
drainReactivation :: Chr ()
drainReactivation =
  drainQueue $ \sid -> do
    alive <- aliveConstraint sid
    when alive $ do
      emitTrace $ do
        (ct, vs) <- suspensionView sid
        ctName <- constraintTypeLabel ct
        ts <- snapshotValues vs
        pure (TEReactivate sid ctName ts)
      void (callProc reactivateDispatchName [CId sid])

-- | Add a constraint to the store. The constraint name can be
-- unqualified (resolved via the session's export map) or fully
-- qualified.
tellConstraint :: Types.Name -> [Value] -> Chr ()
tellConstraint name args = do
  SessionEnv {exportMap, exportedSet} <- ask
  resolved <- case resolveByExport exportMap exportedSet name (length args) of
    Left err -> runtimeErrorS err
    Right qname -> pure qname
  tellResolvedConstraint resolved args

-- | 'tellConstraint' for a name that has already been resolved —
-- \"YCHR.Internal.Runtime.Goal\" resolves a goal in the calling
-- session, before the fork, and the search driver resolves a choice
-- point's alternatives without the export check. Re-resolving here
-- would undo both.
tellResolvedConstraint :: Types.Name -> [Value] -> Chr ()
tellResolvedConstraint name args = do
  SessionEnv {procMap} <- ask
  let tellName = tellProcName name (length args)
  pm <- liftIO (readIORef procMap)
  unless (Map.member tellName pm) $
    runtimeErrorS ("Constraint not found: " ++ T.unpack tellName.unName)
  _ <- callProc tellName (map CVal args)
  pure ()

-- | Name resolution against the export map and qualified-name set.
-- Used by 'tellConstraint' to canonicalize an unqualified constraint
-- name to its module-qualified form so the proc-map lookup matches.
resolveByExport ::
  Map Types.UnqualifiedIdentifier ExportResolution ->
  Set Types.QualifiedIdentifier ->
  Types.Name ->
  Int ->
  Either String Types.Name
resolveByExport expMap expSet name arity = case name of
  Types.Unqualified n ->
    case Map.lookup (Types.UnqualifiedIdentifier n arity) expMap of
      Just (UniqueExport qname) -> Right (Types.qualifiedToName qname)
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
    if Set.member (Types.QualifiedIdentifier m n arity) expSet
      then Right name
      else
        Left
          ( "Constraint not exported: "
              ++ T.unpack m
              ++ ":"
              ++ T.unpack n
              ++ "/"
              ++ show arity
          )
