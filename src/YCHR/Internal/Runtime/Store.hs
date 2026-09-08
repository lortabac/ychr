{-# LANGUAGE OverloadedRecordDot #-}

-- | Constraint store for the CHR Haskell runtime.
--
-- Manages constraint suspensions: creation, storage, killing, liveness
-- checking, field access, and snapshot-based iteration. Integrates with
-- the observer/reactivation mechanism in "YCHR.Internal.Runtime.Var": when a
-- constraint of a non-inert type is stored, it registers as an observer
-- on its variable arguments so that future unification triggers
-- reactivation. Constraints of an inert type — one with no occurrence
-- procedure to run — register nothing, since their reactivation would
-- be a no-op; see 'storeConstraint'.
module YCHR.Internal.Runtime.Store
  ( -- * Types
    Suspension (..),

    -- * Operations
    createConstraint,
    storeConstraint,
    killConstraint,
    aliveConstraint,
    getConstraintArg,
    getConstraintType,
    idEqual,
    isConstraintType,
    getStoreSnapshot,
    getAllStoredConstraints,
    isSuspAlive,
    suspArg,
    lookupSusp,
  )
where

import Control.Monad (unless)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask)
import Data.IORef
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import YCHR.Internal.Runtime.Monad (Chr, SessionEnv (..))
import YCHR.Internal.Runtime.Trail (recordFlagWrite)
import YCHR.Internal.Runtime.Types (Suspension (..), SuspensionId (..), Value (..))
import YCHR.Internal.Runtime.Var (addObserver)
import YCHR.Internal.Types (ConstraintType (..), Name)

-- ---------------------------------------------------------------------------
-- Operations
-- ---------------------------------------------------------------------------

-- | Look up a suspension by id. Calls 'error' on miss because every id
-- in circulation must have been allocated via 'createConstraint'; a miss
-- is a runtime invariant violation, not a user-facing failure.
lookupSusp :: SuspensionId -> Chr Suspension
lookupSusp (SuspensionId sid) = do
  SessionEnv {storeById} <- ask
  m <- liftIO $ readIORef storeById
  case IntMap.lookup sid m of
    Just s -> pure s
    Nothing -> error $ "lookupSusp: unknown SuspensionId " ++ show sid

-- | Allocate a new constraint suspension. The constraint is alive but
-- not yet in the type-indexed store. Use 'storeConstraint' to add it.
createConstraint :: ConstraintType -> [Value] -> Chr SuspensionId
createConstraint cType cArgs = do
  SessionEnv {storeNextId, storeById} <- ask
  sid <- liftIO $ do
    n <- readIORef storeNextId
    writeIORef storeNextId (n + 1)
    pure (SuspensionId n)
  aliveRef <- liftIO $ newIORef True
  storedRef <- liftIO $ newIORef False
  let susp = Suspension sid cType cArgs aliveRef storedRef
  liftIO $ modifyIORef' storeById (IntMap.insert (let SuspensionId n = sid in n) susp)
  pure sid

-- | Add a constraint to the type-indexed store and, unless its type
-- is inert, register it as an observer on each of its variable
-- arguments. Idempotent: under Late Storage the compiler emits a
-- reachable 'YCHR.Internal.VM.Store' both
-- per fired kept occurrence and at the end of every activation, and
-- only the first may take effect — a second append would make the
-- constraint match twice as a partner, and a second registration would
-- reactivate it twice per binding. Returns whether this call stored
-- the constraint, so the interpreter's trace reports only stores that
-- took effect.
--
-- An /inert/ type (see 'YCHR.Internal.VM.Program'.'inertTypes') is one
-- whose activation runs no occurrence procedure, so reactivating one
-- of its constraints can only re-store it, which 'storeConstraint'
-- already refuses. Registering it as an observer would therefore buy
-- nothing and cost one enqueue-and-discard per binding of every
-- variable it mentions. @search:alt\/1@ is the case that motivates
-- this: a search path of depth @k@ would otherwise leave @k@ dead
-- choice points observing the search variables.
storeConstraint :: SuspensionId -> Chr Bool
storeConstraint sid = do
  susp <- lookupSusp sid
  alreadyStored <- liftIO $ readIORef susp.stored
  if alreadyStored
    then pure False
    else do
      -- Defensive rather than load-bearing, unlike the 'alive' write
      -- in 'killConstraint'. A search choice point only happens at
      -- quiescence, when no activation is in progress, and 'stored'
      -- can only flip inside the activation that created the
      -- suspension — so a suspension whose flag flips inside a branch
      -- is also absent from that branch's 'storeById' snapshot and
      -- disappears wholesale on restore. Trailing it anyway keeps the
      -- invariant statable as "suspension flags are trailed" instead
      -- of resting on that argument.
      recordFlagWrite susp.stored
      liftIO $ writeIORef susp.stored True
      SessionEnv {storeByType, inertTypes} <- ask
      let ConstraintType idx = susp.suspType
      liftIO $ modifyIORef' storeByType (IntMap.adjust (Seq.|> susp) idx)
      unless (IntSet.member idx inertTypes) $ mapM_ (addObserver sid) susp.args
      pure True

-- | Kill a constraint (set alive to False).
killConstraint :: SuspensionId -> Chr ()
killConstraint sid = do
  Suspension {alive} <- lookupSusp sid
  recordFlagWrite alive
  liftIO $ writeIORef alive False

-- | Check if a constraint is still alive.
aliveConstraint :: SuspensionId -> Chr Bool
aliveConstraint sid = do
  Suspension {alive} <- lookupSusp sid
  liftIO $ readIORef alive

-- | Get a constraint argument by 0-based index.
getConstraintArg :: SuspensionId -> Int -> Chr Value
getConstraintArg sid idx = do
  Suspension {args = sargs} <- lookupSusp sid
  if idx >= 0 && idx < length sargs
    then pure (sargs !! idx)
    else error $ "getConstraintArg: index " ++ show idx ++ " out of bounds"

-- | Get the constraint type of a suspension.
getConstraintType :: SuspensionId -> Chr ConstraintType
getConstraintType sid = do
  Suspension {suspType} <- lookupSusp sid
  pure suspType

-- | Compare two suspension IDs for equality. Pure.
idEqual :: SuspensionId -> SuspensionId -> Bool
idEqual = (==)

-- | Check if a suspension has the given constraint type.
isConstraintType :: SuspensionId -> ConstraintType -> Chr Bool
isConstraintType sid cType = do
  t <- getConstraintType sid
  pure (t == cType)

-- | Get a snapshot of all suspensions of a given type. The returned
-- 'Seq' is an immutable snapshot: new constraints appended after this
-- call are invisible to the iterator.
getStoreSnapshot :: ConstraintType -> Chr (Seq Suspension)
getStoreSnapshot (ConstraintType idx) = do
  SessionEnv {storeByType} <- ask
  liftIO $ IntMap.findWithDefault Seq.empty idx <$> readIORef storeByType

-- | Return a snapshot of every constraint type in the store, paired with
-- its source name and the sequence of stored suspensions. Types are
-- returned in 'ConstraintType' index order. The returned 'Seq's are
-- immutable snapshots; callers still need to filter out dead suspensions
-- via 'isSuspAlive'.
getAllStoredConstraints :: Chr [(Name, Seq Suspension)]
getAllStoredConstraints = do
  SessionEnv {storeByType, storeTypeNames} <- ask
  storeMap <- liftIO (readIORef storeByType)
  pure
    [ (name, IntMap.findWithDefault Seq.empty i storeMap)
    | (i, name) <- IntMap.toAscList storeTypeNames
    ]

-- | Check if a suspension is alive by reading its IORef.
isSuspAlive :: Suspension -> Chr Bool
isSuspAlive Suspension {alive} = liftIO $ readIORef alive

-- | Get a suspension argument by 0-based index. Pure.
suspArg :: Suspension -> Int -> Value
suspArg Suspension {args = sargs} idx = sargs !! idx
