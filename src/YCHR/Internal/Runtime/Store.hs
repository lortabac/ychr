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
    indexedPositionsFor,
    candidateSuspensions,
    getAllStoredConstraints,
    isSuspAlive,
    suspArg,
    lookupSusp,
  )
where

import Control.Monad (when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask)
import Data.Foldable (toList)
import Data.IORef
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import YCHR.Internal.Runtime.Index
  ( GroundKey,
    candidateSlots,
    indexThreshold,
    insertConstraints,
    typeIndexed,
  )
import YCHR.Internal.Runtime.Monad (Chr, SessionEnv (..))
import YCHR.Internal.Runtime.Trail (recordFlagWrite)
import YCHR.Internal.Runtime.Types (Suspension (..), SuspensionId (..), Value (..))
import YCHR.Internal.Runtime.Var (addObserver, addObserverAndKey, groundKey)
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

-- | Add a constraint to the type-indexed store; unless its type is
-- inert, register it as an observer on each of its variable arguments;
-- and record it in the per-argument indexes the program's index
-- conditions can be answered from. Idempotent: under Late Storage the
-- compiler emits a reachable 'YCHR.Internal.VM.Store' both per fired
-- kept occurrence and at the end of every activation, and only the
-- first may take effect — a second append would make the constraint
-- match twice as a partner, a second registration would reactivate it
-- twice per binding, and a second index entry would file it twice.
-- Returns whether this call stored the constraint, so the
-- interpreter's trace reports only stores that took effect.
--
-- An /inert/ type (see 'YCHR.Internal.VM.Program'.'inertTypes') is one
-- whose activation runs no occurrence procedure, so reactivating one
-- of its constraints can only re-store it, which 'storeConstraint'
-- already refuses. Registering it as an observer would therefore buy
-- nothing and cost one enqueue-and-discard per binding of every
-- variable it mentions. @search:alt\/1@ is the case that motivates
-- this: a search path of depth @k@ would otherwise leave @k@ dead
-- choice points observing the search variables.
--
-- The index entries are the /Indexing/ optimization of the paper
-- (§5.3); see "YCHR.Internal.Runtime.Index" for the reasoning. The
-- argument walk that registers observers is the same one that computes
-- an indexed argument's ground key ('addObserverAndKey'), so a store
-- pays one traversal per argument, not two — and only once the type's
-- bucket is big enough to be worth indexing at all ('indexThreshold'),
-- below which this is the pre-index path exactly.
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
      SessionEnv {storeByType, storeIndex, indexPositions, inertTypes} <- ask
      let cType = susp.suspType
          idx = cType.unConstraintType
          positions = IntMap.findWithDefault IntSet.empty idx indexPositions
          observe = not (IntSet.member idx inertTypes)
          append = IntMap.adjust (Seq.|> susp) idx
          registerObservers = when observe $ mapM_ (addObserver sid) susp.args
      if IntSet.null positions
        then do
          -- No position of this type is ever looked up through an
          -- index, so this is the pre-index path exactly: the observer
          -- registration, and nothing else.
          registerObservers
          liftIO $ modifyIORef' storeByType append
          pure True
        else do
          storeMap <- liftIO $ readIORef storeByType
          si <- liftIO $ readIORef storeIndex
          let owned = IntMap.findWithDefault Seq.empty idx storeMap
              slot = Seq.length owned
              -- @slot@ is where this store lands, so the bucket holds
              -- @slot + 1@ constraints once it has.
              worthIndexing = slot + 1 >= indexThreshold || typeIndexed cType si
          if not worthIndexing
            then do
              -- Too small to be worth indexing: still the pre-index
              -- path, and the whole bucket is filed in one pass later
              -- if it grows past the threshold.
              registerObservers
              liftIO $ modifyIORef' storeByType append
              pure True
            else do
              -- One traversal per argument: register the observers
              -- (what this did before the index existed), and at an
              -- indexed position also build the argument's ground key.
              let walk (j, arg)
                    | IntSet.member j positions =
                        if observe then addObserverAndKey sid arg else groundKey arg
                    | observe = Nothing <$ addObserver sid arg
                    | otherwise = pure Nothing
                  -- The pass that crosses the threshold files the
                  -- bucket's existing suspensions too. Their observers
                  -- were registered when they were stored, so only
                  -- their keys are wanted here.
                  indexedPositions = IntSet.toAscList positions
                  entriesOf s =
                    zip indexedPositions
                      <$> traverse (\j -> groundKey (suspArg s j)) indexedPositions
                  withEntries (s, s') = fmap ((,) s) (entriesOf s')
              backlog <-
                if typeIndexed cType si
                  then pure []
                  else traverse withEntries (zip [0 ..] (toList owned))
              keys <- traverse walk (zip [0 ..] susp.args)
              let entries = [(j, key) | (j, key) <- zip [0 ..] keys, IntSet.member j positions]
              liftIO $ do
                modifyIORef' storeByType append
                -- The index is a persistent value behind one reference,
                -- like the store it describes, so a search snapshot
                -- restores the two together
                -- ('YCHR.Internal.Runtime.Search').
                let stores = backlog ++ [(slot, entries)]
                modifyIORef' storeIndex (insertConstraints cType stores)
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

-- | The argument positions the store can answer an index lookup for
-- right now, or 'Nothing' when it has no index for this type — no
-- position of it is ever looked up, or its bucket has not yet reached
-- 'indexThreshold'. A caller that gets 'Nothing' scans, and skips
-- computing a lookup key it would not use.
indexedPositionsFor :: ConstraintType -> Chr (Maybe IntSet)
indexedPositionsFor cType = do
  SessionEnv {storeIndex, indexPositions} <- ask
  si <- liftIO $ readIORef storeIndex
  let ConstraintType idx = cType
      positions = IntMap.findWithDefault IntSet.empty idx indexPositions
  pure $
    if not (IntSet.null positions) && typeIndexed cType si
      then Just positions
      else Nothing

-- | The stored suspensions of a type that may hold an argument at
-- position @pos@ 'equal' to a value whose ground key is @key@, in store
-- order.
--
-- This is the lookup half of the paper's /Indexing/ optimization
-- (§5.3): where 'getStoreSnapshot' hands back the whole type bucket,
-- this hands back the bucket's key plus the position's non-ground
-- fallback set — a superset of the suspensions that can match, which
-- the caller's per-candidate condition check then narrows. Ask only
-- for a @(type, pos)@ pair 'YCHR.Internal.VM.Index.indexablePositions'
-- reports: a position the store was not told to index has no entries,
-- and an empty answer there would lose every candidate. See
-- "YCHR.Internal.Runtime.Index".
--
-- A type the store has not indexed — no position of it is ever looked
-- up, or its bucket has not reached 'indexThreshold' — is answered by
-- the whole bucket, which is the pre-index behaviour exactly. So is a
-- candidate set that is not smaller than the bucket: the index has to
-- prune to be worth the per-candidate bookkeeping it adds. Between them
-- those two fallbacks keep the index a win-or-neutral change however
-- small the store is.
candidateSuspensions :: ConstraintType -> Int -> GroundKey -> Chr [Suspension]
candidateSuspensions cType pos key = do
  SessionEnv {storeByType, storeIndex} <- ask
  let ConstraintType idx = cType
  (snapshot, si) <- liftIO $ do
    bt <- readIORef storeByType
    sx <- readIORef storeIndex
    pure (IntMap.findWithDefault Seq.empty idx bt, sx)
  let slots = candidateSlots cType pos key si
  if not (typeIndexed cType si) || IntSet.size slots >= Seq.length snapshot
    then pure (toList snapshot)
    else
      pure
        [ susp
        | slot <- IntSet.toAscList slots,
          Just susp <- [Seq.lookup slot snapshot]
        ]

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

-- | Get a suspension argument by 0-based index. Pure. Calls 'error' on an
-- out-of-range index, mirroring 'getConstraintArg'; an out-of-range index is
-- a runtime invariant violation, not a user-facing failure.
suspArg :: Suspension -> Int -> Value
suspArg Suspension {args = sargs} idx
  | idx >= 0 && idx < length sargs = sargs !! idx
  | otherwise = error $ "suspArg: index " ++ show idx ++ " out of bounds"
