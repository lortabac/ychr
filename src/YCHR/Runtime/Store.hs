{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

-- | Constraint store for the CHR Haskell runtime.
--
-- Manages constraint suspensions: creation, storage, killing, liveness
-- checking, field access, and snapshot-based iteration. Integrates with
-- the observer/reactivation mechanism in "YCHR.Runtime.Var": when a
-- constraint is stored, it registers as an observer on its variable
-- arguments so that future unification triggers reactivation.
module YCHR.Runtime.Store
  ( -- * Types
    Suspension (..),
    StoreState,

    -- * Effect
    CHRStore,
    runCHRStore,

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
  )
where

import Data.IORef
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Vector qualified as V
import Data.Vector.Mutable (IOVector)
import Data.Vector.Mutable qualified as MV
import Effectful
import Effectful.Dispatch.Static
import YCHR.Runtime.Types (SuspensionId (..), Value (..))
import YCHR.Runtime.Var (Unify, addObserver, deref)
import YCHR.Types (ConstraintType (..))

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

-- | A constraint suspension in the store.
data Suspension = Suspension
  { suspId :: !SuspensionId,
    suspType :: !ConstraintType,
    args :: ![Value],
    alive :: !(IORef Bool)
  }

-- | Internal state of the constraint store.
data StoreState = StoreState
  { byType :: !(IOVector (Seq Suspension)),
    -- | Source name of each constraint type, indexed by 'ConstraintType'.
    -- Parallel to 'byType'. Used by introspection (e.g. @print_store@).
    typeNames :: !(Vector Text),
    byId :: !(IORef (IntMap Suspension)),
    nextId :: !(IORef Int)
  }

-- ---------------------------------------------------------------------------
-- Effect
-- ---------------------------------------------------------------------------

data CHRStore :: Effect

type instance DispatchOf CHRStore = Static WithSideEffects

newtype instance StaticRep CHRStore = CHRStoreRep StoreState

-- | Run a computation that uses 'CHRStore'. The argument is the list of
-- constraint type source names, indexed by 'ConstraintType'; its length
-- determines the number of distinct types and the store pre-allocates a
-- vector of that size.
runCHRStore :: (IOE :> es) => [Text] -> Eff (CHRStore : es) a -> Eff es a
runCHRStore typeNameList m = do
  let numTypes = length typeNameList
  byType <- liftIO $ MV.replicate numTypes Seq.empty
  byId <- liftIO $ newIORef IntMap.empty
  nextId <- liftIO $ newIORef 0
  evalStaticRep (CHRStoreRep (StoreState byType (V.fromList typeNameList) byId nextId)) m

-- ---------------------------------------------------------------------------
-- Internal helpers
-- ---------------------------------------------------------------------------

getStoreState :: (CHRStore :> es) => Eff es StoreState
getStoreState = do
  CHRStoreRep st <- getStaticRep
  pure st

lookupSusp :: (CHRStore :> es) => SuspensionId -> Eff es Suspension
lookupSusp (SuspensionId sid) = do
  st <- getStoreState
  m <- unsafeEff_ $ readIORef st.byId
  case IntMap.lookup sid m of
    Just s -> pure s
    Nothing -> error $ "lookupSusp: unknown SuspensionId " ++ show sid

-- ---------------------------------------------------------------------------
-- Operations
-- ---------------------------------------------------------------------------

-- | Allocate a new constraint suspension. The constraint is alive but
-- not yet in the type-indexed store. Use 'storeConstraint' to add it.
createConstraint :: (CHRStore :> es) => ConstraintType -> [Value] -> Eff es SuspensionId
createConstraint cType args = do
  st <- getStoreState
  sid <- unsafeEff_ $ do
    n <- readIORef st.nextId
    writeIORef st.nextId (n + 1)
    pure (SuspensionId n)
  aliveRef <- unsafeEff_ $ newIORef True
  let susp = Suspension sid cType args aliveRef
  unsafeEff_ $ modifyIORef' st.byId (IntMap.insert (let SuspensionId n = sid in n) susp)
  pure sid

-- | Add a constraint to the type-indexed store and register it as an
-- observer on each of its variable arguments.
storeConstraint :: (CHRStore :> es, Unify :> es) => SuspensionId -> Eff es ()
storeConstraint sid = do
  susp <- lookupSusp sid
  st <- getStoreState
  let ConstraintType idx = susp.suspType
  unsafeEff_ $ MV.modify st.byType (Seq.|> susp) idx
  -- Register as observer on each variable argument
  mapM_ (registerObserver sid) susp.args

-- | Register a suspension as an observer on a value, if it's an unbound variable.
registerObserver :: (CHRStore :> es, Unify :> es) => SuspensionId -> Value -> Eff es ()
registerObserver sid val = do
  d <- deref val
  case d of
    VVar _ -> addObserver sid d
    _ -> pure ()

-- | Kill a constraint (set alive to False).
killConstraint :: (CHRStore :> es) => SuspensionId -> Eff es ()
killConstraint sid = do
  susp <- lookupSusp sid
  unsafeEff_ $ writeIORef susp.alive False

-- | Check if a constraint is still alive.
aliveConstraint :: (CHRStore :> es) => SuspensionId -> Eff es Bool
aliveConstraint sid = do
  susp <- lookupSusp sid
  unsafeEff_ $ readIORef susp.alive

-- | Get a constraint argument by 0-based index.
getConstraintArg :: (CHRStore :> es) => SuspensionId -> Int -> Eff es Value
getConstraintArg sid idx = do
  susp <- lookupSusp sid
  if idx >= 0 && idx < length susp.args
    then pure (susp.args !! idx)
    else error $ "getConstraintArg: index " ++ show idx ++ " out of bounds"

-- | Get the constraint type of a suspension.
getConstraintType :: (CHRStore :> es) => SuspensionId -> Eff es ConstraintType
getConstraintType sid = (.suspType) <$> lookupSusp sid

-- | Compare two suspension IDs for equality. Pure.
idEqual :: SuspensionId -> SuspensionId -> Bool
idEqual = (==)

-- | Check if a suspension has the given constraint type.
isConstraintType :: (CHRStore :> es) => SuspensionId -> ConstraintType -> Eff es Bool
isConstraintType sid cType = do
  t <- getConstraintType sid
  pure (t == cType)

-- | Get a snapshot of all suspensions of a given type. The returned
-- 'Seq' is an immutable snapshot: new constraints appended after this
-- call are invisible to the iterator.
getStoreSnapshot :: (CHRStore :> es) => ConstraintType -> Eff es (Seq Suspension)
getStoreSnapshot (ConstraintType idx) = do
  st <- getStoreState
  if idx >= 0 && idx < MV.length st.byType
    then unsafeEff_ $ MV.read st.byType idx
    else pure Seq.empty

-- | Return a snapshot of every constraint type in the store, paired with
-- its source name (from the 'runCHRStore' argument) and the sequence of
-- stored suspensions. Types are returned in 'ConstraintType' index order.
-- The returned 'Seq's are immutable snapshots; callers still need to
-- filter out dead suspensions via 'isSuspAlive'.
getAllStoredConstraints :: (CHRStore :> es) => Eff es [(Text, Seq Suspension)]
getAllStoredConstraints = do
  st <- getStoreState
  let n = MV.length st.byType
  unsafeEff_ $
    traverse
      ( \i -> do
          susps <- MV.read st.byType i
          let name = st.typeNames V.! i
          pure (name, susps)
      )
      [0 .. n - 1]

-- | Check if a suspension is alive by reading its IORef.
isSuspAlive :: (CHRStore :> es) => Suspension -> Eff es Bool
isSuspAlive susp = unsafeEff_ $ readIORef susp.alive

-- | Get a suspension argument by 0-based index. Pure.
suspArg :: Suspension -> Int -> Value
suspArg susp idx = susp.args !! idx
