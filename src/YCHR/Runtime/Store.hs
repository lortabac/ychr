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
    isSuspAlive,
    suspArg,
  )
where

import Data.IORef
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Effectful
import Effectful.Dispatch.Static
import YCHR.Runtime.Types (SuspensionId (..), Value (..))
import YCHR.Runtime.Var (Unify, addObserver, deref)

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

-- | A constraint suspension in the store.
data Suspension = Suspension
  { suspId :: !SuspensionId,
    suspType :: !String,
    suspArgs :: ![Value],
    suspAlive :: !(IORef Bool)
  }

-- | Internal state of the constraint store.
data StoreState = StoreState
  { storeByType :: !(IORef (Map String (Seq Suspension))),
    storeById :: !(IORef (IntMap Suspension)),
    storeNextId :: !(IORef Int)
  }

-- ---------------------------------------------------------------------------
-- Effect
-- ---------------------------------------------------------------------------

data CHRStore :: Effect

type instance DispatchOf CHRStore = Static WithSideEffects

newtype instance StaticRep CHRStore = CHRStoreRep StoreState

-- | Run a computation that uses 'CHRStore'.
runCHRStore :: (IOE :> es) => Eff (CHRStore : es) a -> Eff es a
runCHRStore m = do
  byType <- liftIO $ newIORef Map.empty
  byId <- liftIO $ newIORef IntMap.empty
  nextId <- liftIO $ newIORef 0
  evalStaticRep (CHRStoreRep (StoreState byType byId nextId)) m

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
  byId <- unsafeEff_ $ readIORef (storeById st)
  case IntMap.lookup sid byId of
    Just s -> pure s
    Nothing -> error $ "lookupSusp: unknown SuspensionId " ++ show sid

-- ---------------------------------------------------------------------------
-- Operations
-- ---------------------------------------------------------------------------

-- | Allocate a new constraint suspension. The constraint is alive but
-- not yet in the type-indexed store. Use 'storeConstraint' to add it.
createConstraint :: (CHRStore :> es) => String -> [Value] -> Eff es SuspensionId
createConstraint cType args = do
  st <- getStoreState
  sid <- unsafeEff_ $ do
    n <- readIORef (storeNextId st)
    writeIORef (storeNextId st) (n + 1)
    pure (SuspensionId n)
  aliveRef <- unsafeEff_ $ newIORef True
  let susp = Suspension sid cType args aliveRef
  unsafeEff_ $ modifyIORef' (storeById st) (IntMap.insert (let SuspensionId n = sid in n) susp)
  pure sid

-- | Add a constraint to the type-indexed store and register it as an
-- observer on each of its variable arguments.
storeConstraint :: (CHRStore :> es, Unify :> es) => SuspensionId -> Eff es ()
storeConstraint sid = do
  susp <- lookupSusp sid
  st <- getStoreState
  unsafeEff_ $ modifyIORef' (storeByType st) $ \m ->
    let existing = Map.findWithDefault Seq.empty (suspType susp) m
     in Map.insert (suspType susp) (existing Seq.|> susp) m
  -- Register as observer on each variable argument
  mapM_ (registerObserver sid) (suspArgs susp)

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
  unsafeEff_ $ writeIORef (suspAlive susp) False

-- | Check if a constraint is still alive.
aliveConstraint :: (CHRStore :> es) => SuspensionId -> Eff es Bool
aliveConstraint sid = do
  susp <- lookupSusp sid
  unsafeEff_ $ readIORef (suspAlive susp)

-- | Get a constraint argument by 0-based index.
getConstraintArg :: (CHRStore :> es) => SuspensionId -> Int -> Eff es Value
getConstraintArg sid idx = do
  susp <- lookupSusp sid
  let args = suspArgs susp
  if idx >= 0 && idx < length args
    then pure (args !! idx)
    else error $ "getConstraintArg: index " ++ show idx ++ " out of bounds"

-- | Get the constraint type of a suspension.
getConstraintType :: (CHRStore :> es) => SuspensionId -> Eff es String
getConstraintType sid = suspType <$> lookupSusp sid

-- | Compare two suspension IDs for equality. Pure.
idEqual :: SuspensionId -> SuspensionId -> Bool
idEqual = (==)

-- | Check if a suspension has the given constraint type.
isConstraintType :: (CHRStore :> es) => SuspensionId -> String -> Eff es Bool
isConstraintType sid cType = do
  t <- getConstraintType sid
  pure (t == cType)

-- | Get a snapshot of all suspensions of a given type. The returned
-- 'Seq' is an immutable snapshot: new constraints appended after this
-- call are invisible to the iterator.
getStoreSnapshot :: (CHRStore :> es) => String -> Eff es (Seq Suspension)
getStoreSnapshot cType = do
  st <- getStoreState
  byType <- unsafeEff_ $ readIORef (storeByType st)
  pure $ Map.findWithDefault Seq.empty cType byType

-- | Check if a suspension is alive by reading its IORef.
isSuspAlive :: (CHRStore :> es) => Suspension -> Eff es Bool
isSuspAlive susp = unsafeEff_ $ readIORef (suspAlive susp)

-- | Get a suspension argument by 0-based index. Pure.
suspArg :: Suspension -> Int -> Value
suspArg susp idx = suspArgs susp !! idx
