{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

-- | Reactivation queue for the CHR Haskell runtime.
--
-- Accumulates constraint suspension IDs that need reactivation (typically
-- enqueued as a side effect of unification) and provides a drain operation
-- that processes them one at a time. The drain re-reads the queue on every
-- iteration so that IDs enqueued by reentrant unifications during the
-- callback are picked up.
module YCHR.Internal.Runtime.Reactivation
  ( -- * Operations
    enqueue,
    enqueueObservers,
    drainQueue,
  )
where

import Control.Monad (filterM)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask)
import Data.IORef
import Data.IntMap.Strict qualified as IntMap
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import YCHR.Internal.Runtime.Monad (Chr, SessionEnv (..))
import YCHR.Internal.Runtime.Types (Suspension (..), SuspensionId (..))

-- | Append suspension IDs to the back of the queue.
enqueue :: [SuspensionId] -> Chr ()
enqueue ids = do
  SessionEnv {reactQueue} <- ask
  liftIO $ modifyIORef' reactQueue (<> Seq.fromList ids)

-- | Enqueue the observers returned by a binding
-- ('YCHR.Internal.Runtime.Var.unify'), keeping only the ids that name
-- a live suspension of /this/ session.
--
-- Two kinds of id are dropped. An id with no suspension in this
-- session's store is /foreign/: logical variables are shared across
-- forked sessions ("YCHR.Internal.Runtime.Search") while suspension
-- ids are globally unique, so a variable's observer list may carry
-- ids that belong to a different session — which this session cannot
-- reactivate. An id whose suspension is dead is /stale/: a kill only
-- flips the @alive@ flag, and nothing ever removes an id from an
-- observer list, so a variable observed by a constraint that has
-- since been killed keeps naming it forever. That matters most under
-- search, where a path of depth @k@ leaves @k@ dead choice points
-- observing the search variable.
--
-- Dropping the stale ones here rather than at the drain saves the
-- queue append, the pop and a second lookup for each. The drain keeps
-- its own liveness check regardless: a constraint can die between
-- being enqueued and being reached.
--
-- Returns how many ids were actually enqueued, which is what the
-- tracer reports as the reactivation count of a unification.
enqueueObservers :: [SuspensionId] -> Chr Int
enqueueObservers ids = do
  SessionEnv {storeById} <- ask
  m <- liftIO $ readIORef storeById
  live <- liftIO $ filterM (isLiveIn m) ids
  enqueue live
  pure (length live)
  where
    isLiveIn m (SuspensionId n) = case IntMap.lookup n m of
      Nothing -> pure False
      Just susp -> readIORef susp.alive

-- | Drain the queue one element at a time, calling the callback for each.
-- Re-reads the queue on every iteration so that IDs enqueued by the
-- callback (via reentrant unifications) are picked up.
drainQueue :: (SuspensionId -> Chr ()) -> Chr ()
drainQueue callback = go
  where
    go = do
      SessionEnv {reactQueue} <- ask
      mNext <- liftIO $ atomicModifyIORef' reactQueue $ \case
        Empty -> (Seq.empty, Nothing)
        x :<| rest -> (rest, Just x)
      case mNext of
        Nothing -> pure ()
        Just sid -> callback sid >> go
