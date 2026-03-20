{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

-- | Reactivation queue for the CHR Haskell runtime.
--
-- Accumulates constraint suspension IDs that need reactivation (typically
-- enqueued as a side effect of unification) and provides a drain operation
-- that processes them one at a time. The drain re-reads the queue on every
-- iteration so that IDs enqueued by reentrant unifications during the
-- callback are picked up.

module YCHR.Runtime.Reactivation
  ( -- * Effect
    ReactQueue
  , runReactQueue

    -- * Operations
  , enqueue
  , drainQueue
  ) where

import Data.IORef
import Data.Sequence (Seq (..))
import qualified Data.Sequence as Seq

import Effectful
import Effectful.Dispatch.Static

import YCHR.Runtime.Types (SuspensionId (..))


-- ---------------------------------------------------------------------------
-- Effect
-- ---------------------------------------------------------------------------

data ReactQueue :: Effect
type instance DispatchOf ReactQueue = Static WithSideEffects
newtype instance StaticRep ReactQueue = ReactQueueRep (IORef (Seq SuspensionId))

-- | Run a computation that uses 'ReactQueue', starting with an empty queue.
runReactQueue :: IOE :> es => Eff (ReactQueue : es) a -> Eff es a
runReactQueue m = do
  ref <- liftIO $ newIORef Seq.empty
  evalStaticRep (ReactQueueRep ref) m


-- ---------------------------------------------------------------------------
-- Operations
-- ---------------------------------------------------------------------------

getRef :: ReactQueue :> es => Eff es (IORef (Seq SuspensionId))
getRef = do
  ReactQueueRep ref <- getStaticRep
  pure ref

-- | Append suspension IDs to the back of the queue.
enqueue :: ReactQueue :> es => [SuspensionId] -> Eff es ()
enqueue ids = do
  ref <- getRef
  unsafeEff_ $ modifyIORef' ref (<> Seq.fromList ids)

-- | Drain the queue one element at a time, calling the callback for each.
-- Re-reads the queue on every iteration so that IDs enqueued by the
-- callback (via reentrant unifications) are picked up.
drainQueue :: ReactQueue :> es => (SuspensionId -> Eff es ()) -> Eff es ()
drainQueue callback = go
  where
    go = do
      ref <- getRef
      mNext <- unsafeEff_ $ atomicModifyIORef' ref $ \case
        Empty      -> (Seq.empty, Nothing)
        x :<| rest -> (rest, Just x)
      case mNext of
        Nothing  -> pure ()
        Just sid -> callback sid >> go
