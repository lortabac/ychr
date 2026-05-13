{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

-- | Reactivation queue for the CHR Haskell runtime.
--
-- Accumulates constraint suspension IDs that need reactivation (typically
-- enqueued as a side effect of unification) and provides a drain operation
-- that processes them one at a time. The drain re-reads the queue on every
-- iteration so that IDs enqueued by reentrant unifications during the
-- callback are picked up.
module YCHR.Runtime.Reactivation
  ( enqueue,
    drainQueue,
  )
where

import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask)
import Data.IORef
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import YCHR.Runtime.Monad (Chr, SessionEnv (..))
import YCHR.Runtime.Types (SuspensionId)

-- | Append suspension IDs to the back of the queue.
enqueue :: [SuspensionId] -> Chr ()
enqueue ids = do
  SessionEnv {reactQueue} <- ask
  liftIO $ modifyIORef' reactQueue (<> Seq.fromList ids)

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
