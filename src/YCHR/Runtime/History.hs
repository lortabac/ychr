{-# LANGUAGE OverloadedRecordDot #-}

-- | Propagation history for the CHR Haskell runtime.
--
-- Tracks which rule has fired with which combination of constraint
-- identifiers, to prevent redundant re-firing of propagation rules.
module YCHR.Runtime.History
  ( addHistory,
    notInHistory,
  )
where

import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask)
import Data.IORef
import Data.Set qualified as Set
import YCHR.Runtime.Monad (Chr, SessionEnv (..))
import YCHR.Runtime.Types (SuspensionId)
import YCHR.VM (RuleId)

-- | Record that a rule has fired with the given constraint identifiers.
addHistory :: RuleId -> [SuspensionId] -> Chr ()
addHistory ruleId ids = do
  SessionEnv {history} <- ask
  liftIO $ modifyIORef' history (Set.insert (ruleId, ids))

-- | Check that a rule has /not/ fired with the given constraint identifiers.
-- Returns 'True' if the entry is absent (i.e. the rule may fire).
notInHistory :: RuleId -> [SuspensionId] -> Chr Bool
notInHistory ruleId ids = do
  SessionEnv {history} <- ask
  liftIO $ Set.notMember (ruleId, ids) <$> readIORef history
