{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

-- | Propagation history for the CHR Haskell runtime.
--
-- Tracks which rule has fired with which combination of constraint
-- identifiers, to prevent redundant re-firing of propagation rules.

module YCHR.Runtime.History
  ( -- * Effect
    PropHistory
  , runPropHistory

    -- * Operations
  , addHistory
  , notInHistory
  ) where

import Data.IORef
import Data.Set (Set)
import qualified Data.Set as Set

import Effectful
import Effectful.Dispatch.Static

import YCHR.Runtime.Types (SuspensionId (..))
import YCHR.VM (RuleName)


-- ---------------------------------------------------------------------------
-- Effect
-- ---------------------------------------------------------------------------

data PropHistory :: Effect
type instance DispatchOf PropHistory = Static WithSideEffects
newtype instance StaticRep PropHistory = PropHistoryRep (IORef (Set (RuleName, [SuspensionId])))

-- | Run a computation that uses 'PropHistory', starting with an empty history.
runPropHistory :: IOE :> es => Eff (PropHistory : es) a -> Eff es a
runPropHistory m = do
  ref <- liftIO $ newIORef Set.empty
  evalStaticRep (PropHistoryRep ref) m


-- ---------------------------------------------------------------------------
-- Operations
-- ---------------------------------------------------------------------------

getRef :: PropHistory :> es => Eff es (IORef (Set (RuleName, [SuspensionId])))
getRef = do
  PropHistoryRep ref <- getStaticRep
  pure ref

-- | Record that a rule has fired with the given constraint identifiers.
addHistory :: PropHistory :> es => RuleName -> [SuspensionId] -> Eff es ()
addHistory ruleName ids = do
  ref <- getRef
  unsafeEff_ $ modifyIORef' ref (Set.insert (ruleName, ids))

-- | Check that a rule has /not/ fired with the given constraint identifiers.
-- Returns 'True' if the entry is absent (i.e. the rule may fire).
notInHistory :: PropHistory :> es => RuleName -> [SuspensionId] -> Eff es Bool
notInHistory ruleName ids = do
  ref <- getRef
  unsafeEff_ $ Set.notMember (ruleName, ids) <$> readIORef ref
