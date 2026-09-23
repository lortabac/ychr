{-# LANGUAGE OverloadedStrings #-}

module YCHR.Runtime.ReactivationTest (tests) where

import Control.Monad.IO.Class (liftIO)
import Data.IORef
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import YCHR.Internal.Runtime.Monad (Chr, initSessionEnv, runChr)
import YCHR.Internal.Runtime.Reactivation
import YCHR.Internal.Runtime.Store (createConstraint, killConstraint)
import YCHR.Internal.Runtime.Types (SuspensionId (..), Value (..))
import YCHR.Internal.Types (ConstraintType (..), Name (..))

tests :: TestTree
tests =
  testGroup
    "YCHR.Internal.Runtime.Reactivation"
    [ orderTests,
      reentrancyTests,
      observerTests,
      miscTests
    ]

runReactEnv :: Chr a -> IO a
runReactEnv action = do
  env <- initSessionEnv [] [] [] Map.empty Map.empty Map.empty Map.empty Map.empty Set.empty
  runChr action env

-- | A session with one constraint-type slot, so 'createConstraint' has
-- somewhere to put a suspension. 'enqueueObservers' reads the
-- id-indexed map, which 'createConstraint' populates on its own, so
-- nothing here has to be stored.
runReactStoreEnv :: Chr a -> IO a
runReactStoreEnv action = do
  env <-
    initSessionEnv
      [Unqualified ""]
      []
      []
      Map.empty
      Map.empty
      Map.empty
      Map.empty
      Map.empty
      Set.empty
  runChr action env

-- | Drain the queue, collecting all IDs in order.
drainCollect :: Chr [SuspensionId]
drainCollect = do
  ref <- liftIO $ newIORef []
  drainQueue $ \sid -> liftIO $ modifyIORef' ref (sid :)
  liftIO $ reverse <$> readIORef ref

orderTests :: TestTree
orderTests =
  testGroup
    "FIFO order"
    [ testCase "multiple enqueues preserve combined order" $ do
        ids <- runReactEnv $ do
          enqueue [SuspensionId 0, SuspensionId 1]
          enqueue [SuspensionId 2, SuspensionId 3]
          drainCollect
        ids @?= [SuspensionId 0, SuspensionId 1, SuspensionId 2, SuspensionId 3]
    ]

reentrancyTests :: TestTree
reentrancyTests =
  testGroup
    "reentrancy"
    [ testCase "callback enqueues more IDs" $ do
        ids <- runReactEnv $ do
          ref <- liftIO $ newIORef []
          enqueue [SuspensionId 0]
          drainQueue $ \sid -> do
            liftIO $ modifyIORef' ref (sid :)
            case sid of
              SuspensionId 0 -> enqueue [SuspensionId 10, SuspensionId 11]
              _ -> pure ()
          liftIO $ reverse <$> readIORef ref
        ids @?= [SuspensionId 0, SuspensionId 10, SuspensionId 11],
      testCase "deep reentrancy (N < 3 -> enqueue N+1)" $ do
        ids <- runReactEnv $ do
          ref <- liftIO $ newIORef []
          enqueue [SuspensionId 0]
          drainQueue $ \sid@(SuspensionId n) -> do
            liftIO $ modifyIORef' ref (sid :)
            if n < 3
              then enqueue [SuspensionId (n + 1)]
              else pure ()
          liftIO $ reverse <$> readIORef ref
        ids @?= [SuspensionId 0, SuspensionId 1, SuspensionId 2, SuspensionId 3]
    ]

-- | 'enqueueObservers' keeps only the ids naming a live suspension of
-- this session, and reports how many it kept. A variable's observer
-- list is never pruned, so both the foreign ids of another session and
-- the stale ids of killed constraints reach it.
observerTests :: TestTree
observerTests =
  testGroup
    "enqueueObservers"
    [ testCase "live ids are enqueued in order" $ do
        (ids, n) <- runReactStoreEnv $ do
          a <- createConstraint (ConstraintType 0) [VInt 1]
          b <- createConstraint (ConstraintType 0) [VInt 2]
          n <- enqueueObservers [a, b]
          ids <- drainCollect
          pure (ids, n)
        ids @?= [SuspensionId 0, SuspensionId 1]
        n @?= 2,
      testCase "a killed constraint is dropped" $ do
        (ids, n) <- runReactStoreEnv $ do
          dead <- createConstraint (ConstraintType 0) [VInt 1]
          live <- createConstraint (ConstraintType 0) [VInt 2]
          killConstraint dead
          n <- enqueueObservers [dead, live]
          ids <- drainCollect
          pure (ids, n)
        ids @?= [SuspensionId 1]
        n @?= 1,
      testCase "an id from another session is dropped" $ do
        (ids, n) <- runReactStoreEnv $ do
          n <- enqueueObservers [SuspensionId 99]
          ids <- drainCollect
          pure (ids, n)
        ids @?= []
        n @?= 0
    ]

miscTests :: TestTree
miscTests =
  testGroup
    "misc"
    [ testCase "queue empty after drain" $ do
        ids <- runReactEnv $ do
          enqueue [SuspensionId 0, SuspensionId 1]
          _ <- drainCollect
          drainCollect
        ids @?= [],
      testCase "duplicates preserved" $ do
        ids <- runReactEnv $ do
          enqueue [SuspensionId 5, SuspensionId 5]
          drainCollect
        ids @?= [SuspensionId 5, SuspensionId 5]
    ]
