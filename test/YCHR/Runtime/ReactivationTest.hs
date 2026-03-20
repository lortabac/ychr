{-# LANGUAGE DataKinds #-}

module YCHR.Runtime.ReactivationTest (tests) where

import Data.IORef
import Effectful
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import YCHR.Runtime.Reactivation
import YCHR.Runtime.Types (SuspensionId (..))

tests :: TestTree
tests =
  testGroup
    "YCHR.Runtime.Reactivation"
    [ emptyTests,
      orderTests,
      reentrancyTests,
      miscTests
    ]

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

runReactEnv :: Eff [ReactQueue, IOE] a -> IO a
runReactEnv = runEff . runReactQueue

-- | Drain the queue, collecting all IDs in order.
drainCollect :: (ReactQueue :> es, IOE :> es) => Eff es [SuspensionId]
drainCollect = do
  ref <- liftIO $ newIORef []
  drainQueue $ \sid -> liftIO $ modifyIORef' ref (sid :)
  liftIO $ reverse <$> readIORef ref

-- ---------------------------------------------------------------------------
-- Empty queue
-- ---------------------------------------------------------------------------

emptyTests :: TestTree
emptyTests =
  testGroup
    "empty queue"
    [ testCase "drain on empty does nothing" $ do
        ids <- runReactEnv drainCollect
        ids @?= []
    ]

-- ---------------------------------------------------------------------------
-- FIFO order
-- ---------------------------------------------------------------------------

orderTests :: TestTree
orderTests =
  testGroup
    "FIFO order"
    [ testCase "single enqueue preserves order" $ do
        ids <- runReactEnv $ do
          enqueue [SuspensionId 0, SuspensionId 1]
          drainCollect
        ids @?= [SuspensionId 0, SuspensionId 1],
      testCase "multiple enqueues preserve combined order" $ do
        ids <- runReactEnv $ do
          enqueue [SuspensionId 0, SuspensionId 1]
          enqueue [SuspensionId 2, SuspensionId 3]
          drainCollect
        ids @?= [SuspensionId 0, SuspensionId 1, SuspensionId 2, SuspensionId 3],
      testCase "empty list enqueue is a no-op" $ do
        ids <- runReactEnv $ do
          enqueue []
          drainCollect
        ids @?= []
    ]

-- ---------------------------------------------------------------------------
-- Reentrancy
-- ---------------------------------------------------------------------------

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

-- ---------------------------------------------------------------------------
-- Misc
-- ---------------------------------------------------------------------------

miscTests :: TestTree
miscTests =
  testGroup
    "misc"
    [ testCase "queue empty after drain" $ do
        ids <- runReactEnv $ do
          enqueue [SuspensionId 0, SuspensionId 1]
          _ <- drainCollect -- first drain
          drainCollect -- second drain should be empty
        ids @?= [],
      testCase "duplicates preserved" $ do
        ids <- runReactEnv $ do
          enqueue [SuspensionId 5, SuspensionId 5]
          drainCollect
        ids @?= [SuspensionId 5, SuspensionId 5]
    ]
