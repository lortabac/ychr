{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module YCHR.Runtime.HistoryTest (tests) where

import Effectful
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import YCHR.Runtime.History
import YCHR.Runtime.Types (SuspensionId (..))

tests :: TestTree
tests =
  testGroup
    "YCHR.Runtime.History"
    [ emptyTests,
      addTests,
      distinctionTests,
      miscTests
    ]

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

runHistoryEnv :: Eff [PropHistory, IOE] a -> IO a
runHistoryEnv = runEff . runPropHistory

-- ---------------------------------------------------------------------------
-- Empty history
-- ---------------------------------------------------------------------------

emptyTests :: TestTree
emptyTests =
  testGroup
    "empty history"
    [ testCase "notInHistory returns True" $ do
        r <- runHistoryEnv $ notInHistory "rule1" [SuspensionId 0]
        r @?= True
    ]

-- ---------------------------------------------------------------------------
-- After addHistory
-- ---------------------------------------------------------------------------

addTests :: TestTree
addTests =
  testGroup
    "addHistory"
    [ testCase "same entry -> notInHistory returns False" $ do
        r <- runHistoryEnv $ do
          addHistory "rule1" [SuspensionId 0, SuspensionId 1]
          notInHistory "rule1" [SuspensionId 0, SuspensionId 1]
        r @?= False,
      testCase "duplicate addHistory is idempotent" $ do
        r <- runHistoryEnv $ do
          addHistory "rule1" [SuspensionId 0]
          addHistory "rule1" [SuspensionId 0]
          notInHistory "rule1" [SuspensionId 0]
        r @?= False
    ]

-- ---------------------------------------------------------------------------
-- Distinction tests
-- ---------------------------------------------------------------------------

distinctionTests :: TestTree
distinctionTests =
  testGroup
    "distinctness"
    [ testCase "different rule name -> True" $ do
        r <- runHistoryEnv $ do
          addHistory "rule1" [SuspensionId 0]
          notInHistory "rule2" [SuspensionId 0]
        r @?= True,
      testCase "different IDs -> True" $ do
        r <- runHistoryEnv $ do
          addHistory "rule1" [SuspensionId 0]
          notInHistory "rule1" [SuspensionId 1]
        r @?= True,
      testCase "different ID order -> True" $ do
        r <- runHistoryEnv $ do
          addHistory "rule1" [SuspensionId 0, SuspensionId 1]
          notInHistory "rule1" [SuspensionId 1, SuspensionId 0]
        r @?= True
    ]

-- ---------------------------------------------------------------------------
-- Misc
-- ---------------------------------------------------------------------------

miscTests :: TestTree
miscTests =
  testGroup
    "misc"
    [ testCase "multiple independent entries" $ do
        runHistoryEnv $ do
          addHistory "r1" [SuspensionId 0]
          addHistory "r2" [SuspensionId 1]
          r1 <- notInHistory "r1" [SuspensionId 0]
          r2 <- notInHistory "r2" [SuspensionId 1]
          r3 <- notInHistory "r1" [SuspensionId 1]
          liftIO $ r1 @?= False
          liftIO $ r2 @?= False
          liftIO $ r3 @?= True,
      testCase "empty ID list works" $ do
        runHistoryEnv $ do
          r1 <- notInHistory "rule1" []
          liftIO $ r1 @?= True
          addHistory "rule1" []
          r2 <- notInHistory "rule1" []
          liftIO $ r2 @?= False
    ]
