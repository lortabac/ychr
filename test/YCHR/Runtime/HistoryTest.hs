{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module YCHR.Runtime.HistoryTest (tests) where

import Effectful
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import YCHR.Runtime.History
import YCHR.Runtime.Types (SuspensionId (..))
import YCHR.VM (RuleId (..))

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
        r <- runHistoryEnv $ notInHistory (RuleId 1) [SuspensionId 0]
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
          addHistory (RuleId 1) [SuspensionId 0, SuspensionId 1]
          notInHistory (RuleId 1) [SuspensionId 0, SuspensionId 1]
        r @?= False,
      testCase "duplicate addHistory is idempotent" $ do
        r <- runHistoryEnv $ do
          addHistory (RuleId 1) [SuspensionId 0]
          addHistory (RuleId 1) [SuspensionId 0]
          notInHistory (RuleId 1) [SuspensionId 0]
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
          addHistory (RuleId 1) [SuspensionId 0]
          notInHistory (RuleId 2) [SuspensionId 0]
        r @?= True,
      testCase "different IDs -> True" $ do
        r <- runHistoryEnv $ do
          addHistory (RuleId 1) [SuspensionId 0]
          notInHistory (RuleId 1) [SuspensionId 1]
        r @?= True,
      testCase "different ID order -> True" $ do
        r <- runHistoryEnv $ do
          addHistory (RuleId 1) [SuspensionId 0, SuspensionId 1]
          notInHistory (RuleId 1) [SuspensionId 1, SuspensionId 0]
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
          addHistory (RuleId 1) [SuspensionId 0]
          addHistory (RuleId 2) [SuspensionId 1]
          r1 <- notInHistory (RuleId 1) [SuspensionId 0]
          r2 <- notInHistory (RuleId 2) [SuspensionId 1]
          r3 <- notInHistory (RuleId 1) [SuspensionId 1]
          liftIO $ r1 @?= False
          liftIO $ r2 @?= False
          liftIO $ r3 @?= True,
      testCase "empty ID list works" $ do
        runHistoryEnv $ do
          r1 <- notInHistory (RuleId 1) []
          liftIO $ r1 @?= True
          addHistory (RuleId 1) []
          r2 <- notInHistory (RuleId 1) []
          liftIO $ r2 @?= False
    ]
