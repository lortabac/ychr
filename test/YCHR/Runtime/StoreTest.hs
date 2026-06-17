{-# LANGUAGE OverloadedStrings #-}

module YCHR.Runtime.StoreTest (tests) where

import Control.Monad.IO.Class (liftIO)
import Data.Foldable (toList)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import YCHR.Runtime.Monad (Chr, initSessionEnv, runChr)
import YCHR.Runtime.Store
import YCHR.Runtime.Types (SuspensionId (..), Value (..))
import YCHR.Runtime.Var (equal, newVar, unify)
import YCHR.Types (ConstraintType (..), Name (..))

tests :: TestTree
tests =
  testGroup
    "YCHR.Runtime.Store"
    [ createTests,
      storeTests,
      killTests,
      fieldTests,
      iterationTests,
      observerTests
    ]

-- | A 100-slot session is large enough for every test in this module
-- (which use ConstraintType 0/1 and occasionally check ConstraintType 99).
runStoreEnv :: Chr a -> IO a
runStoreEnv action = do
  env <-
    initSessionEnv
      (replicate 100 (Unqualified ""))
      []
      Map.empty
      Map.empty
      Map.empty
      Map.empty
      Set.empty
  runChr action env

-- | Run an action and pair the result with the observer IDs accumulated
-- by the final 'unify' (or an empty list if no 'unify' happened).
runStoreObservers :: Chr [SuspensionId] -> IO [SuspensionId]
runStoreObservers = runStoreEnv

countAlive :: [Suspension] -> Chr Int
countAlive [] = pure 0
countAlive (s : ss) = do
  a <- isSuspAlive s
  rest <- countAlive ss
  pure $ (if a then 1 else 0) + rest

createTests :: TestTree
createTests =
  testGroup
    "createConstraint"
    [ testCase "returns distinct IDs" $ do
        runStoreEnv $ do
          id1 <- createConstraint (ConstraintType 0) [VInt 1, VInt 2]
          id2 <- createConstraint (ConstraintType 0) [VInt 3, VInt 4]
          liftIO $ assertBool "IDs should differ" (not (idEqual id1 id2)),
      testCase "constraint is alive before storing" $ do
        runStoreEnv $ do
          sid <- createConstraint (ConstraintType 0) [VInt 1, VInt 2]
          alive <- aliveConstraint sid
          liftIO $ alive @?= True
    ]

storeTests :: TestTree
storeTests =
  testGroup
    "storeConstraint"
    [ testCase "appears in snapshot" $ do
        runStoreEnv $ do
          sid <- createConstraint (ConstraintType 0) [VInt 1, VInt 2]
          storeConstraint sid
          snap <- getStoreSnapshot (ConstraintType 0)
          liftIO $ length snap @?= 1,
      testCase "multiple same type" $ do
        runStoreEnv $ do
          s1 <- createConstraint (ConstraintType 0) [VInt 1, VInt 2]
          s2 <- createConstraint (ConstraintType 0) [VInt 3, VInt 4]
          storeConstraint s1
          storeConstraint s2
          snap <- getStoreSnapshot (ConstraintType 0)
          liftIO $ length snap @?= 2,
      testCase "different types" $ do
        runStoreEnv $ do
          s1 <- createConstraint (ConstraintType 0) [VInt 1, VInt 2]
          s2 <- createConstraint (ConstraintType 1) [VInt 5]
          storeConstraint s1
          storeConstraint s2
          snapLeq <- getStoreSnapshot (ConstraintType 0)
          snapGcd <- getStoreSnapshot (ConstraintType 1)
          liftIO $ length snapLeq @?= 1
          liftIO $ length snapGcd @?= 1,
      testCase "empty snapshot for unknown type" $ do
        runStoreEnv $ do
          snap <- getStoreSnapshot (ConstraintType 99)
          liftIO $ length snap @?= 0
    ]

killTests :: TestTree
killTests =
  testGroup
    "killConstraint"
    [ testCase "alive becomes False" $ do
        runStoreEnv $ do
          sid <- createConstraint (ConstraintType 0) [VInt 1, VInt 2]
          storeConstraint sid
          killConstraint sid
          alive <- aliveConstraint sid
          liftIO $ alive @?= False,
      testCase "still in snapshot after kill" $ do
        runStoreEnv $ do
          sid <- createConstraint (ConstraintType 0) [VInt 1, VInt 2]
          storeConstraint sid
          killConstraint sid
          snap <- getStoreSnapshot (ConstraintType 0)
          liftIO $ length snap @?= 1,
      testCase "doesn't affect other constraints" $ do
        runStoreEnv $ do
          s1 <- createConstraint (ConstraintType 0) [VInt 1, VInt 2]
          s2 <- createConstraint (ConstraintType 0) [VInt 3, VInt 4]
          storeConstraint s1
          storeConstraint s2
          killConstraint s1
          a1 <- aliveConstraint s1
          a2 <- aliveConstraint s2
          liftIO $ a1 @?= False
          liftIO $ a2 @?= True
    ]

fieldTests :: TestTree
fieldTests =
  testGroup
    "fields"
    [ testCase "getConstraintArg" $ do
        runStoreEnv $ do
          sid <- createConstraint (ConstraintType 0) [VInt 10, VAtom "x"]
          a0 <- getConstraintArg sid 0
          a1 <- getConstraintArg sid 1
          liftIO $ case a0 of VInt 10 -> pure (); _ -> assertBool "arg 0" False
          liftIO $ case a1 of VAtom "x" -> pure (); _ -> assertBool "arg 1" False,
      testCase "getConstraintType" $ do
        runStoreEnv $ do
          sid <- createConstraint (ConstraintType 1) [VInt 5]
          t <- getConstraintType sid
          liftIO $ t @?= ConstraintType 1,
      testCase "idEqual same" $ do
        runStoreEnv $ do
          sid <- createConstraint (ConstraintType 0) [VInt 1, VInt 2]
          liftIO $ assertBool "same id" (idEqual sid sid),
      testCase "idEqual different" $ do
        runStoreEnv $ do
          s1 <- createConstraint (ConstraintType 0) [VInt 1, VInt 2]
          s2 <- createConstraint (ConstraintType 0) [VInt 3, VInt 4]
          liftIO $ assertBool "different id" (not (idEqual s1 s2)),
      testCase "isConstraintType true" $ do
        runStoreEnv $ do
          sid <- createConstraint (ConstraintType 0) [VInt 1, VInt 2]
          r <- isConstraintType sid (ConstraintType 0)
          liftIO $ r @?= True,
      testCase "isConstraintType false" $ do
        runStoreEnv $ do
          sid <- createConstraint (ConstraintType 0) [VInt 1, VInt 2]
          r <- isConstraintType sid (ConstraintType 1)
          liftIO $ r @?= False
    ]

iterationTests :: TestTree
iterationTests =
  testGroup
    "iteration"
    [ testCase "skip dead in snapshot" $ do
        runStoreEnv $ do
          s1 <- createConstraint (ConstraintType 0) [VInt 1, VInt 2]
          s2 <- createConstraint (ConstraintType 0) [VInt 3, VInt 4]
          storeConstraint s1
          storeConstraint s2
          killConstraint s1
          snap <- getStoreSnapshot (ConstraintType 0)
          alive <- countAlive (toList snap)
          liftIO $ alive @?= 1,
      testCase "new constraints invisible to captured snapshot" $ do
        runStoreEnv $ do
          s1 <- createConstraint (ConstraintType 0) [VInt 1, VInt 2]
          storeConstraint s1
          snap <- getStoreSnapshot (ConstraintType 0)
          s2 <- createConstraint (ConstraintType 0) [VInt 3, VInt 4]
          storeConstraint s2
          liftIO $ length snap @?= 1
          snap2 <- getStoreSnapshot (ConstraintType 0)
          liftIO $ length snap2 @?= 2,
      testCase "kill visible during iteration via isSuspAlive" $ do
        runStoreEnv $ do
          s1 <- createConstraint (ConstraintType 0) [VInt 1, VInt 2]
          s2 <- createConstraint (ConstraintType 0) [VInt 3, VInt 4]
          storeConstraint s1
          storeConstraint s2
          snap <- getStoreSnapshot (ConstraintType 0)
          killConstraint s1
          (susp1, susp2) <- liftIO $ case toList snap of
            (s1' : s2' : _) -> pure (s1', s2')
            _ -> assertFailure "expected at least 2 suspensions in store"
          a1 <- isSuspAlive susp1
          a2 <- isSuspAlive susp2
          liftIO $ a1 @?= False
          liftIO $ a2 @?= True,
      testCase "filter by argument equality" $ do
        runStoreEnv $ do
          s1 <- createConstraint (ConstraintType 0) [VInt 1, VInt 2]
          s2 <- createConstraint (ConstraintType 0) [VInt 3, VInt 4]
          s3 <- createConstraint (ConstraintType 0) [VInt 1, VInt 5]
          storeConstraint s1
          storeConstraint s2
          storeConstraint s3
          snap <- getStoreSnapshot (ConstraintType 0)
          let susps = toList snap
          matches <- filterByArg 0 (VInt 1) susps
          liftIO $ length matches @?= 2,
      testCase "suspArg pure access" $ do
        runStoreEnv $ do
          sid <- createConstraint (ConstraintType 0) [VInt 10, VAtom "y"]
          storeConstraint sid
          snap <- getStoreSnapshot (ConstraintType 0)
          s <- liftIO $ case toList snap of
            (s : _) -> pure s
            [] -> assertFailure "expected at least 1 suspension in store"
          liftIO $ case suspArg s 0 of VInt 10 -> pure (); _ -> assertBool "arg 0" False
          liftIO $ case suspArg s 1 of VAtom "y" -> pure (); _ -> assertBool "arg 1" False
    ]
  where
    filterByArg :: Int -> Value -> [Suspension] -> Chr [Suspension]
    filterByArg _ _ [] = pure []
    filterByArg idx val (s : ss) = do
      alive <- isSuspAlive s
      if alive
        then do
          eq <- equal (suspArg s idx) val
          rest <- filterByArg idx val ss
          pure $ if eq then s : rest else rest
        else filterByArg idx val ss

observerTests :: TestTree
observerTests =
  testGroup
    "observer registration"
    [ testCase "unifying a constraint's var arg emits SuspensionId" $ do
        obs <- runStoreObservers $ do
          x <- newVar
          sid <- createConstraint (ConstraintType 0) [x, VInt 2]
          storeConstraint sid
          (_, o) <- unify x (VInt 1)
          pure o
        assertBool
          "should contain the suspension id"
          (SuspensionId 0 `elem` obs),
      testCase "ground args produce no observer" $ do
        runStoreEnv $ do
          sid <- createConstraint (ConstraintType 0) [VInt 1, VInt 2]
          storeConstraint sid
          pure (),
      testCase "multiple constraints on same variable" $ do
        obs <- runStoreObservers $ do
          x <- newVar
          s1 <- createConstraint (ConstraintType 0) [x, VInt 2]
          s2 <- createConstraint (ConstraintType 1) [x]
          storeConstraint s1
          storeConstraint s2
          (_, o) <- unify x (VInt 1)
          pure o
        assertBool "should contain s1" (SuspensionId 0 `elem` obs)
        assertBool "should contain s2" (SuspensionId 1 `elem` obs),
      testCase "var nested in a compound arg emits SuspensionId" $ do
        obs <- runStoreObservers $ do
          x <- newVar
          -- The var is nested two levels deep inside compound
          -- arguments, not a bare top-level argument. Reactivation
          -- must still observe it (ωr Reactivate).
          sid <-
            createConstraint
              (ConstraintType 0)
              [VTerm "pair" [VTerm "box" [x], VInt 2]]
          storeConstraint sid
          (_, o) <- unify x (VInt 1)
          pure o
        assertBool
          "should contain the suspension id"
          (SuspensionId 0 `elem` obs)
    ]
