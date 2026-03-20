{-# LANGUAGE DataKinds #-}

module YCHR.Runtime.StoreTest (tests) where

import Data.Foldable (toList)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=), assertBool, assertFailure)

import Effectful
import Effectful.Writer.Static.Local (Writer, runWriter)

import YCHR.Runtime.Types (SuspensionId (..), Value (..))
import YCHR.Runtime.Var (Unify, runUnify, newVar, unify, equal)
import YCHR.Runtime.Store


tests :: TestTree
tests = testGroup "YCHR.Runtime.Store"
  [ createTests
  , storeTests
  , killTests
  , fieldTests
  , iterationTests
  , observerTests
  ]


-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

-- | Run an Eff computation with CHRStore, Unify, Writer, and IOE.
runStoreEnv :: Eff [Writer [SuspensionId], CHRStore, Unify, IOE] a -> IO (a, [SuspensionId])
runStoreEnv = runEff . runUnify . runCHRStore . runWriter @[SuspensionId]

runStoreEnv_ :: Eff [Writer [SuspensionId], CHRStore, Unify, IOE] a -> IO a
runStoreEnv_ m = fst <$> runStoreEnv m

-- | Count alive suspensions in a snapshot.
countAlive :: CHRStore :> es => [Suspension] -> Eff es Int
countAlive [] = pure 0
countAlive (s:ss) = do
  a <- isSuspAlive s
  rest <- countAlive ss
  pure $ (if a then 1 else 0) + rest


-- ---------------------------------------------------------------------------
-- createConstraint tests
-- ---------------------------------------------------------------------------

createTests :: TestTree
createTests = testGroup "createConstraint"
  [ testCase "returns distinct IDs" $ do
      runStoreEnv_ $ do
        id1 <- createConstraint "leq" [VInt 1, VInt 2]
        id2 <- createConstraint "leq" [VInt 3, VInt 4]
        liftIO $ assertBool "IDs should differ" (not (idEqual id1 id2))

  , testCase "constraint is alive before storing" $ do
      runStoreEnv_ $ do
        sid <- createConstraint "leq" [VInt 1, VInt 2]
        alive <- aliveConstraint sid
        liftIO $ alive @?= True
  ]


-- ---------------------------------------------------------------------------
-- storeConstraint tests
-- ---------------------------------------------------------------------------

storeTests :: TestTree
storeTests = testGroup "storeConstraint"
  [ testCase "appears in snapshot" $ do
      runStoreEnv_ $ do
        sid <- createConstraint "leq" [VInt 1, VInt 2]
        storeConstraint sid
        snap <- getStoreSnapshot "leq"
        liftIO $ length snap @?= 1

  , testCase "multiple same type" $ do
      runStoreEnv_ $ do
        s1 <- createConstraint "leq" [VInt 1, VInt 2]
        s2 <- createConstraint "leq" [VInt 3, VInt 4]
        storeConstraint s1
        storeConstraint s2
        snap <- getStoreSnapshot "leq"
        liftIO $ length snap @?= 2

  , testCase "different types" $ do
      runStoreEnv_ $ do
        s1 <- createConstraint "leq" [VInt 1, VInt 2]
        s2 <- createConstraint "gcd" [VInt 5]
        storeConstraint s1
        storeConstraint s2
        snapLeq <- getStoreSnapshot "leq"
        snapGcd <- getStoreSnapshot "gcd"
        liftIO $ length snapLeq @?= 1
        liftIO $ length snapGcd @?= 1

  , testCase "empty snapshot for unknown type" $ do
      runStoreEnv_ $ do
        snap <- getStoreSnapshot "nonexistent"
        liftIO $ length snap @?= 0
  ]


-- ---------------------------------------------------------------------------
-- killConstraint tests
-- ---------------------------------------------------------------------------

killTests :: TestTree
killTests = testGroup "killConstraint"
  [ testCase "alive becomes False" $ do
      runStoreEnv_ $ do
        sid <- createConstraint "leq" [VInt 1, VInt 2]
        storeConstraint sid
        killConstraint sid
        alive <- aliveConstraint sid
        liftIO $ alive @?= False

  , testCase "still in snapshot after kill" $ do
      runStoreEnv_ $ do
        sid <- createConstraint "leq" [VInt 1, VInt 2]
        storeConstraint sid
        killConstraint sid
        snap <- getStoreSnapshot "leq"
        liftIO $ length snap @?= 1

  , testCase "doesn't affect other constraints" $ do
      runStoreEnv_ $ do
        s1 <- createConstraint "leq" [VInt 1, VInt 2]
        s2 <- createConstraint "leq" [VInt 3, VInt 4]
        storeConstraint s1
        storeConstraint s2
        killConstraint s1
        a1 <- aliveConstraint s1
        a2 <- aliveConstraint s2
        liftIO $ a1 @?= False
        liftIO $ a2 @?= True
  ]


-- ---------------------------------------------------------------------------
-- Field access tests
-- ---------------------------------------------------------------------------

fieldTests :: TestTree
fieldTests = testGroup "fields"
  [ testCase "getConstraintArg" $ do
      runStoreEnv_ $ do
        sid <- createConstraint "leq" [VInt 10, VAtom "x"]
        a0 <- getConstraintArg sid 0
        a1 <- getConstraintArg sid 1
        liftIO $ case a0 of { VInt 10 -> pure (); _ -> assertBool "arg 0" False }
        liftIO $ case a1 of { VAtom "x" -> pure (); _ -> assertBool "arg 1" False }

  , testCase "getConstraintType" $ do
      runStoreEnv_ $ do
        sid <- createConstraint "gcd" [VInt 5]
        t <- getConstraintType sid
        liftIO $ t @?= "gcd"

  , testCase "idEqual same" $ do
      runStoreEnv_ $ do
        sid <- createConstraint "leq" [VInt 1, VInt 2]
        liftIO $ assertBool "same id" (idEqual sid sid)

  , testCase "idEqual different" $ do
      runStoreEnv_ $ do
        s1 <- createConstraint "leq" [VInt 1, VInt 2]
        s2 <- createConstraint "leq" [VInt 3, VInt 4]
        liftIO $ assertBool "different id" (not (idEqual s1 s2))

  , testCase "isConstraintType true" $ do
      runStoreEnv_ $ do
        sid <- createConstraint "leq" [VInt 1, VInt 2]
        r <- isConstraintType sid "leq"
        liftIO $ r @?= True

  , testCase "isConstraintType false" $ do
      runStoreEnv_ $ do
        sid <- createConstraint "leq" [VInt 1, VInt 2]
        r <- isConstraintType sid "gcd"
        liftIO $ r @?= False
  ]


-- ---------------------------------------------------------------------------
-- Iteration tests
-- ---------------------------------------------------------------------------

iterationTests :: TestTree
iterationTests = testGroup "iteration"
  [ testCase "skip dead in snapshot" $ do
      runStoreEnv_ $ do
        s1 <- createConstraint "leq" [VInt 1, VInt 2]
        s2 <- createConstraint "leq" [VInt 3, VInt 4]
        storeConstraint s1
        storeConstraint s2
        killConstraint s1
        snap <- getStoreSnapshot "leq"
        alive <- countAlive (toList snap)
        liftIO $ alive @?= 1

  , testCase "new constraints invisible to captured snapshot" $ do
      runStoreEnv_ $ do
        s1 <- createConstraint "leq" [VInt 1, VInt 2]
        storeConstraint s1
        snap <- getStoreSnapshot "leq"
        -- Add another constraint after snapshot
        s2 <- createConstraint "leq" [VInt 3, VInt 4]
        storeConstraint s2
        -- Original snapshot should still have only 1
        liftIO $ length snap @?= 1
        -- Fresh snapshot should have 2
        snap2 <- getStoreSnapshot "leq"
        liftIO $ length snap2 @?= 2

  , testCase "kill visible during iteration via isSuspAlive" $ do
      runStoreEnv_ $ do
        s1 <- createConstraint "leq" [VInt 1, VInt 2]
        s2 <- createConstraint "leq" [VInt 3, VInt 4]
        storeConstraint s1
        storeConstraint s2
        snap <- getStoreSnapshot "leq"
        -- Kill s1 after snapshot
        killConstraint s1
        -- isSuspAlive sees the kill through the IORef
        (susp1, susp2) <- liftIO $ case toList snap of
          (s1' : s2' : _) -> pure (s1', s2')
          _ -> assertFailure "expected at least 2 suspensions in \"leq\" store"
        a1 <- isSuspAlive susp1
        a2 <- isSuspAlive susp2
        liftIO $ a1 @?= False
        liftIO $ a2 @?= True

  , testCase "filter by argument equality" $ do
      runStoreEnv_ $ do
        s1 <- createConstraint "leq" [VInt 1, VInt 2]
        s2 <- createConstraint "leq" [VInt 3, VInt 4]
        s3 <- createConstraint "leq" [VInt 1, VInt 5]
        storeConstraint s1
        storeConstraint s2
        storeConstraint s3
        snap <- getStoreSnapshot "leq"
        -- Filter: first arg equal to VInt 1
        let susps = toList snap
        matches <- filterByArg 0 (VInt 1) susps
        liftIO $ length matches @?= 2

  , testCase "suspArg pure access" $ do
      runStoreEnv_ $ do
        sid <- createConstraint "leq" [VInt 10, VAtom "y"]
        storeConstraint sid
        snap <- getStoreSnapshot "leq"
        s <- liftIO $ case toList snap of
          (s : _) -> pure s
          [] -> assertFailure "expected at least 1 suspension in \"leq\" store"
        liftIO $ case suspArg s 0 of { VInt 10 -> pure (); _ -> assertBool "arg 0" False }
        liftIO $ case suspArg s 1 of { VAtom "y" -> pure (); _ -> assertBool "arg 1" False }
  ]
  where
    filterByArg :: (CHRStore :> es, Unify :> es) => Int -> Value -> [Suspension] -> Eff es [Suspension]
    filterByArg _ _ [] = pure []
    filterByArg idx val (s:ss) = do
      alive <- isSuspAlive s
      if alive
        then do
          eq <- equal (suspArg s idx) val
          rest <- filterByArg idx val ss
          pure $ if eq then s : rest else rest
        else filterByArg idx val ss


-- ---------------------------------------------------------------------------
-- Observer registration tests
-- ---------------------------------------------------------------------------

observerTests :: TestTree
observerTests = testGroup "observer registration"
  [ testCase "unifying a constraint's var arg emits SuspensionId" $ do
      (_, obs) <- runStoreEnv $ do
        x <- newVar
        sid <- createConstraint "leq" [x, VInt 2]
        storeConstraint sid
        _ <- unify x (VInt 1)
        pure ()
      assertBool "should contain the suspension id" (SuspensionId 0 `elem` obs)

  , testCase "ground args produce no observer" $ do
      (_, obs) <- runStoreEnv $ do
        sid <- createConstraint "leq" [VInt 1, VInt 2]
        storeConstraint sid
        pure ()
      obs @?= []

  , testCase "multiple constraints on same variable" $ do
      (_, obs) <- runStoreEnv $ do
        x <- newVar
        s1 <- createConstraint "leq" [x, VInt 2]
        s2 <- createConstraint "gcd" [x]
        storeConstraint s1
        storeConstraint s2
        _ <- unify x (VInt 1)
        pure ()
      -- Both suspension IDs should appear
      assertBool "should contain s1" (SuspensionId 0 `elem` obs)
      assertBool "should contain s2" (SuspensionId 1 `elem` obs)
  ]
