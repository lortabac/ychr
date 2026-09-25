{-# LANGUAGE OverloadedStrings #-}

-- | Tests for the store's per-argument indexes (the paper's /Indexing/
-- optimization). See "YCHR.Internal.Runtime.Index".
--
-- The property under test throughout is the one the optimization rests
-- on: the index may narrow the iterator, but never below the matching
-- suspensions, and never out of store order.
module YCHR.Runtime.IndexTest (tests) where

import Control.Monad (filterM)
import Control.Monad.IO.Class (liftIO)
import Data.Foldable (toList)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.List (isSubsequenceOf)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))
import YCHR.Internal.Runtime.Index
import YCHR.Internal.Runtime.Monad (Chr, initSessionEnv, runChr)
import YCHR.Internal.Runtime.Store
  ( Suspension (..),
    candidateSuspensions,
    createConstraint,
    getStoreSnapshot,
    killConstraint,
    storeConstraint,
    suspArg,
  )
import YCHR.Internal.Runtime.Types (SuspensionId, Value (..))
import YCHR.Internal.Runtime.Var
  ( addObserver,
    addObserverAndKey,
    equal,
    groundKey,
    newVar,
    unify,
  )
import YCHR.Internal.Types (ConstraintType (..), Name (..))
import YCHR.Internal.VM
  ( ArgIndex (..),
    BoolExpr (..),
    Literal (..),
    ProcKind (..),
    Procedure (..),
    Program (..),
    Stmt (..),
    ValExpr (..),
  )

tests :: TestTree
tests =
  testGroup
    "YCHR.Internal.Runtime.Index"
    [ keyTests,
      programTests,
      stateTests,
      candidateTests,
      observerTests
    ]

-- ---------------------------------------------------------------------------
-- Session
-- ---------------------------------------------------------------------------

-- | A session that indexes argument 0 of 'ConstraintType' 0, the
-- arrangement every candidate test below assumes.
runIndexEnv :: Chr a -> IO a
runIndexEnv action = do
  env <-
    initSessionEnv
      (replicate 2 (Unqualified ""))
      []
      []
      (IntMap.fromList [(0, IntSet.singleton 0)])
      Map.empty
      Map.empty
      Map.empty
      Map.empty
      Map.empty
      Set.empty
  runChr action env

-- | A program whose single procedure has the given body.
programWith :: [Stmt] -> Program
programWith stmts =
  Program
    { numTypes = 1,
      typeNames = [],
      numRules = 0,
      ruleNames = [],
      procedures =
        [ Procedure
            { name = "p",
              params = [],
              body = stmts,
              procKind = PKTell (ConstraintType 0)
            }
        ],
      evaluables = [],
      callables = [],
      inertTypes = []
    }

-- | A 'Foreach' with one condition on argument @pos@.
foreach :: ConstraintType -> Int -> [Stmt] -> Stmt
foreach cType pos body =
  Foreach "L" cType "susp" [(ArgIndex pos, Lit (IntLit 0))] body

-- ---------------------------------------------------------------------------
-- Keys
-- ---------------------------------------------------------------------------

keyTests :: TestTree
keyTests =
  testGroup
    "groundKey"
    [ testCase "scalars and nested compounds" $
        runIndexEnv $ do
          k1 <- groundKey (VTerm "f" [VInt 1, VAtom "a", VBool True, VText "t"])
          liftIO $
            k1
              @?= Just (KTerm "f" [KInt 1, KAtom "a", KBool True, KText "t"])
          k2 <- groundKey (VInt (-3))
          liftIO $ k2 @?= Just (KInt (-3)),
      testCase "a nested unbound variable makes the whole value unkeyable" $
        runIndexEnv $ do
          x <- newVar
          bare <- groundKey x
          nested <- groundKey (VTerm "f" [VInt 1, VTerm "g" [x]])
          liftIO $ do
            bare @?= Nothing
            nested @?= Nothing,
      testCase "dereferences before keying" $
        runIndexEnv $ do
          x <- newVar
          _ <- unify x (VInt 7)
          k <- groundKey (VTerm "f" [x])
          liftIO $ k @?= Just (KTerm "f" [KInt 7]),
      testCase "negative zero and zero share a key" $
        runIndexEnv $ do
          neg <- groundKey (VFloat (-0.0))
          pos <- groundKey (VFloat 0.0)
          liftIO $ do
            neg @?= Just (KFloat 0)
            neg @?= pos,
      testCase "every NaN shares a key, and no NaN equals itself under equal" $
        runIndexEnv $ do
          a <- groundKey (VFloat (0 / 0))
          b <- groundKey (VFloat (0 / 0))
          liftIO $ do
            a @?= Just KNaN
            a @?= b,
      -- @equal@ never equates an integer with a float, so the keys must
      -- not either: a shared key would only cost a rejected candidate,
      -- but a key /finer/ than ask-equality would lose one.
      testCase "an integer key is not a float key" $
        runIndexEnv $ do
          i <- groundKey (VInt 1)
          f <- groundKey (VFloat 1.0)
          liftIO $ assertBool "keys must differ" (i /= f)
    ]

-- ---------------------------------------------------------------------------
-- Derivation from the program
-- ---------------------------------------------------------------------------

programTests :: TestTree
programTests =
  testGroup
    "indexablePositions"
    [ testCase "a program with no Foreach has no positions" $
        indexablePositions (programWith []) @?= IntMap.empty,
      testCase "collects the condition positions of a top-level loop" $
        indexablePositions (programWith [foreach (ConstraintType 0) 1 []])
          @?= IntMap.fromList [(0, IntSet.singleton 1)],
      testCase "recurses into branches, drains and nested loops, deduplicating" $
        let body =
              [ If
                  (BLit True)
                  [foreach (ConstraintType 1) 0 []]
                  [ DrainReactivationQueue
                      "pend"
                      [foreach (ConstraintType 0) 2 [foreach (ConstraintType 0) 2 []]]
                  ]
              ]
         in indexablePositions (programWith body)
              @?= IntMap.fromList [(0, IntSet.singleton 2), (1, IntSet.singleton 0)]
    ]

-- ---------------------------------------------------------------------------
-- Index state
-- ---------------------------------------------------------------------------

stateTests :: TestTree
stateTests =
  testGroup
    "insertConstraints/candidateSlots"
    [ testCase "a ground key lands in its bucket" $
        let si =
              insertConstraints (ConstraintType 0) [(3, [(0, Just (KInt 1))])] emptyStoreIndex
         in candidateSlots (ConstraintType 0) 0 (KInt 1) si @?= IntSet.singleton 3,
      testCase "an unkeyable value lands in the fallback set of every key" $
        let si =
              insertConstraints (ConstraintType 0) [(4, [(0, Nothing)])] emptyStoreIndex
         in do
              candidateSlots (ConstraintType 0) 0 (KInt 1) si @?= IntSet.singleton 4
              candidateSlots (ConstraintType 0) 0 (KInt 99) si @?= IntSet.singleton 4,
      testCase "an unindexed position has no entries" $
        let si =
              insertConstraints (ConstraintType 0) [(5, [(0, Just (KInt 1))])] emptyStoreIndex
         in candidateSlots (ConstraintType 0) 1 (KInt 1) si @?= IntSet.empty,
      testCase "entries accumulate per type and position" $
        let type1 = insertConstraints (ConstraintType 1) [(2, [(0, Just (KInt 1))])]
            si =
              insertConstraints
                (ConstraintType 0)
                [(0, [(0, Just (KInt 1)), (1, Nothing)]), (1, [(0, Just (KInt 1))])]
                $ type1 emptyStoreIndex
         in do
              candidateSlots (ConstraintType 0) 0 (KInt 1) si @?= IntSet.fromList [0, 1]
              candidateSlots (ConstraintType 0) 1 (KInt 1) si @?= IntSet.singleton 0
              candidateSlots (ConstraintType 1) 0 (KInt 1) si @?= IntSet.singleton 2
              candidateSlots (ConstraintType 0) 0 (KInt 2) si @?= IntSet.empty,
      testCase "a type is indexed exactly once a store is filed for it" $
        let empty = emptyStoreIndex
            one = insertConstraints (ConstraintType 0) [(0, [(0, Just (KInt 1))])] empty
         in do
              typeIndexed (ConstraintType 0) empty @?= False
              typeIndexed (ConstraintType 1) empty @?= False
              typeIndexed (ConstraintType 0) one @?= True
              typeIndexed (ConstraintType 1) one @?= False
    ]

-- ---------------------------------------------------------------------------
-- Candidates against a real store
-- ---------------------------------------------------------------------------

-- | The suspensions a full scan would offer for the condition
-- @arg(0) == value@, in store order.
scanMatching :: ConstraintType -> Value -> Chr [SuspensionId]
scanMatching cType v = do
  snap <- getStoreSnapshot cType
  matching <- filterM (\s -> equal (suspArg s 0) v) (toList snap)
  pure (map (.suspId) matching)

-- | The suspensions the index offers for a ground key on argument 0.
indexedMatching :: ConstraintType -> GroundKey -> Chr [SuspensionId]
indexedMatching cType key = map (.suspId) <$> candidateSuspensions cType 0 key

candidateTests :: TestTree
candidateTests =
  testGroup
    "candidateSuspensions"
    [ testCase "an all-ground store yields exactly the matching bucket" $
        runIndexEnv $ do
          [s1, s2, s3] <- storePastThreshold [VInt 1, VInt 2, VInt 1]
          actual <- indexedMatching (ConstraintType 0) (KInt 1)
          expected <- scanMatching (ConstraintType 0) (VInt 1)
          liftIO $ do
            actual @?= [s1, s3]
            actual @?= expected
            assertBool "the non-matching suspension is out" (s2 `notElem` actual),
      testCase "an unkeyable argument is always a candidate, in store order" $
        runIndexEnv $ do
          x <- newVar
          [s1, s2, s3, s4] <- storePastThreshold [VInt 1, x, VTerm "f" [x], VInt 1]
          actual <- indexedMatching (ConstraintType 0) (KInt 1)
          expected <- scanMatching (ConstraintType 0) (VInt 1)
          liftIO $ do
            actual @?= [s1, s2, s3, s4]
            assertBool
              "a full scan's answer is still in the narrower set"
              (expected `isSubsequenceOf` actual),
      -- The fallback set is what makes a lookup for a key that is not
      -- ground at store time still findable once it is: the suspension
      -- moved nowhere, and a scan of the fallback still checks it.
      testCase "a suspension stored unbound is found once its argument is bound" $
        runIndexEnv $ do
          x <- newVar
          [s1, _, _, _] <- storePastThreshold [x, VInt 2, VInt 3, VInt 4]
          before <- indexedMatching (ConstraintType 0) (KInt 7)
          _ <- unify x (VInt 7)
          after <- indexedMatching (ConstraintType 0) (KInt 7)
          expected <- scanMatching (ConstraintType 0) (VInt 7)
          liftIO $ do
            before @?= [s1]
            after @?= [s1]
            after @?= expected,
      -- Nothing removes an index entry on a kill — the iterator's
      -- liveness check does that — so a dead suspension is still
      -- offered, exactly as a full scan still offers it.
      testCase "a killed suspension stays in the index until the iterator filters it" $
        runIndexEnv $ do
          [s1, s2, _, _] <- storePastThreshold [VInt 1, VInt 1, VInt 2, VInt 3]
          _ <- killConstraint s2
          actual <- indexedMatching (ConstraintType 0) (KInt 1)
          liftIO $ actual @?= [s1, s2],
      -- Indexing is on demand: below the threshold the store files
      -- nothing and a lookup is the plain scan, which is what keeps a
      -- small bucket from paying for an index it cannot profit from.
      testCase "a bucket below the threshold is not indexed and scans" $
        runIndexEnv $ do
          s1 <- store1 (VInt 1)
          s2 <- store1 (VInt 2)
          actual <- indexedMatching (ConstraintType 0) (KInt 1)
          -- Unindexed, so the lookup is the whole bucket.
          liftIO $ actual @?= [s1, s2],
      -- The store that crosses the threshold files the whole bucket,
      -- not just itself: a suspension stored while the type was still
      -- unindexed must still be findable through the index.
      testCase "crossing the threshold files the bucket that predates it" $
        runIndexEnv $ do
          s1 <- store1 (VInt 1)
          _ <- mapM (store1 . VInt) [2 .. fromIntegral (indexThreshold - 1)]
          below <- indexedMatching (ConstraintType 0) (KInt 1)
          crossingStore <- store1 (VInt 2)
          crossing <- indexedMatching (ConstraintType 0) (KInt 1)
          liftIO $ do
            -- Below the threshold the lookup is the whole bucket.
            length below @?= indexThreshold - 1
            assertBool "the unindexed lookup still offers the match" (s1 `elem` below)
            -- And the store that crosses it makes the index answer the
            -- same lookup with only the match.
            crossing @?= [s1]
            assertBool "the new store is not a match" (crossingStore `notElem` crossing)
    ]

-- | Create and store a one-argument constraint of the indexed type.
store1 :: Value -> Chr SuspensionId
store1 v = do
  sid <- createConstraint (ConstraintType 0) [v]
  _ <- storeConstraint sid
  pure sid

-- | Store the given argument values, then pad the type's bucket with
-- distinct non-matching ones until it is past 'indexThreshold' — so the
-- store maintains an index for it and the tests below exercise the
-- indexed path rather than the below-threshold scan.
storePastThreshold :: [Value] -> Chr [SuspensionId]
storePastThreshold values = do
  ids <- mapM store1 values
  let padding = indexThreshold - length values
  _ <- mapM (store1 . VInt) [1000 .. 1000 + fromIntegral padding - 1]
  pure ids

-- ---------------------------------------------------------------------------
-- The fused observer/key walk
-- ---------------------------------------------------------------------------

-- | 'addObserverAndKey' must register exactly what 'addObserver' does,
-- and the key must come out of the same traversal. The observers a
-- binding collects are observable through 'unify''s second result: the
-- two walks run in separate sessions that allocate their ids in the same
-- order, so the collected ids are directly comparable.
observerTests :: TestTree
observerTests =
  testGroup
    "addObserverAndKey"
    [ testCase "registers exactly the observers addObserver registers" $ do
        (fusedX1, fusedX2, mkey) <- runIndexEnv $ do
          sid <- createConstraint (ConstraintType 0) []
          x1 <- newVar
          x2 <- newVar
          k <- addObserverAndKey sid (VTerm "f" [x1, VTerm "g" [x2, VInt 1], x1])
          (_, o1) <- unify x1 (VInt 7)
          (_, o2) <- unify x2 (VInt 7)
          pure (o1, o2, k)
        (plainX1, plainX2) <- runIndexEnv $ do
          sid <- createConstraint (ConstraintType 0) []
          x1 <- newVar
          x2 <- newVar
          addObserver sid (VTerm "f" [x1, VTerm "g" [x2, VInt 1], x1])
          (_, o1) <- unify x1 (VInt 7)
          (_, o2) <- unify x2 (VInt 7)
          pure (o1, o2)
        liftIO $ do
          -- A variable reached twice in the term is registered twice by
          -- both walks.
          fusedX1 @?= plainX1
          fusedX2 @?= plainX2
          assertBool "the repeated variable is registered twice" (length fusedX1 == 2)
          mkey @?= Nothing,
      testCase "returns the key of a ground argument" $
        runIndexEnv $ do
          sid <- createConstraint (ConstraintType 0) []
          k <- addObserverAndKey sid (VTerm "f" [VInt 1, VAtom "a"])
          liftIO $ k @?= Just (KTerm "f" [KInt 1, KAtom "a"]),
      -- The store takes this path for an inert type whose position is
      -- nevertheless indexed — which the current compiler cannot
      -- produce, but which must not silently start observing.
      testCase "groundKey registers nothing" $
        runIndexEnv $ do
          x <- newVar
          k <- groundKey (VTerm "f" [x])
          (_, obs) <- unify x (VInt 1)
          liftIO $ do
            k @?= Nothing
            obs @?= []
    ]
