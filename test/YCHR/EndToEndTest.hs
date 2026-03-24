{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module YCHR.EndToEndTest (tests) where

import Data.Foldable (toList)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Effectful
import Effectful.Writer.Static.Local (Writer, runWriter)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import YCHR.EndToEnd (compileModules)
import YCHR.Runtime.History (PropHistory, runPropHistory)
import YCHR.Runtime.Interpreter (HostCallRegistry, callProc)
import YCHR.Runtime.Reactivation (ReactQueue, runReactQueue)
import YCHR.Runtime.Store (CHRStore, getStoreSnapshot, isSuspAlive, runCHRStore)
import YCHR.Runtime.Types (RuntimeVal (..), SuspensionId (..), Value (..))
import YCHR.Runtime.Var (Unify, equal, newVar, runUnify)
import YCHR.VM qualified as VM

tests :: TestTree
tests =
  testGroup
    "YCHR.EndToEnd"
    [ leqTests,
      fibTests
    ]

-- ---------------------------------------------------------------------------
-- Shared helpers
-- ---------------------------------------------------------------------------

compileOrFail :: [(FilePath, Text)] -> IO VM.Program
compileOrFail inputs = case compileModules inputs of
  Left err -> assertFailure $ show err
  Right prog -> pure prog

isPrefixOfName :: String -> VM.Name -> Bool
isPrefixOfName prefix (VM.Name n) = take (length prefix) n == prefix

findTellOrFail :: VM.Program -> IO VM.Name
findTellOrFail prog =
  case [VM.procName p | p <- VM.progProcedures prog, "tell_" `isPrefixOfName` VM.procName p] of
    (n : _) -> pure n
    [] -> assertFailure "No tell procedure found"

buildProcMap :: VM.Program -> Map.Map VM.Name VM.Procedure
buildProcMap prog = Map.fromList [(VM.procName p, p) | p <- VM.progProcedures prog]

runStack ::
  VM.Program ->
  Eff
    [ Writer [SuspensionId],
      ReactQueue,
      PropHistory,
      CHRStore,
      Unify,
      IOE
    ]
    a ->
  IO a
runStack prog m =
  runEff
    . runUnify
    . runCHRStore (VM.progNumTypes prog)
    . runPropHistory
    . runReactQueue
    . fmap fst
    . runWriter @[SuspensionId]
    $ m

countAlive :: (CHRStore :> es) => VM.ConstraintType -> Eff es Int
countAlive cType = do
  snapshot <- getStoreSnapshot cType
  alives <- traverse isSuspAlive (toList snapshot)
  pure (length (filter id alives))

-- ---------------------------------------------------------------------------
-- LEQ surface source
-- ---------------------------------------------------------------------------

leqSource :: Text
leqSource =
  ":- module(order, []).\n\
  \:- chr_constraint leq/2.\n\
  \\n\
  \reflexivity @ leq(X, X) <=> true.\n\
  \antisymmetry @ leq(X, Y), leq(Y, X) <=> X = Y.\n\
  \idempotence @ leq(X, Y) \\ leq(X, Y) <=> true.\n\
  \transitivity @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).\n"

leqType :: VM.ConstraintType
leqType = VM.ConstraintType 0

leqHostCalls :: HostCallRegistry
leqHostCalls = Map.empty

leqTests :: TestTree
leqTests =
  testGroup
    "LEQ handler (from surface language)"
    [ testCase "reflexivity: leq(3, 3) fires, store empty" $ do
        prog <- compileOrFail [("order.chr", leqSource)]
        tellName <- findTellOrFail prog
        let procMap = buildProcMap prog
        n <- runStack prog $ do
          _ <- callProc procMap leqHostCalls tellName [RVal (VInt 3), RVal (VInt 3)]
          countAlive leqType
        n @?= 0,
      testCase "no rule fires: leq(1, 2) stays" $ do
        prog <- compileOrFail [("order.chr", leqSource)]
        tellName <- findTellOrFail prog
        let procMap = buildProcMap prog
        n <- runStack prog $ do
          _ <- callProc procMap leqHostCalls tellName [RVal (VInt 1), RVal (VInt 2)]
          countAlive leqType
        n @?= 1,
      testCase "antisymmetry: leq(X, Y), leq(Y, X) unifies X=Y, store empty" $ do
        prog <- compileOrFail [("order.chr", leqSource)]
        tellName <- findTellOrFail prog
        let procMap = buildProcMap prog
        (n, areEqual) <- runStack prog $ do
          x <- newVar
          y <- newVar
          _ <- callProc procMap leqHostCalls tellName [RVal x, RVal y]
          _ <- callProc procMap leqHostCalls tellName [RVal y, RVal x]
          n <- countAlive leqType
          eq <- equal x y
          pure (n, eq)
        n @?= 0
        assertBool "X and Y should be unified" areEqual,
      testCase "transitivity: leq(1,2), leq(2,3) produces leq(1,3)" $ do
        prog <- compileOrFail [("order.chr", leqSource)]
        tellName <- findTellOrFail prog
        let procMap = buildProcMap prog
        n <- runStack prog $ do
          _ <- callProc procMap leqHostCalls tellName [RVal (VInt 1), RVal (VInt 2)]
          _ <- callProc procMap leqHostCalls tellName [RVal (VInt 2), RVal (VInt 3)]
          countAlive leqType
        n @?= 3,
      testCase "idempotence: leq(1,2), leq(1,2) removes duplicate" $ do
        prog <- compileOrFail [("order.chr", leqSource)]
        tellName <- findTellOrFail prog
        let procMap = buildProcMap prog
        n <- runStack prog $ do
          _ <- callProc procMap leqHostCalls tellName [RVal (VInt 1), RVal (VInt 2)]
          _ <- callProc procMap leqHostCalls tellName [RVal (VInt 1), RVal (VInt 2)]
          countAlive leqType
        n @?= 1,
      testCase "full cycle: leq(a,b), leq(b,c), leq(c,a) — all removed, all unified" $ do
        prog <- compileOrFail [("order.chr", leqSource)]
        tellName <- findTellOrFail prog
        let procMap = buildProcMap prog
        (n, eqAB, eqBC) <- runStack prog $ do
          a <- newVar
          b <- newVar
          c <- newVar
          _ <- callProc procMap leqHostCalls tellName [RVal a, RVal b]
          _ <- callProc procMap leqHostCalls tellName [RVal b, RVal c]
          _ <- callProc procMap leqHostCalls tellName [RVal c, RVal a]
          n <- countAlive leqType
          eqAB <- equal a b
          eqBC <- equal b c
          pure (n, eqAB, eqBC)
        n @?= 0
        assertBool "a and b should be unified" eqAB
        assertBool "b and c should be unified" eqBC
    ]

-- ---------------------------------------------------------------------------
-- Fibonacci surface source
-- ---------------------------------------------------------------------------

fibSource :: Text
fibSource =
  ":- module(fib, []).\n\
  \:- chr_constraint fib/2.\n\
  \\n\
  \base0 @ fib(0, R) <=> R = 0.\n\
  \base1 @ fib(1, R) <=> R = 1.\n\
  \rec @ fib(N, R) <=> N1 is N - 1, N2 is N - 2, fib(N1, R1), fib(N2, R2), Tmp is R1 + R2, R = Tmp.\n"

extractIntArgs :: String -> [RuntimeVal] -> (Int, Int)
extractIntArgs _ [RVal (VInt a), RVal (VInt b)] = (a, b)
extractIntArgs context vals = error $ context ++ ": expected 2 Int arguments, got " ++ show (length vals)

fibHostCalls :: HostCallRegistry
fibHostCalls =
  Map.fromList
    [ (VM.Name "+", \args -> let (a, b) = extractIntArgs "+" args in RVal (VInt (a + b))),
      (VM.Name "-", \args -> let (a, b) = extractIntArgs "-" args in RVal (VInt (a - b)))
    ]

fibTests :: TestTree
fibTests =
  testGroup
    "Fibonacci (from surface language)"
    [ testCase "fib 10 = 55" $ do
        prog <- compileOrFail [("fib.chr", fibSource)]
        tellName <- findTellOrFail prog
        let procMap = buildProcMap prog
        result <- runStack prog $ do
          r <- newVar
          _ <- callProc procMap fibHostCalls tellName [RVal (VInt 10), RVal r]
          equal r (VInt 55)
        assertBool "fib 10 should equal 55" result
    ]
