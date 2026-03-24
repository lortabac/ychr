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
import YCHR.EndToEnd (CompiledProgram (..), compileModules, resolveQueryConstraint, runQuery)
import YCHR.Runtime.History (PropHistory, runPropHistory)
import YCHR.Runtime.Interpreter (HostCallRegistry, callProc)
import YCHR.Runtime.Reactivation (ReactQueue, runReactQueue)
import YCHR.Runtime.Store (CHRStore, getStoreSnapshot, isSuspAlive, runCHRStore)
import YCHR.Runtime.Types (RuntimeVal (..), SuspensionId (..), Value (..))
import YCHR.Runtime.Var (Unify, equal, newVar, runUnify)
import YCHR.Types (Constraint (..), Name (..), Term (..))
import YCHR.VM qualified as VM

tests :: TestTree
tests =
  testGroup
    "YCHR.EndToEnd"
    [ leqTests,
      fibTests,
      visibilityTests
    ]

-- ---------------------------------------------------------------------------
-- Shared helpers
-- ---------------------------------------------------------------------------

compileOrFail :: [(FilePath, Text)] -> IO CompiledProgram
compileOrFail inputs = case compileModules inputs of
  Left err -> assertFailure $ show err
  Right cp -> pure cp

isPrefixOfName :: String -> VM.Name -> Bool
isPrefixOfName prefix (VM.Name n) = take (length prefix) n == prefix

findTellOrFail :: CompiledProgram -> IO VM.Name
findTellOrFail cp =
  let prog = cpProgram cp
   in case [VM.procName p | p <- VM.progProcedures prog, "tell_" `isPrefixOfName` VM.procName p] of
        (n : _) -> pure n
        [] -> assertFailure "No tell procedure found"

buildProcMap :: CompiledProgram -> Map.Map VM.Name VM.Procedure
buildProcMap cp = Map.fromList [(VM.procName p, p) | p <- VM.progProcedures (cpProgram cp)]

runStack ::
  CompiledProgram ->
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
runStack cp m =
  runEff
    . runUnify
    . runCHRStore (VM.progNumTypes (cpProgram cp))
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
  ":- module(order, [leq/2]).\n\
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
  ":- module(fib, [fib/2]).\n\
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
    [ (VM.Name "+", \args -> let (a, b) = extractIntArgs "+" args in pure (RVal (VInt (a + b)))),
      (VM.Name "-", \args -> let (a, b) = extractIntArgs "-" args in pure (RVal (VInt (a - b))))
    ]

fibTests :: TestTree
fibTests =
  testGroup
    "Fibonacci (from surface language)"
    [ testCase "fib 10 = 55" $ do
        prog <- compileOrFail [("fib.chr", fibSource)]
        (_, bindings) <- runQuery prog fibHostCalls "fib:fib(10, R)"
        Map.lookup "R" bindings @?= Just (IntTerm 55)
    ]

-- ---------------------------------------------------------------------------
-- Query visibility
-- ---------------------------------------------------------------------------

hiddenSource :: Text
hiddenSource =
  ":- module(secret, []).\n\
  \:- chr_constraint hidden/1.\n\
  \\n\
  \hidden(X) <=> true.\n"

exportedSource :: Text
exportedSource =
  ":- module(pub, [visible/1]).\n\
  \:- chr_constraint visible/1.\n\
  \:- chr_constraint internal/1.\n\
  \\n\
  \visible(X) <=> true.\n\
  \internal(X) <=> true.\n"

ambiguousSourceA :: Text
ambiguousSourceA =
  ":- module(modA, [foo/1]).\n\
  \:- chr_constraint foo/1.\n\
  \\n\
  \foo(X) <=> true.\n"

ambiguousSourceB :: Text
ambiguousSourceB =
  ":- module(modB, [foo/1]).\n\
  \:- chr_constraint foo/1.\n\
  \\n\
  \foo(X) <=> true.\n"

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

visibilityTests :: TestTree
visibilityTests =
  testGroup
    "Query visibility"
    [ testCase "unqualified resolves to unique exported constraint" $ do
        cp <- compileOrFail [("pub.chr", exportedSource)]
        let q = Constraint (Unqualified "visible") [VarTerm "X"]
        case resolveQueryConstraint cp q of
          Right (Constraint (Qualified "pub" "visible") _) -> pure ()
          other -> assertFailure $ "Expected Right (Qualified pub visible), got: " ++ show other,
      testCase "unqualified hidden constraint fails" $ do
        cp <- compileOrFail [("secret.chr", hiddenSource)]
        let q = Constraint (Unqualified "hidden") [VarTerm "X"]
        assertBool "Should fail for hidden constraint" (isLeft (resolveQueryConstraint cp q)),
      testCase "qualified exported constraint succeeds" $ do
        cp <- compileOrFail [("pub.chr", exportedSource)]
        let q = Constraint (Qualified "pub" "visible") [VarTerm "X"]
        case resolveQueryConstraint cp q of
          Right _ -> pure ()
          Left err -> assertFailure $ "Should succeed: " ++ err,
      testCase "qualified hidden constraint fails" $ do
        cp <- compileOrFail [("secret.chr", hiddenSource)]
        let q = Constraint (Qualified "secret" "hidden") [VarTerm "X"]
        assertBool "Should fail for hidden qualified constraint" (isLeft (resolveQueryConstraint cp q)),
      testCase "qualified non-exported internal constraint fails" $ do
        cp <- compileOrFail [("pub.chr", exportedSource)]
        let q = Constraint (Qualified "pub" "internal") [VarTerm "X"]
        assertBool "Should fail for non-exported constraint" (isLeft (resolveQueryConstraint cp q)),
      testCase "ambiguous unqualified name fails" $ do
        cp <-
          compileOrFail
            [ ("a.chr", ambiguousSourceA),
              ("b.chr", ambiguousSourceB)
            ]
        let q = Constraint (Unqualified "foo") [VarTerm "X"]
        assertBool "Should fail for ambiguous constraint" (isLeft (resolveQueryConstraint cp q)),
      testCase "ambiguous name resolved with qualification" $ do
        cp <-
          compileOrFail
            [ ("a.chr", ambiguousSourceA),
              ("b.chr", ambiguousSourceB)
            ]
        let q = Constraint (Qualified "modA" "foo") [VarTerm "X"]
        case resolveQueryConstraint cp q of
          Right _ -> pure ()
          Left err -> assertFailure $ "Should succeed with qualification: " ++ err
    ]
