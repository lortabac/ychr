{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module YCHR.CompileTest (tests) where

import Data.Foldable (toList)
import Data.Map.Strict qualified as Map
import Effectful
import Effectful.Writer.Static.Local (Writer, runWriter)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))
import YCHR.Compile (compile)
import YCHR.DSL
import YCHR.Desugar (desugarProgram, extractSymbolTable)
import YCHR.Parsed (Module)
import YCHR.Rename (renameProgram)
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
    "YCHR.Compile"
    [ leqTests
    ]

-- ---------------------------------------------------------------------------
-- LEQ handler construction via DSL pipeline
-- ---------------------------------------------------------------------------

leqModule :: [Module]
leqModule =
  [ module' "Order"
      `declaring` ["leq" // 2]
      `defining` [ "reflexivity" @: ([con "leq" [var "X", var "X"]] <=> [atom "true"]),
                   "antisymmetry"
                     @: ( [con "leq" [var "X", var "Y"], con "leq" [var "Y", var "X"]]
                            <=> [var "X" .=. var "Y"]
                        ),
                   "idempotence"
                     @: (([con "leq" [var "X", var "Y"]] \\ [con "leq" [var "X", var "Y"]]) [atom "true"]),
                   "transitivity"
                     @: ( [con "leq" [var "X", var "Y"], con "leq" [var "Y", var "Z"]]
                            ==> [func "leq" [var "X", var "Z"]]
                        )
                 ]
  ]

-- | Build the compiled VM program from the LEQ modules.
compiledLeqProgram :: VM.Program
compiledLeqProgram =
  let Right renamed = renameProgram leqModule
      Right desugared = desugarProgram renamed
      symTab = extractSymbolTable desugared
   in compile desugared symTab

leqProcMap :: Map.Map VM.Name VM.Procedure
leqProcMap =
  let VM.Program {VM.progProcedures} = compiledLeqProgram
   in Map.fromList [(VM.procName p, p) | p <- progProcedures]

-- ---------------------------------------------------------------------------
-- Host call registry (empty for LEQ)
-- ---------------------------------------------------------------------------

leqHostCalls :: HostCallRegistry
leqHostCalls = Map.empty

-- ---------------------------------------------------------------------------
-- Test helpers
-- ---------------------------------------------------------------------------

leqType :: VM.ConstraintType
leqType = VM.ConstraintType 0

countAlive :: (CHRStore :> es) => VM.ConstraintType -> Eff es Int
countAlive cType = do
  snapshot <- getStoreSnapshot cType
  alives <- mapM isSuspAlive (toList snapshot)
  pure (length (filter id alives))

runFullStack ::
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
runFullStack m =
  runEff
    . runUnify
    . runCHRStore (VM.progNumTypes compiledLeqProgram)
    . runPropHistory
    . runReactQueue
    . fmap fst
    . runWriter @[SuspensionId]
    $ m

-- | Find the tell procedure name for leq.
tellLeqName :: VM.Name
tellLeqName =
  case [VM.procName p | p <- VM.progProcedures compiledLeqProgram, "tell_" `isPrefixOfName` VM.procName p] of
    (n : _) -> n
    [] -> error "No tell procedure found"

isPrefixOfName :: String -> VM.Name -> Bool
isPrefixOfName prefix (VM.Name n) = take (length prefix) n == prefix

callTellLeq ::
  ( Writer [SuspensionId] :> es,
    Unify :> es,
    CHRStore :> es,
    PropHistory :> es,
    ReactQueue :> es
  ) =>
  Value ->
  Value ->
  Eff es RuntimeVal
callTellLeq x y =
  callProc leqProcMap leqHostCalls tellLeqName [RVal x, RVal y]

-- ---------------------------------------------------------------------------
-- Tests
-- ---------------------------------------------------------------------------

leqTests :: TestTree
leqTests =
  testGroup
    "LEQ handler (compiled)"
    [ testCase "reflexivity: leq(3, 3) fires, store empty" $ do
        n <- runFullStack $ do
          _ <- callTellLeq (VInt 3) (VInt 3)
          countAlive leqType
        n @?= 0,
      testCase "no rule fires: leq(1, 2) stays" $ do
        n <- runFullStack $ do
          _ <- callTellLeq (VInt 1) (VInt 2)
          countAlive leqType
        n @?= 1,
      testCase "antisymmetry: leq(X, Y), leq(Y, X) unifies X=Y, store empty" $ do
        (n, areEqual) <- runFullStack $ do
          x <- newVar
          y <- newVar
          _ <- callTellLeq x y
          _ <- callTellLeq y x
          n <- countAlive leqType
          eq <- equal x y
          pure (n, eq)
        n @?= 0
        assertBool "X and Y should be unified" areEqual,
      testCase "transitivity: leq(1,2), leq(2,3) produces leq(1,3)" $ do
        n <- runFullStack $ do
          _ <- callTellLeq (VInt 1) (VInt 2)
          _ <- callTellLeq (VInt 2) (VInt 3)
          countAlive leqType
        -- leq(1,2), leq(2,3) stay, transitivity adds leq(1,3) = 3 total
        n @?= 3,
      testCase "idempotence: leq(1,2), leq(1,2) removes duplicate" $ do
        n <- runFullStack $ do
          _ <- callTellLeq (VInt 1) (VInt 2)
          _ <- callTellLeq (VInt 1) (VInt 2)
          countAlive leqType
        n @?= 1,
      testCase "full cycle: leq(a,b), leq(b,c), leq(c,a) — all removed, all unified" $ do
        (n, eqAB, eqBC) <- runFullStack $ do
          a <- newVar
          b <- newVar
          c <- newVar
          _ <- callTellLeq a b
          _ <- callTellLeq b c
          _ <- callTellLeq c a
          n <- countAlive leqType
          eqAB <- equal a b
          eqBC <- equal b c
          pure (n, eqAB, eqBC)
        n @?= 0
        assertBool "a and b should be unified" eqAB
        assertBool "b and c should be unified" eqBC
    ]
