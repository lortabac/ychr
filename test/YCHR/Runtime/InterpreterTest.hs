{-# LANGUAGE OverloadedStrings #-}

module YCHR.Runtime.InterpreterTest (tests) where

import Control.Exception (try)
import Control.Monad.IO.Class (liftIO)
import Data.Foldable (toList)
import Data.List (isInfixOf)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import YCHR.Runtime.Error (RuntimeErrorThrown (..))
import YCHR.Runtime.Interpreter
  ( HostCallFn (..),
    HostCallRegistry,
    baseHostCallRegistry,
    bindParams,
    callProc,
    interpret,
  )
import YCHR.Runtime.Monad (Chr, initSessionEnv, runChr)
import YCHR.Runtime.Store (getStoreSnapshot, isSuspAlive)
import YCHR.Runtime.Types (CallVal (..), SuspensionId (..), Value (..))
import YCHR.Runtime.Var (equal, newVar, unify)
import YCHR.Types qualified as Types
import YCHR.VM

tests :: TestTree
tests =
  testGroup
    "YCHR.Runtime.Interpreter"
    [ leqTests,
      evalDeepTests,
      typePredicateTests,
      univTests,
      bindParamsTests,
      errorPathTests
    ]

-- ---------------------------------------------------------------------------
-- Session helpers
-- ---------------------------------------------------------------------------

-- | Run a Chr action with an empty session (no procedures, no types,
-- no host calls). Useful for tests that exercise primitives that only
-- need 'Unify' / store / queue, where the session is set up just to
-- give them a place to live.
runChrEmpty :: Chr a -> IO a
runChrEmpty action = do
  env <- initSessionEnv [] [] Map.empty Map.empty Map.empty Map.empty Set.empty
  runChr action env

-- | Like 'runChrEmpty' but with the base host-call registry available.
runChrBase :: Chr a -> IO a
runChrBase action = do
  env <- initSessionEnv [] [] Map.empty baseHostCallRegistry Map.empty Map.empty Set.empty
  runChr action env

-- | Run a Chr action against the LEQ session.
runChrLeq :: Chr a -> IO a
runChrLeq action = do
  env <-
    initSessionEnv
      [Types.Unqualified "leq"]
      []
      leqProcMap
      Map.empty
      Map.empty
      Map.empty
      Set.empty
  runChr action env

-- ---------------------------------------------------------------------------
-- Runtime-error trigger tests
-- ---------------------------------------------------------------------------

-- | Run a single-procedure VM program and expect a 'RuntimeErrorThrown'.
expectRuntimeError :: Program -> Name -> [Value] -> IO String
expectRuntimeError prog entry args = do
  outcome <- try @RuntimeErrorThrown (interpret prog Map.empty entry args)
  case outcome of
    Left (RuntimeErrorThrown msg _stack) -> pure msg
    Right _ -> assertFailure "expected RuntimeErrorThrown, got a value"

singleProc :: Name -> [Name] -> [Stmt] -> Program
singleProc procName params body =
  Program
    { numTypes = 0,
      typeNames = [],
      numRules = 0,
      ruleNames = [],
      procedures = [mkProc procName params body],
      evaluables = []
    }

-- | Build a 'Procedure' with a placeholder 'procKind'. The kind tag
-- isn't observable by the interpreter tests (they exercise call /
-- store / unify behaviour, not tracing), so a single neutral
-- 'PKReactivateDispatch' keeps the test fixtures terse.
mkProc :: Name -> [Name] -> [Stmt] -> Procedure
mkProc n ps body =
  Procedure
    { name = n,
      params = ps,
      body = body,
      procKind = PKReactivateDispatch
    }

errorPathTests :: TestTree
errorPathTests =
  testGroup
    "runtime error paths"
    [ testCase "BFromVal on a non-bool value reports a guard error" $ do
        let prog =
              singleProc
                "p"
                []
                [ BoolExprStmt (BFromVal (Lit (IntLit 42))),
                  Return (Lit (BoolLit False))
                ]
        msg <- expectRuntimeError prog "p" []
        assertBool ("expected 'guard did not evaluate to a boolean' in: " ++ msg) $
          "guard did not evaluate to a boolean" `isInfixOf` msg,
      testCase "Break with a label no enclosing Foreach catches escapes" $ do
        let prog =
              singleProc
                "p"
                []
                [Break (Label "missing"), Return (Lit (BoolLit False))]
        msg <- expectRuntimeError prog "p" []
        assertBool ("expected 'uncaught Break' in: " ++ msg) $
          "uncaught Break" `isInfixOf` msg
        assertBool ("expected label 'missing' in: " ++ msg) $
          "missing" `isInfixOf` msg,
      testCase "Continue with a label no enclosing Foreach catches escapes" $ do
        let prog =
              singleProc
                "p"
                []
                [Continue (Label "nope"), Return (Lit (BoolLit False))]
        msg <- expectRuntimeError prog "p" []
        assertBool ("expected 'uncaught Continue' in: " ++ msg) $
          "uncaught Continue" `isInfixOf` msg
        assertBool ("expected label 'nope' in: " ++ msg) $
          "nope" `isInfixOf` msg,
      testCase "CallExpr targeting an unknown procedure errors with its name" $ do
        let prog =
              singleProc
                "p"
                []
                [ ExprStmt (CallExpr "no_such_proc" []),
                  Return (Lit (BoolLit False))
                ]
        msg <- expectRuntimeError prog "p" []
        assertBool ("expected 'unknown procedure' in: " ++ msg) $
          "unknown procedure" `isInfixOf` msg
        assertBool ("expected the missing name in: " ++ msg) $
          "no_such_proc" `isInfixOf` msg,
      testCase "evaluating an unbound named variable errors with its name" $ do
        let prog =
              singleProc
                "p"
                []
                [Return (Var "missing")]
        msg <- expectRuntimeError prog "p" []
        assertBool ("expected 'unbound variable' in: " ++ msg) $
          "unbound variable" `isInfixOf` msg
        assertBool ("expected the missing name in: " ++ msg) $
          "missing" `isInfixOf` msg,
      testCase "EvalDeep of an unbound fresh variable returns the variable itself" $ do
        let prog =
              singleProc
                "p"
                []
                [ LetVal "v" NewVar,
                  Return (EvalDeep (Var "v"))
                ]
        result <- interpret prog Map.empty "p" []
        case result of
          VVar _ -> pure ()
          _ -> assertFailure "expected VVar, got something else"
    ]

bindParamsTests :: TestTree
bindParamsTests =
  testGroup
    "bindParams"
    [ testCase "matching arity returns Right" $
        case bindParams "p" ["x", "y"] [CVal (VInt 1), CVal (VInt 2)] of
          Right _ -> pure ()
          Left msg -> assertFailure ("expected Right, got Left: " ++ msg),
      testCase "too few args returns Left with proc name" $
        case bindParams "myProc" ["x", "y"] [CVal (VInt 1)] of
          Left msg -> do
            assertBool ("missing arity-mismatch text in: " ++ msg) $
              "arity mismatch" `isInfixOf` msg
            assertBool ("missing proc name in: " ++ msg) $
              "myProc" `isInfixOf` msg
          Right _ -> assertFailure "expected Left",
      testCase "too many args returns Left" $
        case bindParams "p" ["x"] [CVal (VInt 1), CVal (VInt 2)] of
          Left msg ->
            assertBool ("missing arity-mismatch text in: " ++ msg) $
              "arity mismatch" `isInfixOf` msg
          Right _ -> assertFailure "expected Left",
      testCase "mixed-kind args bind by tag" $
        case bindParams "p" ["v", "i"] [CVal (VInt 7), CId (SuspensionId 3)] of
          Right _ -> pure ()
          Left msg -> assertFailure ("expected Right, got Left: " ++ msg)
    ]

-- ---------------------------------------------------------------------------
-- LEQ VM program
-- ---------------------------------------------------------------------------

leqType :: ConstraintType
leqType = ConstraintType 0

leqProgram :: Program
leqProgram =
  Program
    { numTypes = 1,
      typeNames = [Types.Unqualified "leq"],
      numRules = 1,
      ruleNames = ["transitivity"],
      evaluables = [],
      procedures =
        [ tellLeq,
          activateLeq,
          occurrenceLeq1,
          occurrenceLeq2,
          occurrenceLeq3,
          occurrenceLeq4,
          occurrenceLeq5,
          occurrenceLeq6,
          occurrenceLeq7,
          reactivateDispatch
        ]
    }

leqProcMap :: Map.Map Name Procedure
leqProcMap =
  Map.fromList [(p.name, p) | p <- leqProgram.procedures]

tellLeq :: Procedure
tellLeq =
  mkProc
    "tell_leq2"
    ["X", "Y"]
    [ LetId "id" (CreateConstraint leqType [Var "X", Var "Y"]),
      Store (IdVar "id"),
      ExprStmt (CallExpr "activate_leq2" [AId (IdVar "id")])
    ]

activateLeq :: Procedure
activateLeq =
  mkProc
    "activate_leq2"
    ["susp"]
    [ LetId "id" (IdVar "susp"),
      LetVal "X" (FieldArg (IdVar "susp") (ArgIndex 0)),
      LetVal "Y" (FieldArg (IdVar "susp") (ArgIndex 1)),
      LetVal "d" (CallExpr "occurrence_leq2_1" occCallArgs),
      If (BFromVal (Var "d")) [Return (Lit (BoolLit True))] [],
      LetVal "d" (CallExpr "occurrence_leq2_2" occCallArgs),
      If (BFromVal (Var "d")) [Return (Lit (BoolLit True))] [],
      LetVal "d" (CallExpr "occurrence_leq2_3" occCallArgs),
      If (BFromVal (Var "d")) [Return (Lit (BoolLit True))] [],
      LetVal "d" (CallExpr "occurrence_leq2_4" occCallArgs),
      If (BFromVal (Var "d")) [Return (Lit (BoolLit True))] [],
      LetVal "d" (CallExpr "occurrence_leq2_5" occCallArgs),
      If (BFromVal (Var "d")) [Return (Lit (BoolLit True))] [],
      LetVal "d" (CallExpr "occurrence_leq2_6" occCallArgs),
      If (BFromVal (Var "d")) [Return (Lit (BoolLit True))] [],
      LetVal "d" (CallExpr "occurrence_leq2_7" occCallArgs),
      If (BFromVal (Var "d")) [Return (Lit (BoolLit True))] [],
      Return (Lit (BoolLit False))
    ]
  where
    occCallArgs = [AId (IdVar "id"), AVal (Var "X"), AVal (Var "Y")]

occurrenceLeq1 :: Procedure
occurrenceLeq1 =
  mkProc
    "occurrence_leq2_1"
    ["id", "X", "Y"]
    [ If
        (BEqual (Var "X") (Var "Y"))
        [ Kill (IdVar "id"),
          Return (Lit (BoolLit True))
        ]
        [],
      Return (Lit (BoolLit False))
    ]

occurrenceLeq2 :: Procedure
occurrenceLeq2 =
  mkProc
    "occurrence_leq2_2"
    ["id", "X", "Y"]
    [ Foreach
        "L1"
        leqType
        "susp"
        []
        [ LetId "pId" (IdVar "susp"),
          LetVal "pA0" (FieldArg (IdVar "susp") (ArgIndex 0)),
          LetVal "pA1" (FieldArg (IdVar "susp") (ArgIndex 1)),
          If
            (BAnd (BAlive (IdVar "id")) (BAlive (IdVar "pId")))
            [ If
                (BNot (BIdEqual (IdVar "pId") (IdVar "id")))
                [ If
                    ( BAnd
                        (BEqual (Var "pA0") (Var "Y"))
                        (BEqual (Var "pA1") (Var "X"))
                    )
                    [ Kill (IdVar "pId"),
                      Kill (IdVar "id"),
                      BoolExprStmt (BUnify (Var "pA0") (Var "pA1")),
                      DrainReactivationQueue
                        "rs"
                        [ExprStmt (CallExpr "reactivate_dispatch" [AId (IdVar "rs")])],
                      Return (Lit (BoolLit True))
                    ]
                    []
                ]
                []
            ]
            []
        ],
      Return (Lit (BoolLit False))
    ]

occurrenceLeq3 :: Procedure
occurrenceLeq3 =
  mkProc
    "occurrence_leq2_3"
    ["id", "X", "Y"]
    [ Foreach
        "L1"
        leqType
        "susp"
        []
        [ LetId "pId" (IdVar "susp"),
          LetVal "pA0" (FieldArg (IdVar "susp") (ArgIndex 0)),
          LetVal "pA1" (FieldArg (IdVar "susp") (ArgIndex 1)),
          If
            (BAnd (BAlive (IdVar "id")) (BAlive (IdVar "pId")))
            [ If
                (BNot (BIdEqual (IdVar "pId") (IdVar "id")))
                [ If
                    ( BAnd
                        (BEqual (Var "X") (Var "pA1"))
                        (BEqual (Var "Y") (Var "pA0"))
                    )
                    [ Kill (IdVar "pId"),
                      Kill (IdVar "id"),
                      BoolExprStmt (BUnify (Var "X") (Var "Y")),
                      DrainReactivationQueue
                        "rs"
                        [ExprStmt (CallExpr "reactivate_dispatch" [AId (IdVar "rs")])],
                      Return (Lit (BoolLit True))
                    ]
                    []
                ]
                []
            ]
            []
        ],
      Return (Lit (BoolLit False))
    ]

occurrenceLeq4 :: Procedure
occurrenceLeq4 =
  mkProc
    "occurrence_leq2_4"
    ["id", "X", "Y"]
    [ Foreach
        "L1"
        leqType
        "susp"
        []
        [ LetId "pId" (IdVar "susp"),
          LetVal "pA0" (FieldArg (IdVar "susp") (ArgIndex 0)),
          LetVal "pA1" (FieldArg (IdVar "susp") (ArgIndex 1)),
          If
            (BAnd (BAlive (IdVar "id")) (BAlive (IdVar "pId")))
            [ If
                (BNot (BIdEqual (IdVar "pId") (IdVar "id")))
                [ If
                    ( BAnd
                        (BEqual (Var "pA0") (Var "X"))
                        (BEqual (Var "pA1") (Var "Y"))
                    )
                    [ Kill (IdVar "id"),
                      Return (Lit (BoolLit True))
                    ]
                    []
                ]
                []
            ]
            []
        ],
      Return (Lit (BoolLit False))
    ]

occurrenceLeq5 :: Procedure
occurrenceLeq5 =
  mkProc
    "occurrence_leq2_5"
    ["id", "X", "Y"]
    [ Foreach
        "L1"
        leqType
        "susp"
        []
        [ LetId "pId" (IdVar "susp"),
          LetVal "pA0" (FieldArg (IdVar "susp") (ArgIndex 0)),
          LetVal "pA1" (FieldArg (IdVar "susp") (ArgIndex 1)),
          If
            (BAnd (BAlive (IdVar "id")) (BAlive (IdVar "pId")))
            [ If
                (BNot (BIdEqual (IdVar "pId") (IdVar "id")))
                [ If
                    ( BAnd
                        (BEqual (Var "X") (Var "pA0"))
                        (BEqual (Var "Y") (Var "pA1"))
                    )
                    [Kill (IdVar "pId")]
                    []
                ]
                []
            ]
            []
        ],
      Return (Lit (BoolLit False))
    ]

occurrenceLeq6 :: Procedure
occurrenceLeq6 =
  mkProc
    "occurrence_leq2_6"
    ["id", "X", "Y"]
    [ Foreach
        "L1"
        leqType
        "susp"
        []
        [ LetId "pId" (IdVar "susp"),
          LetVal "pA0" (FieldArg (IdVar "susp") (ArgIndex 0)),
          LetVal "pA1" (FieldArg (IdVar "susp") (ArgIndex 1)),
          If
            (BAnd (BAlive (IdVar "id")) (BAlive (IdVar "pId")))
            [ If
                (BNot (BIdEqual (IdVar "pId") (IdVar "id")))
                [ If
                    (BEqual (Var "pA1") (Var "X"))
                    [ If
                        (BNotInHistory (RuleId 0) [IdVar "pId", IdVar "id"])
                        [ AddHistory (RuleId 0) [IdVar "pId", IdVar "id"],
                          ExprStmt
                            ( CallExpr
                                "tell_leq2"
                                [AVal (Var "pA0"), AVal (Var "Y")]
                            ),
                          If
                            (BNot (BAlive (IdVar "id")))
                            [Return (Lit (BoolLit True))]
                            []
                        ]
                        []
                    ]
                    []
                ]
                []
            ]
            []
        ],
      Return (Lit (BoolLit False))
    ]

occurrenceLeq7 :: Procedure
occurrenceLeq7 =
  mkProc
    "occurrence_leq2_7"
    ["id", "X", "Y"]
    [ Foreach
        "L1"
        leqType
        "susp"
        []
        [ LetId "pId" (IdVar "susp"),
          LetVal "pA0" (FieldArg (IdVar "susp") (ArgIndex 0)),
          LetVal "pA1" (FieldArg (IdVar "susp") (ArgIndex 1)),
          If
            (BAnd (BAlive (IdVar "id")) (BAlive (IdVar "pId")))
            [ If
                (BNot (BIdEqual (IdVar "pId") (IdVar "id")))
                [ If
                    (BEqual (Var "pA0") (Var "Y"))
                    [ If
                        (BNotInHistory (RuleId 0) [IdVar "id", IdVar "pId"])
                        [ AddHistory (RuleId 0) [IdVar "id", IdVar "pId"],
                          ExprStmt
                            ( CallExpr
                                "tell_leq2"
                                [AVal (Var "X"), AVal (Var "pA1")]
                            ),
                          If
                            (BNot (BAlive (IdVar "id")))
                            [Return (Lit (BoolLit True))]
                            []
                        ]
                        []
                    ]
                    []
                ]
                []
            ]
            []
        ],
      Return (Lit (BoolLit False))
    ]

reactivateDispatch :: Procedure
reactivateDispatch =
  mkProc
    "reactivate_dispatch"
    ["susp"]
    [ If
        (BIsConstraintType (IdVar "susp") leqType)
        [ExprStmt (CallExpr "activate_leq2" [AId (IdVar "susp")])]
        []
    ]

-- ---------------------------------------------------------------------------
-- Test helpers
-- ---------------------------------------------------------------------------

countAlive :: ConstraintType -> Chr Int
countAlive cType = do
  snapshot <- getStoreSnapshot cType
  alives <- traverse isSuspAlive (toList snapshot)
  pure (length (filter id alives))

callTellLeq :: Value -> Value -> Chr Value
callTellLeq x y =
  callProc "tell_leq2" [CVal x, CVal y]

-- ---------------------------------------------------------------------------
-- Tests
-- ---------------------------------------------------------------------------

leqTests :: TestTree
leqTests =
  testGroup
    "LEQ handler"
    [ testCase "reflexivity: leq(3, 3) fires, store empty" $ do
        n <- runChrLeq $ do
          _ <- callTellLeq (VInt 3) (VInt 3)
          countAlive leqType
        n @?= 0,
      testCase "no rule fires: leq(1, 2) stays" $ do
        n <- runChrLeq $ do
          _ <- callTellLeq (VInt 1) (VInt 2)
          countAlive leqType
        n @?= 1,
      testCase "antisymmetry: leq(X, Y), leq(Y, X) unifies X=Y, store empty" $ do
        (n, areEqual) <- runChrLeq $ do
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
        n <- runChrLeq $ do
          _ <- callTellLeq (VInt 1) (VInt 2)
          _ <- callTellLeq (VInt 2) (VInt 3)
          countAlive leqType
        n @?= 3,
      testCase "idempotence: leq(1,2), leq(1,2) removes duplicate" $ do
        n <- runChrLeq $ do
          _ <- callTellLeq (VInt 1) (VInt 2)
          _ <- callTellLeq (VInt 1) (VInt 2)
          countAlive leqType
        n @?= 1,
      testCase "full cycle: leq(a,b), leq(b,c), leq(c,a) — all removed, all unified" $ do
        (n, eqAB, eqBC) <- runChrLeq $ do
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

-- ---------------------------------------------------------------------------
-- EvalDeep tests
-- ---------------------------------------------------------------------------

arithCalls :: HostCallRegistry
arithCalls =
  Map.fromList
    [ ( "+",
        HostCallFn $ \args -> case args of
          [VInt a, VInt b] -> pure (VInt (a + b))
          _ -> liftIO (assertFailure "unexpected args to +")
      ),
      ( "*",
        HostCallFn $ \args -> case args of
          [VInt a, VInt b] -> pure (VInt (a * b))
          _ -> liftIO (assertFailure "unexpected args to *")
      )
    ]

makeCalcProc :: ValExpr -> Program
makeCalcProc body =
  Program
    { numTypes = 0,
      typeNames = [],
      numRules = 0,
      ruleNames = [],
      evaluables = [],
      procedures =
        [ mkProc
            "calc"
            ["x"]
            [ LetVal "y" (EvalDeep body),
              Return (Var "y")
            ]
        ]
    }

runCalc :: ValExpr -> Value -> IO Value
runCalc body x = interpret (makeCalcProc body) arithCalls "calc" [x]

expectInt :: Value -> IO Integer
expectInt (VInt n) = pure n
expectInt _ = assertFailure "expected VInt _"

evalDeepTests :: TestTree
evalDeepTests =
  testGroup
    "EvalDeep"
    [ testCase "flat: +(2, 3) = 5" $ do
        result <- runCalc (HostCall "+" [Lit (IntLit 2), Lit (IntLit 3)]) (VInt 0)
        expectInt result >>= (@?= 5),
      testCase "variable: x + 1, x=5 = 6" $ do
        result <- runCalc (HostCall "+" [Var "x", Lit (IntLit 1)]) (VInt 5)
        expectInt result >>= (@?= 6),
      testCase "nested: 2 * (x + 3), x=4 = 14" $ do
        result <-
          runCalc
            ( HostCall
                "*"
                [ Lit (IntLit 2),
                  HostCall
                    "+"
                    [ Var "x",
                      Lit (IntLit 3)
                    ]
                ]
            )
            (VInt 4)
        expectInt result >>= (@?= 14),
      testCase "literal passthrough: 42 = 42" $ do
        result <- runCalc (Lit (IntLit 42)) (VInt 0)
        expectInt result >>= (@?= 42)
    ]

-- ---------------------------------------------------------------------------
-- Type predicate tests
-- ---------------------------------------------------------------------------

-- | Call a base host call by name on a single Value, returning the result.
callBaseHC :: Name -> Value -> IO Value
callBaseHC name v = case Map.lookup name baseHostCallRegistry of
  Nothing -> assertFailure $ "host call not found: " ++ show name
  Just (HostCallFn f) -> runChrBase (f [v])

-- | Call a single-argument predicate, expecting a Bool.
callTypePred :: Name -> Value -> IO Bool
callTypePred name v = do
  result <- callBaseHC name v
  case result of
    VBool b -> pure b
    _ -> assertFailure $ show name ++ ": expected Bool result"

-- | Lookup a HostCallFn from the base registry, calling 'assertFailure'
-- if not found.
findBaseHC :: Name -> IO HostCallFn
findBaseHC name = case Map.lookup name baseHostCallRegistry of
  Nothing -> assertFailure $ "host call not found: " ++ show name
  Just fn -> pure fn

-- | Call 'term_variables' on a value, returning the resulting list value.
callTermVars :: Value -> IO Value
callTermVars v = do
  HostCallFn f <- findBaseHC (Name "term_variables")
  runChrBase (f [v])

-- | Variant inside a 'Chr' computation that already has a session set up.
callTermVarsChr :: Value -> Chr Value
callTermVarsChr v = case Map.lookup (Name "term_variables") baseHostCallRegistry of
  Nothing -> error "term_variables not found in registry"
  Just (HostCallFn f) -> f [v]

typePredicateTests :: TestTree
typePredicateTests =
  testGroup
    "Type predicates"
    [ testCase "integer: true for VInt" $ do
        b <- callTypePred "integer" (VInt 42)
        assertBool "expected true" b,
      testCase "integer: false for VAtom" $ do
        b <- callTypePred "integer" (VAtom "hello")
        assertBool "expected false" (not b),
      testCase "atom: true for VAtom" $ do
        b <- callTypePred "atom" (VAtom "hello")
        assertBool "expected true" b,
      testCase "atom: false for VInt" $ do
        b <- callTypePred "atom" (VInt 1)
        assertBool "expected false" (not b),
      testCase "boolean: true for VBool" $ do
        b <- callTypePred "boolean" (VBool True)
        assertBool "expected true" b,
      testCase "boolean: false for VAtom" $ do
        b <- callTypePred "boolean" (VAtom "true")
        assertBool "expected false" (not b),
      testCase "string: true for VText" $ do
        b <- callTypePred "string" (VText "hello")
        assertBool "expected true" b,
      testCase "string: false for VAtom" $ do
        b <- callTypePred "string" (VAtom "hello")
        assertBool "expected false" (not b),
      testCase "var: true for unbound variable" $ do
        b <- runChrBase $ do
          v <- newVar
          HostCallFn f <- case Map.lookup (Name "var") baseHostCallRegistry of
            Just hc -> pure hc
            Nothing -> error "var not found"
          result <- f [v]
          case result of
            VBool b' -> pure b'
            _ -> pure False
        assertBool "expected true" b,
      testCase "var: false for bound variable" $ do
        b <- runChrBase $ do
          v <- newVar
          _ <- unify v (VInt 42)
          HostCallFn f <- case Map.lookup (Name "var") baseHostCallRegistry of
            Just hc -> pure hc
            Nothing -> error "var not found"
          result <- f [v]
          case result of
            VBool b' -> pure b'
            _ -> pure False
        assertBool "expected false" (not b),
      testCase "var: false for ground value" $ do
        b <- callTypePred "var" (VInt 42)
        assertBool "expected false" (not b),
      testCase "nonvar: false for unbound variable" $ do
        b <- runChrBase $ do
          v <- newVar
          HostCallFn f <- case Map.lookup (Name "nonvar") baseHostCallRegistry of
            Just hc -> pure hc
            Nothing -> error "nonvar not found"
          result <- f [v]
          case result of
            VBool b' -> pure b'
            _ -> pure False
        assertBool "expected false" (not b),
      testCase "nonvar: true for bound variable" $ do
        b <- runChrBase $ do
          v <- newVar
          _ <- unify v (VInt 42)
          HostCallFn f <- case Map.lookup (Name "nonvar") baseHostCallRegistry of
            Just hc -> pure hc
            Nothing -> error "nonvar not found"
          result <- f [v]
          case result of
            VBool b' -> pure b'
            _ -> pure False
        assertBool "expected true" b,
      testCase "nonvar: true for ground value" $ do
        b <- callTypePred "nonvar" (VInt 42)
        assertBool "expected true" b,
      testCase "ground: true for integer" $ do
        b <- callTypePred "ground" (VInt 42)
        assertBool "expected true" b,
      testCase "ground: true for atom" $ do
        b <- callTypePred "ground" (VAtom "hello")
        assertBool "expected true" b,
      testCase "ground: true for ground compound" $ do
        b <- callTypePred "ground" (VTerm "f" [VInt 1, VAtom "hello"])
        assertBool "expected true" b,
      testCase "ground: false for unbound variable" $ do
        b <- runChrBase $ do
          v <- newVar
          HostCallFn f <- case Map.lookup (Name "ground") baseHostCallRegistry of
            Just hc -> pure hc
            Nothing -> error "ground not found"
          result <- f [v]
          case result of
            VBool b' -> pure b'
            _ -> pure True
        assertBool "expected false" (not b),
      testCase "ground: false for compound with unbound var" $ do
        b <- runChrBase $ do
          v <- newVar
          HostCallFn f <- case Map.lookup (Name "ground") baseHostCallRegistry of
            Just hc -> pure hc
            Nothing -> error "ground not found"
          result <- f [VTerm "f" [VInt 1, v]]
          case result of
            VBool b' -> pure b'
            _ -> pure True
        assertBool "expected false" (not b),
      testCase "ground: true for compound with bound var" $ do
        b <- runChrBase $ do
          v <- newVar
          _ <- unify v (VInt 2)
          HostCallFn f <- case Map.lookup (Name "ground") baseHostCallRegistry of
            Just hc -> pure hc
            Nothing -> error "ground not found"
          result <- f [VTerm "f" [VInt 1, v]]
          case result of
            VBool b' -> pure b'
            _ -> pure True
        assertBool "expected true" b,
      testCase "ground: false for wildcard" $ do
        b <- callTypePred "ground" VWildcard
        assertBool "expected false" (not b),
      testCase "term_variables: ground term yields empty list" $ do
        result <- callTermVars (VTerm "f" [VInt 1, VAtom "hello"])
        case result of
          VAtom "prelude__[]" -> pure ()
          _ -> assertFailure "expected empty list",
      testCase "term_variables: integer yields empty list" $ do
        result <- callTermVars (VInt 42)
        case result of
          VAtom "prelude__[]" -> pure ()
          _ -> assertFailure "expected empty list",
      testCase "term_variables: unbound var yields singleton list" $ do
        (isSingleton, sameVar) <- runChrBase $ do
          v <- newVar
          result <- callTermVarsChr v
          case result of
            VTerm "prelude__." [x, VAtom "prelude__[]"] -> do
              eq <- equal x v
              pure (True, eq)
            _ -> pure (False, False)
        assertBool "expected singleton list" isSingleton
        assertBool "list element should be same variable" sameVar,
      testCase "term_variables: duplicate var appears once" $ do
        (len, sameVar) <- runChrBase $ do
          v <- newVar
          result <- callTermVarsChr (VTerm "f" [v, v])
          case result of
            VTerm "prelude__." [x, VAtom "prelude__[]"] -> do
              eq <- equal x v
              pure (1 :: Int, eq)
            _ -> pure (0, False)
        len @?= 1
        assertBool "list element should be same variable" sameVar,
      testCase "term_variables: two distinct vars in order" $ do
        (len, eq1, eq2) <- runChrBase $ do
          x <- newVar
          y <- newVar
          result <- callTermVarsChr (VTerm "f" [x, y])
          case result of
            VTerm "prelude__." [a, VTerm "prelude__." [b, VAtom "prelude__[]"]] -> do
              e1 <- equal a x
              e2 <- equal b y
              pure (2 :: Int, e1, e2)
            _ -> pure (0, False, False)
        len @?= 2
        assertBool "first element should be X" eq1
        assertBool "second element should be Y" eq2,
      testCase "term_variables: wildcard produces fresh var" $ do
        result <- runChrBase $ callTermVarsChr VWildcard
        case result of
          VTerm "prelude__." [_, VAtom "prelude__[]"] -> pure ()
          _ -> assertFailure "expected singleton list",
      testCase "term_variables: nested compound" $ do
        (len, eq1, eq2) <- runChrBase $ do
          x <- newVar
          y <- newVar
          result <- callTermVarsChr (VTerm "f" [VTerm "g" [x, VInt 1], y])
          case result of
            VTerm "prelude__." [a, VTerm "prelude__." [b, VAtom "prelude__[]"]] -> do
              e1 <- equal a x
              e2 <- equal b y
              pure (2 :: Int, e1, e2)
            _ -> pure (0, False, False)
        len @?= 2
        assertBool "first element should be X" eq1
        assertBool "second element should be Y" eq2,
      testCase "unifiable: true for two equal integers" $ do
        b <- callUnifiable (VInt 1) (VInt 1)
        assertBool "expected true" b,
      testCase "unifiable: false for distinct integers" $ do
        b <- callUnifiable (VInt 1) (VInt 2)
        assertBool "expected false" (not b)
    ]
  where
    callUnifiable a b = case Map.lookup (Name "unifiable") baseHostCallRegistry of
      Nothing -> assertFailure "unifiable not found in registry"
      Just (HostCallFn f) -> do
        result <- runChrEmpty (f [a, b])
        case result of
          VBool b' -> pure b'
          _ -> assertFailure "unifiable: expected Bool result"

-- ---------------------------------------------------------------------------
-- =.. (univ) tests
-- ---------------------------------------------------------------------------

callHostCall1 :: Name -> Value -> IO Value
callHostCall1 name v = case Map.lookup name baseHostCallRegistry of
  Nothing -> assertFailure $ "host call not found: " ++ show name
  Just (HostCallFn f) -> runChrEmpty (f [v])

univTests :: TestTree
univTests =
  testGroup
    "compound_to_list / list_to_compound"
    [ testCase "compound_to_list: f(1, 2) -> [f, 1, 2]" $ do
        result <- callHostCall1 "compound_to_list" (VTerm "f" [VInt 1, VInt 2])
        case result of
          VTerm
            "prelude__."
            [ VAtom "f",
              VTerm
                "prelude__."
                [ VInt 1,
                  VTerm "prelude__." [VInt 2, VAtom "prelude__[]"]
                  ]
              ] -> pure ()
          _ -> assertFailure "unexpected result",
      testCase "compound_to_list: g(hello) -> [g, hello]" $ do
        result <- callHostCall1 "compound_to_list" (VTerm "g" [VAtom "hello"])
        case result of
          VTerm
            "prelude__."
            [ VAtom "g",
              VTerm
                "prelude__."
                [ VAtom "hello",
                  VAtom "prelude__[]"
                  ]
              ] -> pure ()
          _ -> assertFailure "unexpected result",
      testCase "compound_to_list: foo() -> [foo]" $ do
        result <- callHostCall1 "compound_to_list" (VTerm "foo" [])
        case result of
          VTerm "prelude__." [VAtom "foo", VAtom "prelude__[]"] -> pure ()
          _ -> assertFailure "unexpected result",
      testCase "compound_to_list: f(g(1), 2) -> [f, g(1), 2]" $ do
        result <- callHostCall1 "compound_to_list" (VTerm "f" [VTerm "g" [VInt 1], VInt 2])
        case result of
          VTerm
            "prelude__."
            [ VAtom "f",
              VTerm
                "prelude__."
                [ VTerm "g" [VInt 1],
                  VTerm "prelude__." [VInt 2, VAtom "prelude__[]"]
                  ]
              ] -> pure ()
          _ -> assertFailure "unexpected result",
      testCase "list_to_compound: [f, 1, 2] -> f(1, 2)" $ do
        let list =
              VTerm
                "prelude__."
                [ VAtom "f",
                  VTerm
                    "prelude__."
                    [ VInt 1,
                      VTerm "prelude__." [VInt 2, VAtom "prelude__[]"]
                    ]
                ]
        result <- callHostCall1 "list_to_compound" list
        case result of
          VTerm "f" [VInt 1, VInt 2] -> pure ()
          _ -> assertFailure "unexpected result",
      testCase "list_to_compound: [foo] -> foo (atom)" $ do
        let list = VTerm "prelude__." [VAtom "foo", VAtom "prelude__[]"]
        result <- callHostCall1 "list_to_compound" list
        case result of
          VAtom "foo" -> pure ()
          _ -> assertFailure "unexpected result",
      testCase "list_to_compound: [g, hello] -> g(hello)" $ do
        let list =
              VTerm
                "prelude__."
                [ VAtom "g",
                  VTerm
                    "prelude__."
                    [ VAtom "hello",
                      VAtom "prelude__[]"
                    ]
                ]
        result <- callHostCall1 "list_to_compound" list
        case result of
          VTerm "g" [VAtom "hello"] -> pure ()
          _ -> assertFailure "unexpected result"
    ]
