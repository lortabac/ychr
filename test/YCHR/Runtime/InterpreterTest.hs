{-# LANGUAGE OverloadedStrings #-}

module YCHR.Runtime.InterpreterTest (tests) where

-- 'try' comes from the shim so its type variables keep GHC's order
-- (dev-docs/MICROHS_GAPS.md, gap 7).
import Control.Exception.Shim (try)
import Control.Monad.IO.Class (liftIO)
import Data.Foldable (toList)
import Data.List (isInfixOf)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import YCHR.Internal.Loc (dummyLoc)
import YCHR.Internal.Runtime.Error (RuntimeErrorKind (..), RuntimeErrorThrown (..))
import YCHR.Internal.Runtime.Interpreter
  ( HostCallFn (..),
    HostCallRegistry,
    baseHostCallRegistry,
    bindParams,
    callProc,
    interpret,
  )
import YCHR.Internal.Runtime.Monad (Chr, initSessionEnv, runChr)
import YCHR.Internal.Runtime.Store (getStoreSnapshot, isSuspAlive)
import YCHR.Internal.Runtime.Types (CallVal (..), SuspensionId (..), Value (..))
import YCHR.Internal.Runtime.Var (equal, newVar, unify)
import YCHR.Internal.Types qualified as Types
import YCHR.Internal.VM

tests :: TestTree
tests =
  testGroup
    "YCHR.Internal.Runtime.Interpreter"
    [ leqTests,
      evalDeepTests,
      typePredicateTests,
      univTests,
      bindParamsTests,
      errorPathTests,
      errorKindTests,
      softGuardTests,
      closureApplyTests
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
  env <- initSessionEnv [] [] [] Map.empty Map.empty Map.empty Map.empty Map.empty Set.empty
  runChr action env

-- | Like 'runChrEmpty' but with the base host-call registry available.
runChrBase :: Chr a -> IO a
runChrBase action = do
  env <-
    initSessionEnv
      []
      []
      []
      Map.empty
      baseHostCallRegistry
      Map.empty
      Map.empty
      Map.empty
      Set.empty
  runChr action env

-- | Run a Chr action against the LEQ session.
runChrLeq :: Chr a -> IO a
runChrLeq action = do
  env <-
    initSessionEnv
      [Types.Unqualified "leq"]
      []
      []
      leqProcMap
      Map.empty
      Map.empty
      Map.empty
      Map.empty
      Set.empty
  runChr action env

-- ---------------------------------------------------------------------------
-- Runtime-error trigger tests
-- ---------------------------------------------------------------------------

-- | Run a single-procedure VM program and expect a 'RuntimeErrorThrown',
-- returning its message.
expectRuntimeError :: Program -> Name -> [Value] -> IO String
expectRuntimeError prog entry args = snd <$> expectRuntimeErrorKind prog entry args

-- | 'expectRuntimeError', also returning the error's 'RuntimeErrorKind'
-- so a test can pin whether a failure delays a rule guard or aborts.
expectRuntimeErrorKind ::
  Program -> Name -> [Value] -> IO (RuntimeErrorKind, String)
expectRuntimeErrorKind = expectRuntimeErrorKindWith Map.empty

-- | 'expectRuntimeErrorKind' with a host-call registry, for programs
-- whose failure comes from a primitive rather than the interpreter.
expectRuntimeErrorKindWith ::
  HostCallRegistry -> Program -> Name -> [Value] -> IO (RuntimeErrorKind, String)
expectRuntimeErrorKindWith registry prog entry args = do
  outcome <- try @RuntimeErrorThrown (interpret prog registry entry args)
  case outcome of
    Left (RuntimeErrorThrown kind msg _stack) -> pure (kind, msg)
    Right _ -> assertFailure "expected RuntimeErrorThrown, got a value"

singleProc :: Name -> [Name] -> [Stmt] -> Program
singleProc procName params body =
  Program
    { numTypes = 0,
      typeNames = [],
      numRules = 0,
      ruleNames = [],
      procedures = [mkProc procName params body],
      evaluables = [],
      callables = [],
      inertTypes = []
    }

-- | A propagation-history tuple in head-position order, the way
-- 'YCHR.Internal.Compile.buildHistoryIds' builds one.
histIds :: [IdExpr] -> HistoryIds
histIds ids = mkHistoryIds (zip [0 :: Int ..] ids)

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
    [ testCase "BFromVal on a bound non-bool value reports a guard error" $ do
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

-- ---------------------------------------------------------------------------
-- Runtime-error kind classification
-- ---------------------------------------------------------------------------

-- | Run @host(args)@ for its effect, with a fresh unbound variable
-- available as @v@, and report the kind and message of the failure.
hostFailure :: Name -> [ValExpr] -> IO (RuntimeErrorKind, String)
hostFailure host args =
  expectRuntimeErrorKindWith
    baseHostCallRegistry
    ( singleProc
        "p"
        []
        [ LetVal "v" NewVar,
          ExprStmt (HostCall host args),
          Return (Lit (BoolLit False))
        ]
    )
    "p"
    []

-- | Assert that a host call fails as an instantiation error — the
-- classification a rule guard catches.
assertInstantiation :: Name -> [ValExpr] -> IO ()
assertInstantiation host args = do
  (kind, msg) <- hostFailure host args
  assertBool
    ("expected InstantiationError from " ++ show host ++ ", got " ++ show kind ++ ": " ++ msg)
    (kind == InstantiationError)

-- | Assert that a host call fails as a general error — fatal in every
-- position, guards included.
assertGeneral :: Name -> [ValExpr] -> IO ()
assertGeneral host args = do
  (kind, msg) <- hostFailure host args
  assertBool
    ("expected GeneralError from " ++ show host ++ ", got " ++ show kind ++ ": " ++ msg)
    (kind == GeneralError)

-- | Assert that a host call /succeeds/ on an unbound argument with the
-- given boolean result: the primitive is total on unbound values and
-- must not be reclassified.
assertTotalOnUnbound :: Name -> [ValExpr] -> Bool -> IO ()
assertTotalOnUnbound host args expected = do
  let prog =
        singleProc
          "p"
          []
          [ LetVal "v" NewVar,
            Return (HostCall host args)
          ]
  result <- interpret prog baseHostCallRegistry "p" []
  case result of
    VBool b -> b @?= expected
    _ -> assertFailure ("expected a boolean from " ++ show host)

-- | The kind carried by a runtime error decides whether a rule guard
-- delays or the query aborts, so each primitive family is pinned on
-- both sides: an unbound argument on the failure path is an
-- instantiation error, a bound-but-wrong argument is a general one.
errorKindTests :: TestTree
errorKindTests =
  testGroup
    "runtime error kinds"
    [ testGroup
        "strict primitives on an unbound argument"
        [ testCase "numeric arithmetic" $
            assertInstantiation "+" [Var "v", Lit (IntLit 1)],
          testCase "integer division" $
            assertInstantiation "div" [Var "v", Lit (IntLit 2)],
          testCase "float division" $
            assertInstantiation "/" [Lit (FloatLit 1.0), Var "v"],
          testCase "numeric comparison" $
            assertInstantiation ">" [Var "v", Lit (IntLit 0)],
          testCase "numeric conversion" $
            assertInstantiation "int_to_float" [Var "v"],
          testCase "string operation" $
            assertInstantiation "string_length" [Var "v"],
          testCase "write" $
            assertInstantiation "write" [Var "v"],
          testCase "compound decomposition" $
            assertInstantiation "compound_to_list" [Var "v"],
          testCase "dispatch marker" $
            assertInstantiation
              "__chr_inst_error"
              [Lit (AtomLit "lists:length/1"), Lit (IntLit 1)]
        ],
      testGroup
        "strict primitives on a bound but wrong argument"
        [ testCase "numeric arithmetic" $
            assertGeneral "+" [Lit (AtomLit "a"), Lit (IntLit 1)],
          testCase "numeric comparison" $
            assertGeneral ">" [Lit (AtomLit "a"), Lit (IntLit 0)],
          testCase "string operation" $
            assertGeneral "string_length" [Lit (IntLit 1)],
          testCase "division by zero" $
            assertGeneral "div" [Lit (IntLit 1), Lit (IntLit 0)],
          testCase "no matching equation" $
            assertGeneral "__chr_error" [Lit (AtomLit "no matching equation in f/1")]
        ],
      testGroup
        "primitives total on unbound values are not reclassified"
        [ testCase "==" $
            assertTotalOnUnbound "==" [Var "v", Lit (IntLit 1)] False,
          testCase "unifiable" $
            assertTotalOnUnbound "unifiable" [Var "v", Lit (IntLit 1)] True,
          testCase "integer" $
            assertTotalOnUnbound "integer" [Var "v"] False,
          testCase "var" $
            assertTotalOnUnbound "var" [Var "v"] True
        ],
      testGroup
        "BFromVal"
        [ testCase "an unbound guard result is an instantiation error" $ do
            let prog =
                  singleProc
                    "p"
                    []
                    [ LetVal "v" NewVar,
                      BoolExprStmt (BFromVal (Var "v")),
                      Return (Lit (BoolLit False))
                    ]
            (kind, msg) <- expectRuntimeErrorKind prog "p" []
            kind @?= InstantiationError
            assertBool ("expected 'not sufficiently instantiated' in: " ++ msg) $
              "not sufficiently instantiated" `isInfixOf` msg,
          testCase "a bound non-boolean guard result is a general error" $ do
            let prog =
                  singleProc
                    "p"
                    []
                    [ BoolExprStmt (BFromVal (Lit (IntLit 42))),
                      Return (Lit (BoolLit False))
                    ]
            (kind, msg) <- expectRuntimeErrorKind prog "p" []
            kind @?= GeneralError
            assertBool ("expected 'did not evaluate to a boolean' in: " ++ msg) $
              "did not evaluate to a boolean" `isInfixOf` msg,
          testCase "a variable bound to a boolean is accepted" $ do
            let prog =
                  singleProc
                    "p"
                    []
                    [ LetVal "v" NewVar,
                      BoolExprStmt (BUnify (Var "v") (Lit (BoolLit True))),
                      If (BFromVal (Var "v")) [Return (Lit (IntLit 1))] [],
                      Return (Lit (IntLit 0))
                    ]
            result <- interpret prog Map.empty "p" []
            case result of
              VInt n -> n @?= 1
              _ -> assertFailure "expected an integer result"
        ]
    ]

-- ---------------------------------------------------------------------------
-- Soft guard failure
-- ---------------------------------------------------------------------------

-- | Run a program built around @If (BSoftGuard cond) …@ and report
-- which branch was taken.
softGuardBranch :: [Stmt] -> BoolExpr -> IO Bool
softGuardBranch prelude cond = do
  result <-
    interpret
      ( singleProc
          "p"
          []
          ( prelude
              ++ [ If
                     (BSoftGuard cond)
                     [Return (Lit (IntLit 1))]
                     [Return (Lit (IntLit 0))]
                 ]
          )
      )
      baseHostCallRegistry
      "p"
      []
  case result of
    VInt 1 -> pure True
    VInt 0 -> pure False
    _ -> assertFailure "expected an integer branch marker"

frame :: Text -> StackFrame
frame label =
  StackFrame
    { frameLabel = label,
      frameSourceLoc = dummyLoc,
      frameSourceCode = label
    }

-- | 'BSoftGuard' is the VM form behind rule-guard delaying: an
-- instantiation failure inside it becomes 'False', everything else
-- propagates. See @Note [Soft guard catch safety]@ in the interpreter.
softGuardTests :: TestTree
softGuardTests =
  testGroup
    "BSoftGuard"
    [ testCase "an instantiation failure evaluates to false" $ do
        result <-
          softGuardBranch
            [LetVal "v" NewVar]
            (BFromVal (HostCall ">" [Var "v", Lit (IntLit 0)]))
        result @?= False,
      testCase "a general failure propagates" $ do
        let prog =
              singleProc
                "p"
                []
                [ If
                    ( BSoftGuard
                        (BFromVal (HostCall ">" [Lit (AtomLit "a"), Lit (IntLit 0)]))
                    )
                    []
                    [],
                  Return (Lit (IntLit 0))
                ]
        (kind, _) <- expectRuntimeErrorKindWith baseHostCallRegistry prog "p" []
        kind @?= GeneralError,
      testCase "a decidable guard is unaffected" $ do
        yes <- softGuardBranch [] (BFromVal (HostCall ">" [Lit (IntLit 1), Lit (IntLit 0)]))
        yes @?= True
        no <- softGuardBranch [] (BFromVal (HostCall ">" [Lit (IntLit 0), Lit (IntLit 1)]))
        no @?= False,
      testCase "the catch also applies in deep-deref mode" $ do
        result <-
          softGuardBranch
            [LetVal "v" NewVar]
            (BEvalDeep (BFromVal (HostCall ">" [Var "v", Lit (IntLit 0)])))
        result @?= False,
      testCase "a caught failure leaves the call stack intact" $ do
        -- @q@ pushes a frame and then fails with an instantiation
        -- error. The soft guard swallows it; the general error raised
        -- afterwards must report only the frame pushed by @p@, because
        -- every procedure call restores the saved stack on the way out.
        let prog =
              Program
                { numTypes = 0,
                  typeNames = [],
                  numRules = 0,
                  ruleNames = [],
                  procedures =
                    [ mkProc
                        "p"
                        []
                        [ PushFrame (frame "caller"),
                          If (BSoftGuard (BFromVal (CallExpr "q" []))) [] [],
                          ExprStmt (HostCall "__chr_error" [Lit (AtomLit "boom")]),
                          Return (Lit (IntLit 0))
                        ],
                      mkProc
                        "q"
                        []
                        [ PushFrame (frame "callee"),
                          LetVal "v" NewVar,
                          Return (Var "v")
                        ]
                    ],
                  evaluables = [],
                  callables = [],
                  inertTypes = []
                }
        outcome <-
          try @RuntimeErrorThrown (interpret prog baseHostCallRegistry "p" [])
        case outcome of
          Left (RuntimeErrorThrown _ _ stack) ->
            map (.frameLabel) stack @?= ["caller"]
          Right _ -> assertFailure "expected RuntimeErrorThrown, got a value"
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
      callables = [],
      inertTypes = [],
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
                        (BNotInHistory (RuleId 0) (histIds [IdVar "pId", IdVar "id"]))
                        [ AddHistory (RuleId 0) (histIds [IdVar "pId", IdVar "id"]),
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
                        (BNotInHistory (RuleId 0) (histIds [IdVar "id", IdVar "pId"]))
                        [ AddHistory (RuleId 0) (histIds [IdVar "id", IdVar "pId"]),
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
      callables = [],
      inertTypes = [],
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
        expectInt result >>= (@?= 14)
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

-- | Variant inside a 'Chr' computation that already has a session set up.
callTermVarsChr :: Value -> Chr Value
callTermVarsChr v = case Map.lookup (Name "term_variables") baseHostCallRegistry of
  Nothing -> error "term_variables not found in registry"
  Just (HostCallFn f) -> f [v]

typePredicateTests :: TestTree
typePredicateTests =
  testGroup
    "Type predicates"
    [ testCase "integer: false for VAtom" $ do
        b <- callTypePred "integer" (VAtom "hello")
        assertBool "expected false" (not b),
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
      testCase "ground: true for integer" $ do
        b <- callTypePred "ground" (VInt 42)
        assertBool "expected true" b,
      testCase "ground: true for atom" $ do
        b <- callTypePred "ground" (VAtom "hello")
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
        assertBool "second element should be Y" eq2
    ]

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
    [ testCase "compound_to_list: g(hello) -> [g, hello]" $ do
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
          _ -> assertFailure "unexpected result"
    ]

-- ---------------------------------------------------------------------------
-- Closure application
-- ---------------------------------------------------------------------------

-- | The key a @fun m:f\/1@ reference dispatches on.
funKey :: CallableKey
funKey =
  CallableKey {functor = funRefFunctor, identity = Name "m:f", arity = 1}

-- | The key a lifted lambda with one capture and one declared parameter
-- dispatches on.
lamKey :: CallableKey
lamKey =
  CallableKey
    { functor = lambdaClosureFunctor,
      identity = Name "m__lambda_0",
      arity = 1
    }

-- | The closure value of @fun m:f\/1@.
funClosure :: Value
funClosure = VTerm "/" [VAtom "m:f", VInt 1]

-- | The closure value of a lifted lambda with one capture (@10@).
lamClosure :: Value
lamClosure = VTerm "__closure" [VAtom "m__lambda_0", VAtom "src", VInt 10]

-- | A program whose @p@ procedure applies its @f@ parameter to @1@ (and
-- @p2@ to @1@ and @2@) through the given callables table, plus the two
-- callee procedures the table can reach: @fun_proc@ returns its
-- argument, @lam_proc@ adds its capture to its argument.
closureProg :: [(CallableKey, Name)] -> Program
closureProg callables =
  Program
    { numTypes = 0,
      typeNames = [],
      numRules = 0,
      ruleNames = [],
      procedures =
        [ mkProc "p" ["f"] [Return (ApplyClosure (Var "f") [Lit (IntLit 1)])],
          mkProc
            "p2"
            ["f"]
            [Return (ApplyClosure (Var "f") [Lit (IntLit 1), Lit (IntLit 2)])],
          mkProc "fun_proc" ["a"] [Return (Var "a")],
          mkProc "lam_proc" ["cap", "a"] [Return (HostCall "+" [Var "cap", Var "a"])]
        ],
      evaluables = [],
      callables = callables,
      inertTypes = []
    }

-- | 'closureProg' with an unbound closure: @p@ allocates a fresh
-- logical variable and applies it.
unboundClosureProg :: [(CallableKey, Name)] -> Program
unboundClosureProg callables =
  (closureProg callables)
    { procedures =
        [ mkProc
            "p"
            []
            [ LetVal "f" NewVar,
              Return (ApplyClosure (Var "f") [Lit (IntLit 1)])
            ]
        ]
    }

-- | The runtime side of the @'$call'@ contract: which closure reaches
-- which procedure, how captures are threaded, and which failure a miss
-- produces. The end-to-end behavior — including what a whole compiled
-- program does with it — is pinned by the @closure_dispatch_errors@ and
-- @lambda_test@ golden directories.
closureApplyTests :: TestTree
closureApplyTests =
  testGroup
    "ApplyClosure"
    [ testCase "a function reference reaches its table entry" $ do
        v <-
          interpret
            (closureProg [(funKey, "fun_proc")])
            baseHostCallRegistry
            "p"
            [funClosure]
        case v of
          VInt 1 -> pure ()
          _ -> assertFailure "unexpected value",
      testCase "a lifted lambda is called with its captures first" $ do
        v <-
          interpret
            (closureProg [(lamKey, "lam_proc")])
            baseHostCallRegistry
            "p"
            [lamClosure]
        case v of
          VInt 11 -> pure ()
          _ -> assertFailure "unexpected value",
      testCase "a function reference applied at another arity misses" $
        expectRuntimeError
          (closureProg [(funKey, "fun_proc")])
          "p"
          [VTerm "/" [VAtom "m:f", VInt 2]]
          >>= assertContains "call: no matching closure",
      testCase "a lifted lambda applied at another arity misses" $
        -- A lambda closure does not record its declared arity, so the
        -- arity it is *applied* at selects the key; the table only holds
        -- the declared one.
        expectRuntimeError
          (closureProg [(lamKey, "lam_proc")])
          "p2"
          [lamClosure]
          >>= assertContains "call: no matching closure",
      testCase "a data term with a closure-looking field is not a closure" $
        expectRuntimeError
          (closureProg [(funKey, "fun_proc")])
          "p"
          [VTerm "pair" [VAtom "m:f", VInt 1]]
          >>= assertContains "call: no matching closure",
      testCase "a header field bound to the identity still dispatches" $ do
        -- The old dispatchers compared the header fields with BEqual,
        -- which dereferences: a function-reference term whose identity
        -- and arity fields are bound variables dispatched, and still
        -- must.
        let prog =
              (closureProg [(funKey, "fun_proc")])
                { procedures =
                    [ mkProc
                        "p"
                        ["n", "a"]
                        [ LetVal "f" (MakeTerm "/" [Var "n", Var "a"]),
                          Return (ApplyClosure (Var "f") [Lit (IntLit 7)])
                        ],
                      mkProc "fun_proc" ["x"] [Return (Var "x")]
                    ]
                }
        v <- interpret prog baseHostCallRegistry "p" [VAtom "m:f", VInt 1]
        case v of
          VInt 7 -> pure ()
          _ -> assertFailure "expected the bound header to dispatch",
      testCase "a non-term is not a closure" $
        expectRuntimeError
          (closureProg [(funKey, "fun_proc")])
          "p"
          [VInt 5]
          >>= assertContains "call: no matching closure",
      testCase "a well-formed closure with an unknown identity misses" $
        expectRuntimeError
          (closureProg [(funKey, "fun_proc")])
          "p"
          [VTerm "/" [VAtom "m:other", VInt 1]]
          >>= assertContains "call: no matching closure",
      testCase "an unbound closure is an instantiation error" $ do
        (kind, msg) <-
          expectRuntimeErrorKind
            (unboundClosureProg [(funKey, "fun_proc")])
            "p"
            []
        kind @?= InstantiationError
        assertContains "not sufficiently instantiated" msg
    ]
  where
    assertContains needle haystack =
      assertBool
        ("expected " ++ show needle ++ " in: " ++ haystack)
        (needle `isInfixOf` haystack)
