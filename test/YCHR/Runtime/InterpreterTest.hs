{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module YCHR.Runtime.InterpreterTest (tests) where

import Data.Foldable (toList)
import Data.Map.Strict qualified as Map
import Effectful
import Effectful.Writer.Static.Local (Writer, runWriter)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import YCHR.Runtime.History (PropHistory, runPropHistory)
import YCHR.Runtime.Interpreter (HostCallFn (..), HostCallRegistry, baseHostCallRegistry, callProc, interpret)
import YCHR.Runtime.Reactivation (ReactQueue, runReactQueue)
import YCHR.Runtime.Store (CHRStore, getStoreSnapshot, isSuspAlive, runCHRStore)
import YCHR.Runtime.Types (RuntimeVal (..), SuspensionId (..), Value (..))
import YCHR.Runtime.Var (Unify, equal, newVar, runUnify, unify)
import YCHR.VM

tests :: TestTree
tests =
  testGroup
    "YCHR.Runtime.Interpreter"
    [ leqTests,
      hostEvalTests,
      typePredicateTests,
      univTests
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
  Procedure
    "tell_leq"
    ["X", "Y"]
    [ Let "id" (CreateConstraint leqType [Var "X", Var "Y"]),
      Store (Var "id"),
      ExprStmt (CallExpr "activate_leq" [Var "id", Var "X", Var "Y"])
    ]

activateLeq :: Procedure
activateLeq =
  Procedure
    "activate_leq"
    ["id", "X", "Y"]
    [ Let "d" (CallExpr "occurrence_leq_1" [Var "id", Var "X", Var "Y"]),
      If (Var "d") [Return (Lit (BoolLit True))] [],
      Let "d" (CallExpr "occurrence_leq_2" [Var "id", Var "X", Var "Y"]),
      If (Var "d") [Return (Lit (BoolLit True))] [],
      Let "d" (CallExpr "occurrence_leq_3" [Var "id", Var "X", Var "Y"]),
      If (Var "d") [Return (Lit (BoolLit True))] [],
      Let "d" (CallExpr "occurrence_leq_4" [Var "id", Var "X", Var "Y"]),
      If (Var "d") [Return (Lit (BoolLit True))] [],
      Let "d" (CallExpr "occurrence_leq_5" [Var "id", Var "X", Var "Y"]),
      If (Var "d") [Return (Lit (BoolLit True))] [],
      Let "d" (CallExpr "occurrence_leq_6" [Var "id", Var "X", Var "Y"]),
      If (Var "d") [Return (Lit (BoolLit True))] [],
      Let "d" (CallExpr "occurrence_leq_7" [Var "id", Var "X", Var "Y"]),
      If (Var "d") [Return (Lit (BoolLit True))] [],
      Return (Lit (BoolLit False))
    ]

occurrenceLeq1 :: Procedure
occurrenceLeq1 =
  Procedure
    "occurrence_leq_1"
    ["id", "X", "Y"]
    [ If
        (Equal (Var "X") (Var "Y"))
        [ Kill (Var "id"),
          Return (Lit (BoolLit True))
        ]
        [],
      Return (Lit (BoolLit False))
    ]

occurrenceLeq2 :: Procedure
occurrenceLeq2 =
  Procedure
    "occurrence_leq_2"
    ["id", "X", "Y"]
    [ Foreach
        "L1"
        leqType
        "susp"
        []
        [ Let "pId" (FieldGet (Var "susp") FieldId),
          Let "pA0" (FieldGet (Var "susp") (FieldArg (ArgIndex 0))),
          Let "pA1" (FieldGet (Var "susp") (FieldArg (ArgIndex 1))),
          If
            (And (Alive (Var "id")) (Alive (Var "pId")))
            [ If
                (Not (IdEqual (Var "pId") (Var "id")))
                [ If
                    ( And
                        (Equal (Var "pA0") (Var "Y"))
                        (Equal (Var "pA1") (Var "X"))
                    )
                    [ Kill (Var "pId"),
                      Kill (Var "id"),
                      ExprStmt (Unify (Var "pA0") (Var "pA1")),
                      DrainReactivationQueue
                        "rs"
                        [ExprStmt (CallExpr "reactivate_dispatch" [Var "rs"])],
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
  Procedure
    "occurrence_leq_3"
    ["id", "X", "Y"]
    [ Foreach
        "L1"
        leqType
        "susp"
        []
        [ Let "pId" (FieldGet (Var "susp") FieldId),
          Let "pA0" (FieldGet (Var "susp") (FieldArg (ArgIndex 0))),
          Let "pA1" (FieldGet (Var "susp") (FieldArg (ArgIndex 1))),
          If
            (And (Alive (Var "id")) (Alive (Var "pId")))
            [ If
                (Not (IdEqual (Var "pId") (Var "id")))
                [ If
                    ( And
                        (Equal (Var "X") (Var "pA1"))
                        (Equal (Var "Y") (Var "pA0"))
                    )
                    [ Kill (Var "pId"),
                      Kill (Var "id"),
                      ExprStmt (Unify (Var "X") (Var "Y")),
                      DrainReactivationQueue
                        "rs"
                        [ExprStmt (CallExpr "reactivate_dispatch" [Var "rs"])],
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
  Procedure
    "occurrence_leq_4"
    ["id", "X", "Y"]
    [ Foreach
        "L1"
        leqType
        "susp"
        []
        [ Let "pId" (FieldGet (Var "susp") FieldId),
          Let "pA0" (FieldGet (Var "susp") (FieldArg (ArgIndex 0))),
          Let "pA1" (FieldGet (Var "susp") (FieldArg (ArgIndex 1))),
          If
            (And (Alive (Var "id")) (Alive (Var "pId")))
            [ If
                (Not (IdEqual (Var "pId") (Var "id")))
                [ If
                    ( And
                        (Equal (Var "pA0") (Var "X"))
                        (Equal (Var "pA1") (Var "Y"))
                    )
                    [ Kill (Var "id"),
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
  Procedure
    "occurrence_leq_5"
    ["id", "X", "Y"]
    [ Foreach
        "L1"
        leqType
        "susp"
        []
        [ Let "pId" (FieldGet (Var "susp") FieldId),
          Let "pA0" (FieldGet (Var "susp") (FieldArg (ArgIndex 0))),
          Let "pA1" (FieldGet (Var "susp") (FieldArg (ArgIndex 1))),
          If
            (And (Alive (Var "id")) (Alive (Var "pId")))
            [ If
                (Not (IdEqual (Var "pId") (Var "id")))
                [ If
                    ( And
                        (Equal (Var "X") (Var "pA0"))
                        (Equal (Var "Y") (Var "pA1"))
                    )
                    [Kill (Var "pId")]
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
  Procedure
    "occurrence_leq_6"
    ["id", "X", "Y"]
    [ Foreach
        "L1"
        leqType
        "susp"
        []
        [ Let "pId" (FieldGet (Var "susp") FieldId),
          Let "pA0" (FieldGet (Var "susp") (FieldArg (ArgIndex 0))),
          Let "pA1" (FieldGet (Var "susp") (FieldArg (ArgIndex 1))),
          If
            (And (Alive (Var "id")) (Alive (Var "pId")))
            [ If
                (Not (IdEqual (Var "pId") (Var "id")))
                [ If
                    (Equal (Var "pA1") (Var "X"))
                    [ If
                        (NotInHistory "transitivity" [Var "pId", Var "id"])
                        [ AddHistory "transitivity" [Var "pId", Var "id"],
                          ExprStmt (CallExpr "tell_leq" [Var "pA0", Var "Y"]),
                          If
                            (Not (Alive (Var "id")))
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
  Procedure
    "occurrence_leq_7"
    ["id", "X", "Y"]
    [ Foreach
        "L1"
        leqType
        "susp"
        []
        [ Let "pId" (FieldGet (Var "susp") FieldId),
          Let "pA0" (FieldGet (Var "susp") (FieldArg (ArgIndex 0))),
          Let "pA1" (FieldGet (Var "susp") (FieldArg (ArgIndex 1))),
          If
            (And (Alive (Var "id")) (Alive (Var "pId")))
            [ If
                (Not (IdEqual (Var "pId") (Var "id")))
                [ If
                    (Equal (Var "pA0") (Var "Y"))
                    [ If
                        (NotInHistory "transitivity" [Var "id", Var "pId"])
                        [ AddHistory "transitivity" [Var "id", Var "pId"],
                          ExprStmt (CallExpr "tell_leq" [Var "X", Var "pA1"]),
                          If
                            (Not (Alive (Var "id")))
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
  Procedure
    "reactivate_dispatch"
    ["susp"]
    [ If
        (IsConstraintType (Var "susp") leqType)
        [ Let "rx" (FieldGet (Var "susp") (FieldArg (ArgIndex 0))),
          Let "ry" (FieldGet (Var "susp") (FieldArg (ArgIndex 1))),
          ExprStmt (CallExpr "activate_leq" [Var "susp", Var "rx", Var "ry"])
        ]
        []
    ]

-- ---------------------------------------------------------------------------
-- Host call registry (empty for LEQ)
-- ---------------------------------------------------------------------------

leqHostCalls :: HostCallRegistry
leqHostCalls = Map.empty

-- ---------------------------------------------------------------------------
-- Test helpers
-- ---------------------------------------------------------------------------

-- | Count alive constraints of a given type in the store.
countAlive :: (CHRStore :> es) => ConstraintType -> Eff es Int
countAlive cType = do
  snapshot <- getStoreSnapshot cType
  alives <- traverse isSuspAlive (toList snapshot)
  pure (length (filter id alives))

-- | Run within the full effect stack, returning a result.
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
    . runCHRStore 1
    . runPropHistory
    . runReactQueue
    . fmap fst
    . runWriter @[SuspensionId]
    $ m

-- | Call tell_leq within the full effect stack.
callTellLeq ::
  ( IOE :> es,
    Writer [SuspensionId] :> es,
    Unify :> es,
    CHRStore :> es,
    PropHistory :> es,
    ReactQueue :> es
  ) =>
  Value -> Value -> Eff es RuntimeVal
callTellLeq x y =
  callProc leqProcMap leqHostCalls "tell_leq" [RVal x, RVal y]

-- ---------------------------------------------------------------------------
-- Tests
-- ---------------------------------------------------------------------------

leqTests :: TestTree
leqTests =
  testGroup
    "LEQ handler"
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

-- ---------------------------------------------------------------------------
-- HostEval tests
-- ---------------------------------------------------------------------------

arithCalls :: HostCallRegistry
arithCalls =
  Map.fromList
    [ ( "+",
        HostCallFn $ \args -> case args of
          [RVal (VInt a), RVal (VInt b)] -> pure (RVal (VInt (a + b)))
          _ -> liftIO (assertFailure "unexpected args to +")
      ),
      ( "*",
        HostCallFn $ \args -> case args of
          [RVal (VInt a), RVal (VInt b)] -> pure (RVal (VInt (a * b)))
          _ -> liftIO (assertFailure "unexpected args to *")
      )
    ]

makeCalcProc :: Expr -> Program
makeCalcProc body =
  Program
    { numTypes = 0,
      procedures =
        [ Procedure
            "calc"
            ["x"]
            [ Let "y" (HostEval body),
              Return (Var "y")
            ]
        ]
    }

runCalc :: Expr -> Value -> IO RuntimeVal
runCalc body x = interpret (makeCalcProc body) arithCalls "calc" [x]

expectInt :: RuntimeVal -> IO Int
expectInt (RVal (VInt n)) = pure n
expectInt _ = assertFailure "expected RVal (VInt _)"

hostEvalTests :: TestTree
hostEvalTests =
  testGroup
    "HostEval"
    [ testCase "flat: +(2, 3) = 5" $ do
        result <- runCalc (HostCall "+" [Lit (IntLit 2), Lit (IntLit 3)]) (VInt 0)
        expectInt result >>= (@?= 5),
      testCase "variable: x + 1, x=5 = 6" $ do
        result <- runCalc (HostCall "+" [Var "x", Lit (IntLit 1)]) (VInt 5)
        expectInt result >>= (@?= 6),
      testCase "nested: 2 * (x + 3), x=4 = 14" $ do
        result <- runCalc (HostCall "*" [Lit (IntLit 2), HostCall "+" [Var "x", Lit (IntLit 3)]]) (VInt 4)
        expectInt result >>= (@?= 14),
      testCase "literal passthrough: 42 = 42" $ do
        result <- runCalc (Lit (IntLit 42)) (VInt 0)
        expectInt result >>= (@?= 42)
    ]

-- ---------------------------------------------------------------------------
-- Type predicate tests
-- ---------------------------------------------------------------------------

-- | Call a type predicate from baseHostCallRegistry and return the Bool result.
callTypePred :: Name -> Value -> IO Bool
callTypePred name v = case Map.lookup name baseHostCallRegistry of
  Nothing -> assertFailure $ "host call not found: " ++ show name
  Just (HostCallFn f) -> do
    result <- runEff . runUnify $ f [RVal v]
    case result of
      RVal (VBool b) -> pure b
      _ -> assertFailure $ show name ++ ": expected Bool result"

-- | Call term_variables directly, returning the resulting Value.
callTermVars :: Value -> IO Value
callTermVars v = case Map.lookup (Name "term_variables") baseHostCallRegistry of
  Nothing -> assertFailure "term_variables not found in registry"
  Just (HostCallFn f) -> do
    result <- runEff . runUnify $ f [RVal v]
    case result of
      RVal val -> pure val
      _ -> assertFailure "term_variables returned non-RVal"

-- | Call term_variables within an existing Eff context.
callTermVarsEff :: (Unify :> es, IOE :> es) => Value -> Eff es Value
callTermVarsEff v = case Map.lookup (Name "term_variables") baseHostCallRegistry of
  Nothing -> error "term_variables not found in registry"
  Just (HostCallFn f) -> do
    result <- f [RVal v]
    case result of
      RVal val -> pure val
      _ -> error "term_variables returned non-RVal"

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
        b <- runEff . runUnify $ do
          v <- newVar
          let HostCallFn f = case Map.lookup (Name "var") baseHostCallRegistry of
                Just hc -> hc
                Nothing -> error "var not found"
          result <- f [RVal v]
          case result of
            RVal (VBool b') -> pure b'
            _ -> pure False
        assertBool "expected true" b,
      testCase "var: false for bound variable" $ do
        (b, _) <- runEff . runUnify . runWriter @[SuspensionId] $ do
          v <- newVar
          _ <- unify v (VInt 42)
          let HostCallFn f = case Map.lookup (Name "var") baseHostCallRegistry of
                Just hc -> hc
                Nothing -> error "var not found"
          result <- f [RVal v]
          case result of
            RVal (VBool b') -> pure b'
            _ -> pure False
        assertBool "expected false" (not b),
      testCase "var: false for ground value" $ do
        b <- callTypePred "var" (VInt 42)
        assertBool "expected false" (not b),
      testCase "nonvar: false for unbound variable" $ do
        b <- runEff . runUnify $ do
          v <- newVar
          let HostCallFn f = case Map.lookup (Name "nonvar") baseHostCallRegistry of
                Just hc -> hc
                Nothing -> error "nonvar not found"
          result <- f [RVal v]
          case result of
            RVal (VBool b') -> pure b'
            _ -> pure False
        assertBool "expected false" (not b),
      testCase "nonvar: true for bound variable" $ do
        (b, _) <- runEff . runUnify . runWriter @[SuspensionId] $ do
          v <- newVar
          _ <- unify v (VInt 42)
          let HostCallFn f = case Map.lookup (Name "nonvar") baseHostCallRegistry of
                Just hc -> hc
                Nothing -> error "nonvar not found"
          result <- f [RVal v]
          case result of
            RVal (VBool b') -> pure b'
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
        b <- runEff . runUnify $ do
          v <- newVar
          let HostCallFn f = case Map.lookup (Name "ground") baseHostCallRegistry of
                Just hc -> hc
                Nothing -> error "ground not found"
          result <- f [RVal v]
          case result of
            RVal (VBool b') -> pure b'
            _ -> pure True
        assertBool "expected false" (not b),
      testCase "ground: false for compound with unbound var" $ do
        b <- runEff . runUnify $ do
          v <- newVar
          let HostCallFn f = case Map.lookup (Name "ground") baseHostCallRegistry of
                Just hc -> hc
                Nothing -> error "ground not found"
          result <- f [RVal (VTerm "f" [VInt 1, v])]
          case result of
            RVal (VBool b') -> pure b'
            _ -> pure True
        assertBool "expected false" (not b),
      testCase "ground: true for compound with bound var" $ do
        (b, _) <- runEff . runUnify . runWriter @[SuspensionId] $ do
          v <- newVar
          _ <- unify v (VInt 2)
          let HostCallFn f = case Map.lookup (Name "ground") baseHostCallRegistry of
                Just hc -> hc
                Nothing -> error "ground not found"
          result <- f [RVal (VTerm "f" [VInt 1, v])]
          case result of
            RVal (VBool b') -> pure b'
            _ -> pure True
        assertBool "expected true" b,
      testCase "ground: false for wildcard" $ do
        b <- callTypePred "ground" VWildcard
        assertBool "expected false" (not b),
      testCase "term_variables: ground term yields empty list" $ do
        result <- callTermVars (VTerm "f" [VInt 1, VAtom "hello"])
        case result of
          VAtom "[]" -> pure ()
          _ -> assertFailure "expected empty list",
      testCase "term_variables: integer yields empty list" $ do
        result <- callTermVars (VInt 42)
        case result of
          VAtom "[]" -> pure ()
          _ -> assertFailure "expected empty list",
      testCase "term_variables: unbound var yields singleton list" $ do
        (isSingleton, sameVar) <- runEff . runUnify $ do
          v <- newVar
          result <- callTermVarsEff v
          case result of
            VTerm "." [x, VAtom "[]"] -> do
              eq <- equal x v
              pure (True, eq)
            _ -> pure (False, False)
        assertBool "expected singleton list" isSingleton
        assertBool "list element should be same variable" sameVar,
      testCase "term_variables: duplicate var appears once" $ do
        (len, sameVar) <- runEff . runUnify $ do
          v <- newVar
          result <- callTermVarsEff (VTerm "f" [v, v])
          case result of
            VTerm "." [x, VAtom "[]"] -> do
              eq <- equal x v
              pure (1 :: Int, eq)
            _ -> pure (0, False)
        len @?= 1
        assertBool "list element should be same variable" sameVar,
      testCase "term_variables: two distinct vars in order" $ do
        (len, eq1, eq2) <- runEff . runUnify $ do
          x <- newVar
          y <- newVar
          result <- callTermVarsEff (VTerm "f" [x, y])
          case result of
            VTerm "." [a, VTerm "." [b, VAtom "[]"]] -> do
              e1 <- equal a x
              e2 <- equal b y
              pure (2 :: Int, e1, e2)
            _ -> pure (0, False, False)
        len @?= 2
        assertBool "first element should be X" eq1
        assertBool "second element should be Y" eq2,
      testCase "term_variables: wildcard produces fresh var" $ do
        result <- runEff . runUnify $ do
          callTermVarsEff VWildcard
        case result of
          VTerm "." [_, VAtom "[]"] -> pure ()
          _ -> assertFailure "expected singleton list",
      testCase "term_variables: nested compound" $ do
        (len, eq1, eq2) <- runEff . runUnify $ do
          x <- newVar
          y <- newVar
          result <- callTermVarsEff (VTerm "f" [VTerm "g" [x, VInt 1], y])
          case result of
            VTerm "." [a, VTerm "." [b, VAtom "[]"]] -> do
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

-- | Call a host call by name, passing a single Value argument.
callHostCall1 :: Name -> Value -> IO Value
callHostCall1 name v = case Map.lookup name baseHostCallRegistry of
  Nothing -> assertFailure $ "host call not found: " ++ show name
  Just (HostCallFn f) -> do
    result <- runEff . runUnify $ f [RVal v]
    case result of
      RVal val -> pure val
      _ -> assertFailure "expected RVal result"

univTests :: TestTree
univTests =
  testGroup
    "compound_to_list / list_to_compound"
    [ testCase "compound_to_list: f(1, 2) -> [f, 1, 2]" $ do
        result <- callHostCall1 "compound_to_list" (VTerm "f" [VInt 1, VInt 2])
        case result of
          VTerm "." [VAtom "f", VTerm "." [VInt 1, VTerm "." [VInt 2, VAtom "[]"]]] -> pure ()
          _ -> assertFailure "unexpected result",
      testCase "compound_to_list: g(hello) -> [g, hello]" $ do
        result <- callHostCall1 "compound_to_list" (VTerm "g" [VAtom "hello"])
        case result of
          VTerm "." [VAtom "g", VTerm "." [VAtom "hello", VAtom "[]"]] -> pure ()
          _ -> assertFailure "unexpected result",
      testCase "compound_to_list: foo() -> [foo]" $ do
        result <- callHostCall1 "compound_to_list" (VTerm "foo" [])
        case result of
          VTerm "." [VAtom "foo", VAtom "[]"] -> pure ()
          _ -> assertFailure "unexpected result",
      testCase "compound_to_list: f(g(1), 2) -> [f, g(1), 2]" $ do
        result <- callHostCall1 "compound_to_list" (VTerm "f" [VTerm "g" [VInt 1], VInt 2])
        case result of
          VTerm "." [VAtom "f", VTerm "." [VTerm "g" [VInt 1], VTerm "." [VInt 2, VAtom "[]"]]] -> pure ()
          _ -> assertFailure "unexpected result",
      testCase "list_to_compound: [f, 1, 2] -> f(1, 2)" $ do
        let list = VTerm "." [VAtom "f", VTerm "." [VInt 1, VTerm "." [VInt 2, VAtom "[]"]]]
        result <- callHostCall1 "list_to_compound" list
        case result of
          VTerm "f" [VInt 1, VInt 2] -> pure ()
          _ -> assertFailure "unexpected result",
      testCase "list_to_compound: [foo] -> foo()" $ do
        let list = VTerm "." [VAtom "foo", VAtom "[]"]
        result <- callHostCall1 "list_to_compound" list
        case result of
          VTerm "foo" [] -> pure ()
          _ -> assertFailure "unexpected result",
      testCase "list_to_compound: [g, hello] -> g(hello)" $ do
        let list = VTerm "." [VAtom "g", VTerm "." [VAtom "hello", VAtom "[]"]]
        result <- callHostCall1 "list_to_compound" list
        case result of
          VTerm "g" [VAtom "hello"] -> pure ()
          _ -> assertFailure "unexpected result"
    ]
