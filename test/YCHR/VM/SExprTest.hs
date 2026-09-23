{-# LANGUAGE OverloadedStrings #-}

module YCHR.VM.SExprTest (tests) where

import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))
import YCHR.Internal.Types qualified as Types
import YCHR.Internal.VM
import YCHR.Internal.VM.SExpr (VMProgram (..), deserialize, serialize)

tests :: TestTree
tests =
  testGroup
    "VM.SExpr"
    [ testGroup "roundtrip" roundtripTests,
      testGroup "format" formatTests,
      testGroup "legacy" legacyProgramTests
    ]

-- ---------------------------------------------------------------------------
-- Roundtrip: serialize then deserialize = identity
-- ---------------------------------------------------------------------------

roundtripTests :: [TestTree]
roundtripTests =
  [ testCase "empty program" $ roundtrip (Program 0 [] 0 [] [] [] [] []),
    testCase "single empty procedure" $
      roundtrip (Program 1 [Types.Unqualified "foo"] 0 [] [mkProcedure "foo" [] []] [] [] []),
    testCase "procedure with params" $
      roundtrip
        ( Program
            1
            [Types.Unqualified "leq"]
            0
            []
            [mkProcedure "tell_leq2" ["X", "Y"] []]
            []
            []
            []
        ),
    testCase "let-val statement" $
      roundtrip (mkProg [LetVal "x" (Lit (IntLit 42))]),
    testCase "let-id statement" $
      roundtrip (mkProg [LetId "id" (CreateConstraint (ConstraintType 0) [Lit (IntLit 1)])]),
    testCase "assign-val statement" $
      roundtrip (mkProg [AssignVal "x" (Lit (BoolLit True))]),
    testCase "assign-id statement" $
      roundtrip (mkProg [AssignId "id" (IdVar "other")]),
    testCase "if statement" $
      roundtrip
        ( mkProg
            [ If
                (BFromVal (Var "x"))
                [Return (Lit (BoolLit True))]
                [ Return
                    ( Lit
                        ( BoolLit
                            False
                        )
                    )
                ]
            ]
        ),
    testCase "foreach statement" $
      roundtrip
        ( mkProg
            [ Foreach
                "L1"
                (ConstraintType 0)
                "susp"
                [(ArgIndex 0, Var "x"), (ArgIndex 1, Lit (IntLit 3))]
                [ExprStmt (FieldType (IdVar "susp"))]
            ]
        ),
    testCase "foreach with empty conditions" $
      roundtrip
        ( mkProg
            [ Foreach
                "L2"
                (ConstraintType 1)
                "s"
                []
                [ExprStmt (FieldType (IdVar "s"))]
            ]
        ),
    testCase "continue and break" $
      roundtrip (mkProg [Continue "L1", Break "L2"]),
    testCase "store and kill" $
      roundtrip (mkProg [Store (IdVar "id"), Kill (IdVar "id")]),
    testCase "add-history" $
      roundtrip (mkProg [AddHistory (RuleId 0) (histIds [IdVar "id1", IdVar "id2"])]),
    testCase "drain-reactivation-queue" $
      roundtrip
        ( mkProg
            [ DrainReactivationQueue
                "rs"
                [ExprStmt (CallExpr "reactivate_dispatch" [AId (IdVar "rs")])]
            ]
        ),
    testCase "all expression types" $
      roundtrip
        ( mkProg
            [ LetVal "a" (Var "x"),
              LetVal "b" (Lit (IntLit 42)),
              LetVal "b2" (Lit (FloatLit 3.14)),
              LetVal "c" (Lit (AtomLit "foo")),
              LetVal "d" (Lit (TextLit "hello world")),
              LetVal "e" (Lit (BoolLit True)),
              LetVal "f" (Lit (BoolLit False)),
              LetVal "h" (CallExpr "proc" [AVal (Var "a"), AVal (Var "b")]),
              LetVal "i" (HostCall "+" [Var "a", Var "b"]),
              LetVal "j" (EvalDeep (Var "expr")),
              LetVal "k" (EvalIs (Var "expr")),
              LetVal "l" (ApplyClosure (Var "f") [Var "a", Var "b"]),
              LetVal "n" NewVar,
              LetVal "o" (MakeTerm "f" [Var "a", Var "b"]),
              LetVal "q" (GetArg (Var "x") 0),
              LetId "r" (CreateConstraint (ConstraintType 0) [Var "a"]),
              LetId "y" (IdVar "s"),
              LetVal "z" (FieldArg (IdVar "s") (ArgIndex 0)),
              LetVal "z2" (FieldType (IdVar "s")),
              -- Boolean-position expressions exercised through If/BoolExprStmt.
              If (BLit True) [] [],
              If (BNot (BLit False)) [] [],
              If (BAnd (BLit True) (BLit False)) [] [],
              If (BOr (BLit True) (BLit False)) [] [],
              If (BMatchTerm (Var "x") "f" 2) [] [],
              If (BEqual (Var "a") (Var "b")) [] [],
              If (BIdEqual (IdVar "id1") (IdVar "id2")) [] [],
              If (BAlive (IdVar "id")) [] [],
              If (BIsConstraintType (IdVar "s") (ConstraintType 1)) [] [],
              If (BNotInHistory (RuleId 0) (histIds [IdVar "id1", IdVar "id2"])) [] [],
              BoolExprStmt (BUnify (Var "a") (Var "b")),
              If (BFromVal (Var "a")) [] [],
              If (BEvalDeep (BLit True)) [] [],
              If (BSoftGuard (BFromVal (Var "a"))) [] []
            ]
        ),
    testCase "call-expr with zero args" $
      roundtrip (mkProg [ExprStmt (CallExpr "noop" [])]),
    testCase "make-term with zero args" $
      roundtrip (mkProg [LetVal "x" (MakeTerm "nil" [])]),
    testCase "negative integer" $
      roundtrip (mkProg [LetVal "x" (Lit (IntLit (-5)))]),
    testCase "string with special characters" $
      roundtrip (mkProg [LetVal "x" (Lit (TextLit "hello\nworld\t\"quoted\""))]),
    testCase "multi-procedure program" $
      roundtrip
        ( Program
            2
            [Types.Unqualified "a", Types.Unqualified "b"]
            0
            []
            [ mkProcedure
                "tell_a1"
                ["X"]
                [ LetId
                    "id"
                    ( CreateConstraint
                        (ConstraintType 0)
                        [ Var
                            "X"
                        ]
                    ),
                  Store (IdVar "id"),
                  ExprStmt (CallExpr "activate_a1" [AId (IdVar "id")])
                ],
              mkProcedure
                "activate_a1"
                ["susp"]
                [ LetId "id" (IdVar "susp"),
                  LetVal "X" (FieldArg (IdVar "susp") (ArgIndex 0)),
                  Return (Lit (BoolLit False))
                ],
              mkProcedure
                "reactivate_dispatch"
                ["susp"]
                [ If
                    ( BIsConstraintType
                        (IdVar "susp")
                        (ConstraintType 0)
                    )
                    [ExprStmt (CallExpr "activate_a1" [AId (IdVar "susp")])]
                    []
                ]
            ]
            []
            []
            [ConstraintType 1]
        )
  ]

-- | Assert that serializing then deserializing produces the original value.
roundtrip :: Program -> IO ()
roundtrip prog = do
  let vmp = mkVMProg prog
      text = serialize vmp
  case deserialize text of
    Left e ->
      assertBool
        ( "deserialization failed: "
            <> T.unpack e
            <> "\n\nserialized:\n"
            <> T.unpack text
        )
        False
    Right vmp' -> vmp' @?= vmp

-- ---------------------------------------------------------------------------
-- Format: check that serialized output looks right
-- ---------------------------------------------------------------------------

formatTests :: [TestTree]
formatTests =
  [ testCase "var serialization" $
      assertContains
        (serializeProg (mkProg [ExprStmt (Var "x")]))
        ( "(program 0 (type-names) 0 (rule-names) (evaluables) (callables) "
            <> "(inert-types) "
            <> "(procedure \"p\" () (reactivate-dispatch) "
            <> "(expr-stmt (var \"x\"))))"
        ),
    testCase "callables entry serialization" $
      assertContains
        ( serializeProg
            (mkProgWithCallables [(funRefKey "prelude:double" 1, "func_prelude__double1")])
        )
        "(callables (\"/\" \"prelude:double\" 1 \"func_prelude__double1\"))",
    testCase "apply-closure serialization" $
      assertContains
        (serializeProg (mkProg [ExprStmt (ApplyClosure (Var "f") [Var "a"])]))
        "(apply-closure (var \"f\") (var \"a\"))",
    testCase "literals inline without wrapper" $ do
      assertContains (serializeProg (mkProg [LetVal "x" (Lit (BoolLit True))])) "true"
      assertContains (serializeProg (mkProg [LetVal "x" (Lit (BoolLit False))])) "false"
      assertContains (serializeProg (mkProg [LetVal "x" (Lit (IntLit 7))])) "(int 7)"
      assertContains
        (serializeProg (mkProg [LetVal "x" (Lit (AtomLit "foo"))]))
        "(atom \"foo\")",
    testCase "new-var is a bare atom" $
      assertContains (serializeProg (mkProg [LetVal "x" NewVar])) "new-var",
    testCase "exports and symbol table roundtrip" $
      let vmp =
            VMProgram
              { program =
                  Program
                    2
                    [Types.Qualified "M" "leq", Types.Unqualified "gcd"]
                    0
                    []
                    []
                    []
                    []
                    [],
                exportedSet =
                  Set.fromList
                    [ Types.QualifiedIdentifier "M" "leq" 2,
                      Types.QualifiedIdentifier "M" "gcd" 1
                    ],
                symbolTable =
                  Types.mkSymbolTable
                    [ ( Types.Identifier
                          ( Types.Qualified
                              "M"
                              "leq"
                          )
                          2,
                        Types.ConstraintType 0
                      ),
                      (Types.Identifier (Types.Unqualified "gcd") 1, Types.ConstraintType 1)
                    ]
              }
          text = serialize vmp
       in case deserialize text of
            Left e -> assertBool ("deserialization failed: " <> T.unpack e) False
            Right vmp' -> vmp' @?= vmp
  ]

serializeProg :: Program -> Text
serializeProg = serialize . mkVMProg

-- | A program header without the @callables@ and @inert-types@ entries
-- still loads, and declares no callable and no inert type: an absent
-- table is an empty one, and an absent hint changes no result.
--
-- This is a header-shape test, not a general back-compatibility
-- promise. The fixture below is a hand-written minimal program; one
-- written by a compiler before keyed @'$call'@ dispatch would also
-- carry @(call-dispatch N)@ procedures, a proc-kind the reader no
-- longer knows.
legacyProgramTests :: [TestTree]
legacyProgramTests =
  [ testCase "a header without the callables and inert-types entries loads" $
      case deserialize legacyProgramText of
        Left e -> assertBool ("deserialization failed: " <> T.unpack e) False
        Right vmp' -> vmp' @?= mkVMProg (mkProg [ExprStmt (Var "x")]),
    testCase "an explicit empty callables entry reads the same" $
      case deserialize
        (T.replace "(evaluables)" "(evaluables) (callables)" legacyProgramText) of
        Left e -> assertBool ("deserialization failed: " <> T.unpack e) False
        Right vmp' -> vmp' @?= mkVMProg (mkProg [ExprStmt (Var "x")])
  ]

legacyProgramText :: Text
legacyProgramText =
  "(vm-program (program 0 (type-names) 0 (rule-names) (evaluables) "
    <> "(procedure \"p\" () (reactivate-dispatch) "
    <> "(expr-stmt (var \"x\")))) (exports) (symbol-table))"

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

-- | A propagation-history tuple in head-position order, the way
-- 'YCHR.Internal.Compile.buildHistoryIds' builds one.
histIds :: [IdExpr] -> HistoryIds
histIds ids = mkHistoryIds (zip [0 :: Int ..] ids)

-- | Build a minimal program with one procedure containing the given body.
mkProg :: [Stmt] -> Program
mkProg body = Program 0 [] 0 [] [mkProcedure "p" [] body] [] [] []

-- | 'mkProg' with a non-empty callables table.
mkProgWithCallables :: [(CallableKey, Name)] -> Program
mkProgWithCallables callables =
  Program 0 [] 0 [] [mkProcedure "p" [] []] [] callables []

-- | A function-reference callables key, the shape
-- 'YCHR.Internal.Compile.buildCallables' mints for @fun name\/arity@.
funRefKey :: Name -> Int -> CallableKey
funRefKey identity arity =
  CallableKey {functor = funRefFunctor, identity = identity, arity = arity}

-- | Build a 'Procedure' with a placeholder 'procKind'. The kind tag
-- doesn't affect serialization round-tripping or the format tests'
-- assertions, so a single neutral value (with no payload) keeps the
-- fixtures concise.
mkProcedure :: Name -> [Name] -> [Stmt] -> Procedure
mkProcedure n ps body =
  Procedure
    { name = n,
      params = ps,
      body = body,
      procKind = PKReactivateDispatch
    }

-- | Wrap a Program into a VMProgram with empty metadata.
mkVMProg :: Program -> VMProgram
mkVMProg prog =
  VMProgram
    { program = prog,
      exportedSet = Set.empty,
      symbolTable = Types.mkSymbolTable []
    }

assertContains :: Text -> Text -> IO ()
assertContains haystack needle =
  assertBool
    ("expected " <> show needle <> " in:\n" <> T.unpack haystack)
    (needle `T.isInfixOf` haystack)
