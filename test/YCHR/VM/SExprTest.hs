{-# LANGUAGE OverloadedStrings #-}

module YCHR.VM.SExprTest (tests) where

import Data.Text (Text)
import Data.Text qualified as T
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))
import YCHR.VM
import YCHR.VM.SExpr (deserialize, serialize)

tests :: TestTree
tests =
  testGroup
    "VM.SExpr"
    [ testGroup "roundtrip" roundtripTests,
      testGroup "format" formatTests
    ]

-- ---------------------------------------------------------------------------
-- Roundtrip: serialize then deserialize = identity
-- ---------------------------------------------------------------------------

roundtripTests :: [TestTree]
roundtripTests =
  [ testCase "empty program" $ roundtrip (Program 0 []),
    testCase "single empty procedure" $
      roundtrip (Program 1 [Procedure "foo" [] []]),
    testCase "procedure with params" $
      roundtrip (Program 1 [Procedure "tell_leq" ["X", "Y"] []]),
    testCase "let statement" $
      roundtrip (mkProg [Let "x" (Lit (IntLit 42))]),
    testCase "assign statement" $
      roundtrip (mkProg [Assign "x" (Lit (BoolLit True))]),
    testCase "if statement" $
      roundtrip (mkProg [If (Var "x") [Return (Lit (BoolLit True))] [Return (Lit (BoolLit False))]]),
    testCase "foreach statement" $
      roundtrip
        ( mkProg
            [ Foreach
                "L1"
                (ConstraintType 0)
                "susp"
                [(ArgIndex 0, Var "x"), (ArgIndex 1, Lit (IntLit 3))]
                [ExprStmt (Var "susp")]
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
                [ExprStmt (Var "s")]
            ]
        ),
    testCase "continue and break" $
      roundtrip (mkProg [Continue "L1", Break "L2"]),
    testCase "store and kill" $
      roundtrip (mkProg [Store (Var "id"), Kill (Var "id")]),
    testCase "add-history" $
      roundtrip (mkProg [AddHistory "rule1" [Var "id1", Var "id2"]]),
    testCase "drain-reactivation-queue" $
      roundtrip
        ( mkProg
            [ DrainReactivationQueue
                "rs"
                [ExprStmt (CallExpr "reactivate_dispatch" [Var "rs"])]
            ]
        ),
    testCase "all expression types" $
      roundtrip
        ( mkProg
            [ Let "a" (Var "x"),
              Let "b" (Lit (IntLit 42)),
              Let "c" (Lit (AtomLit "foo")),
              Let "d" (Lit (TextLit "hello world")),
              Let "e" (Lit (BoolLit True)),
              Let "f" (Lit (BoolLit False)),
              Let "g" (Lit WildcardLit),
              Let "h" (CallExpr "proc" [Var "a", Var "b"]),
              Let "i" (HostCall "+" [Var "a", Var "b"]),
              Let "j" (HostEval (Var "expr")),
              Let "k" (Not (Var "a")),
              Let "l" (And (Var "a") (Var "b")),
              Let "m" (Or (Var "a") (Var "b")),
              Let "n" NewVar,
              Let "o" (MakeTerm "f" [Var "a", Var "b"]),
              Let "p" (MatchTerm (Var "x") "f" 2),
              Let "q" (GetArg (Var "x") 0),
              Let "r" (CreateConstraint (ConstraintType 0) [Var "a"]),
              Let "s" (Alive (Var "id")),
              Let "t" (IdEqual (Var "id1") (Var "id2")),
              Let "u" (IsConstraintType (Var "s") (ConstraintType 1)),
              Let "v" (NotInHistory "rule" [Var "id1", Var "id2"]),
              Let "w" (Unify (Var "a") (Var "b")),
              Let "x2" (Equal (Var "a") (Var "b")),
              Let "y" (FieldGet (Var "s") FieldId),
              Let "z" (FieldGet (Var "s") (FieldArg (ArgIndex 0))),
              Let "z2" (FieldGet (Var "s") FieldType)
            ]
        ),
    testCase "call-expr with zero args" $
      roundtrip (mkProg [ExprStmt (CallExpr "noop" [])]),
    testCase "make-term with zero args" $
      roundtrip (mkProg [Let "x" (MakeTerm "nil" [])]),
    testCase "negative integer" $
      roundtrip (mkProg [Let "x" (Lit (IntLit (-5)))]),
    testCase "string with special characters" $
      roundtrip (mkProg [Let "x" (Lit (TextLit "hello\nworld\t\"quoted\""))]),
    testCase "multi-procedure program" $
      roundtrip
        ( Program
            2
            [ Procedure "tell_a" ["X"] [Let "id" (CreateConstraint (ConstraintType 0) [Var "X"]), Store (Var "id"), ExprStmt (CallExpr "activate_a" [Var "id"])],
              Procedure "activate_a" ["susp"] [Let "id" (Var "susp"), Let "X" (FieldGet (Var "susp") (FieldArg (ArgIndex 0))), Return (Lit (BoolLit False))],
              Procedure "reactivate_dispatch" ["susp"] [If (IsConstraintType (Var "susp") (ConstraintType 0)) [ExprStmt (CallExpr "activate_a" [Var "susp"])] []]
            ]
        )
  ]

-- | Assert that serializing then deserializing produces the original value.
roundtrip :: Program -> IO ()
roundtrip prog = do
  let text = serialize prog
  case deserialize text of
    Left e -> assertBool ("deserialization failed: " <> T.unpack e <> "\n\nserialized:\n" <> T.unpack text) False
    Right prog' -> prog' @?= prog

-- ---------------------------------------------------------------------------
-- Format: check that serialized output looks right
-- ---------------------------------------------------------------------------

formatTests :: [TestTree]
formatTests =
  [ testCase "var serialization" $
      serialize (mkProg [ExprStmt (Var "x")])
        @?= "(program 0 (procedure \"p\" () (expr-stmt (var \"x\"))))",
    testCase "literals inline without wrapper" $ do
      assertContains (serialize (mkProg [Let "x" (Lit (BoolLit True))])) "true"
      assertContains (serialize (mkProg [Let "x" (Lit (BoolLit False))])) "false"
      assertContains (serialize (mkProg [Let "x" (Lit WildcardLit)])) "wildcard"
      assertContains (serialize (mkProg [Let "x" (Lit (IntLit 7))])) "(int 7)"
      assertContains (serialize (mkProg [Let "x" (Lit (AtomLit "foo"))])) "(atom \"foo\")",
    testCase "new-var is a bare atom" $
      assertContains (serialize (mkProg [Let "x" NewVar])) "new-var"
  ]

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

-- | Build a minimal program with one procedure containing the given body.
mkProg :: [Stmt] -> Program
mkProg body = Program 0 [Procedure "p" [] body]

assertContains :: Text -> Text -> IO ()
assertContains haystack needle =
  assertBool
    ("expected " <> show needle <> " in:\n" <> T.unpack haystack)
    (needle `T.isInfixOf` haystack)
