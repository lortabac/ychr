{-# LANGUAGE OverloadedStrings #-}

module YCHR.PExprTest (tests) where

import Data.Either (isLeft)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import Text.Megaparsec (ParseErrorBundle)
import YCHR.Loc (Ann (..), noAnn)
import YCHR.PExpr

tests :: TestTree
tests =
  testGroup
    "YCHR.PExpr"
    [ atomTests,
      variableTests,
      wildcardTests,
      intTests,
      stringTests,
      compoundTests,
      listTests,
      operatorTests,
      dotTerminationTests,
      commentTests,
      errorTests,
      prettyTests,
      roundtripTests
    ]

-- | Parse with no operators.
p :: Text -> Either (ParseErrorBundle Text Void) [Ann PExpr]
p = parseTerms emptyOps ""

-- | Parse with standard arithmetic operators.
pOps :: Text -> Either (ParseErrorBundle Text Void) [Ann PExpr]
pOps = parseTerms testOps ""

-- | An empty operator table.
emptyOps :: OpTable
emptyOps = mkOpTable []

-- | A small operator table for testing.
testOps :: OpTable
testOps =
  mkOpTable
    [ (200, [(InfixL, "*")]),
      (300, [(InfixL, "+"), (InfixL, "-")]),
      (700, [(InfixN, "is")]),
      (500, [(Prefix, "~")])
    ]

-- | Strip source locations from a term for structural comparison.
strip :: Ann PExpr -> PExpr
strip (Ann t _) = case t of
  Compound f args -> Compound f (map (noAnn . strip) args)
  other -> other

-- | Strip all terms in a parse result.
stripAll :: Either e [Ann PExpr] -> Either e [PExpr]
stripAll = fmap (map strip)

-- ---------------------------------------------------------------------------
-- Atoms
-- ---------------------------------------------------------------------------

atomTests :: TestTree
atomTests =
  testGroup
    "atoms"
    [ testCase "unquoted atom" $
        stripAll (p "foo.") @?= Right [Atom "foo"],
      testCase "single-quoted atom" $
        stripAll (p "'Hello World'.") @?= Right [Atom "Hello World"],
      testCase "quoted atom with escape" $
        stripAll (p "'it''s'.") @?= Right [Atom "it's"],
      testCase "quoted atom with backslash escape" $
        stripAll (p "'line\\none'.") @?= Right [Atom "line\none"],
      testCase "double underscore rejected" $
        assertBool "should fail" (isLeft (p "foo__bar."))
    ]

-- ---------------------------------------------------------------------------
-- Variables
-- ---------------------------------------------------------------------------

variableTests :: TestTree
variableTests =
  testGroup
    "variables"
    [ testCase "simple variable" $
        stripAll (p "X.") @?= Right [Var "X"],
      testCase "multi-char variable" $
        stripAll (p "Foo.") @?= Right [Var "Foo"],
      testCase "variable with digits" $
        stripAll (p "Bar1.") @?= Right [Var "Bar1"],
      testCase "variable with underscore" $
        stripAll (p "X_1.") @?= Right [Var "X_1"]
    ]

-- ---------------------------------------------------------------------------
-- Wildcards
-- ---------------------------------------------------------------------------

wildcardTests :: TestTree
wildcardTests =
  testGroup
    "wildcards"
    [ testCase "wildcard" $
        stripAll (p "_.") @?= Right [Wildcard]
    ]

-- ---------------------------------------------------------------------------
-- Integers
-- ---------------------------------------------------------------------------

intTests :: TestTree
intTests =
  testGroup
    "integers"
    [ testCase "positive integer" $
        stripAll (p "42.") @?= Right [Int 42],
      testCase "negative integer" $
        stripAll (p "-7.") @?= Right [Int (-7)],
      testCase "zero" $
        stripAll (p "0.") @?= Right [Int 0]
    ]

-- ---------------------------------------------------------------------------
-- Strings
-- ---------------------------------------------------------------------------

stringTests :: TestTree
stringTests =
  testGroup
    "strings"
    [ testCase "simple string" $
        stripAll (p "\"hello\".") @?= Right [Str "hello"],
      testCase "string with escape" $
        stripAll (p "\"line\\none\".") @?= Right [Str "line\none"],
      testCase "string with embedded quote" $
        stripAll (p "\"say \\\"hi\\\"\".") @?= Right [Str "say \"hi\""]
    ]

-- ---------------------------------------------------------------------------
-- Compounds
-- ---------------------------------------------------------------------------

compoundTests :: TestTree
compoundTests =
  testGroup
    "compounds"
    [ testCase "compound with args" $
        stripAll (p "f(X, Y).")
          @?= Right [Compound "f" [noAnn (Var "X"), noAnn (Var "Y")]],
      testCase "nested compound" $
        stripAll (p "f(g(a)).")
          @?= Right [Compound "f" [noAnn (Compound "g" [noAnn (Atom "a")])]],
      testCase "nullary compound" $
        stripAll (p "f.") @?= Right [Atom "f"],
      testCase "zero-arg compound" $
        stripAll (p "f().")
          @?= Right [Compound "f" []]
    ]

-- ---------------------------------------------------------------------------
-- Lists
-- ---------------------------------------------------------------------------

listTests :: TestTree
listTests =
  testGroup
    "lists"
    [ testCase "empty list" $
        stripAll (p "[].")
          @?= Right [Atom "[]"],
      testCase "simple list" $
        stripAll (p "[a, b, c].")
          @?= Right
            [ Compound
                "."
                [ noAnn (Atom "a"),
                  noAnn
                    ( Compound
                        "."
                        [ noAnn (Atom "b"),
                          noAnn (Compound "." [noAnn (Atom "c"), noAnn (Atom "[]")])
                        ]
                    )
                ]
            ],
      testCase "head|tail list" $
        stripAll (p "[H|T].")
          @?= Right
            [Compound "." [noAnn (Var "H"), noAnn (Var "T")]],
      testCase "multi head|tail" $
        stripAll (p "[a, b|T].")
          @?= Right
            [ Compound
                "."
                [ noAnn (Atom "a"),
                  noAnn (Compound "." [noAnn (Atom "b"), noAnn (Var "T")])
                ]
            ]
    ]

-- ---------------------------------------------------------------------------
-- Operators
-- ---------------------------------------------------------------------------

operatorTests :: TestTree
operatorTests =
  testGroup
    "operators"
    [ testCase "infix operator" $
        stripAll (pOps "X + Y.")
          @?= Right [Compound "+" [noAnn (Var "X"), noAnn (Var "Y")]],
      testCase "precedence: * binds tighter than +" $
        stripAll (pOps "X + Y * Z.")
          @?= Right
            [ Compound
                "+"
                [ noAnn (Var "X"),
                  noAnn (Compound "*" [noAnn (Var "Y"), noAnn (Var "Z")])
                ]
            ],
      testCase "prefix operator" $
        stripAll (pOps "~ X.")
          @?= Right [Compound "~" [noAnn (Var "X")]],
      testCase "word operator" $
        stripAll (pOps "X is Y.")
          @?= Right [Compound "is" [noAnn (Var "X"), noAnn (Var "Y")]],
      testCase "word operator rejected as atom" $
        assertBool "should fail" (isLeft (pOps "is."))
    ]

-- ---------------------------------------------------------------------------
-- Dot termination
-- ---------------------------------------------------------------------------

dotTerminationTests :: TestTree
dotTerminationTests =
  testGroup
    "dot termination"
    [ testCase "multiple terms" $
        stripAll (p "f(X). g(Y).")
          @?= Right
            [ Compound "f" [noAnn (Var "X")],
              Compound "g" [noAnn (Var "Y")]
            ],
      testCase "empty input" $
        stripAll (p "") @?= Right []
    ]

-- ---------------------------------------------------------------------------
-- Comments
-- ---------------------------------------------------------------------------

commentTests :: TestTree
commentTests =
  testGroup
    "comments"
    [ testCase "line comment" $
        stripAll (p "% this is a comment\nfoo.")
          @?= Right [Atom "foo"],
      testCase "comment between terms" $
        stripAll (p "a.\n% comment\nb.")
          @?= Right [Atom "a", Atom "b"]
    ]

-- ---------------------------------------------------------------------------
-- Error cases
-- ---------------------------------------------------------------------------

errorTests :: TestTree
errorTests =
  testGroup
    "errors"
    [ testCase "unterminated term" $
        assertBool "should fail" (isLeft (p "foo"))
    ]

-- ---------------------------------------------------------------------------
-- Pretty-printing
-- ---------------------------------------------------------------------------

-- | Pretty-print with no operators.
pp :: PExpr -> String
pp = prettyPExpr emptyOps

-- | Pretty-print with test operators.
ppOps :: PExpr -> String
ppOps = prettyPExpr testOps

prettyTests :: TestTree
prettyTests =
  testGroup
    "pretty-printing"
    [ testCase "atom" $
        pp (Atom "foo") @?= "foo",
      testCase "quoted atom (uppercase)" $
        pp (Atom "Foo") @?= "'Foo'",
      testCase "quoted atom (space)" $
        pp (Atom "hello world") @?= "'hello world'",
      testCase "quoted atom (embedded quote)" $
        pp (Atom "it's") @?= "'it''s'",
      testCase "quoted atom (empty)" $
        pp (Atom "") @?= "''",
      testCase "quoted atom (word operator)" $
        ppOps (Atom "is") @?= "'is'",
      testCase "variable" $
        pp (Var "X") @?= "X",
      testCase "wildcard" $
        pp Wildcard @?= "_",
      testCase "positive integer" $
        pp (Int 42) @?= "42",
      testCase "negative integer" $
        pp (Int (-7)) @?= "(-7)",
      testCase "string" $
        pp (Str "hello") @?= "\"hello\"",
      testCase "string with escapes" $
        pp (Str "say \"hi\"\n") @?= "\"say \\\"hi\\\"\\n\"",
      testCase "compound" $
        pp (Compound "f" [noAnn (Var "X"), noAnn (Var "Y")]) @?= "f(X, Y)",
      testCase "compound quoted functor" $
        pp (Compound "Hello" [noAnn (Var "X")]) @?= "'Hello'(X)",
      testCase "zero-arg compound" $
        pp (Compound "f" []) @?= "f()",
      testCase "empty list" $
        pp (Atom "[]") @?= "[]",
      testCase "list" $
        pp (Compound "." [noAnn (Atom "a"), noAnn (Compound "." [noAnn (Atom "b"), noAnn (Atom "[]")])])
          @?= "[a, b]",
      testCase "list with tail" $
        pp (Compound "." [noAnn (Atom "a"), noAnn (Var "T")])
          @?= "[a | T]",
      testCase "infix operator" $
        ppOps (Compound "+" [noAnn (Var "X"), noAnn (Var "Y")])
          @?= "X + Y",
      testCase "operator precedence (no parens needed)" $
        ppOps (Compound "+" [noAnn (Var "X"), noAnn (Compound "*" [noAnn (Var "Y"), noAnn (Var "Z")])])
          @?= "X + Y * Z",
      testCase "operator precedence (parens needed)" $
        ppOps (Compound "*" [noAnn (Compound "+" [noAnn (Var "X"), noAnn (Var "Y")]), noAnn (Var "Z")])
          @?= "(X + Y) * Z",
      testCase "left associativity (no parens)" $
        ppOps (Compound "+" [noAnn (Compound "+" [noAnn (Var "X"), noAnn (Var "Y")]), noAnn (Var "Z")])
          @?= "X + Y + Z",
      testCase "left associativity (parens on right)" $
        ppOps (Compound "+" [noAnn (Var "X"), noAnn (Compound "+" [noAnn (Var "Y"), noAnn (Var "Z")])])
          @?= "X + (Y + Z)",
      testCase "prefix operator" $
        ppOps (Compound "~" [noAnn (Var "X")])
          @?= "~ X",
      testCase "word operator" $
        ppOps (Compound "is" [noAnn (Var "X"), noAnn (Var "Y")])
          @?= "X is Y"
    ]

-- ---------------------------------------------------------------------------
-- Roundtrip tests
-- ---------------------------------------------------------------------------

-- | Assert that pretty-printing and re-parsing a single term produces the
-- same term (modulo source locations).
roundtrip :: OpTable -> String -> PExpr -> IO ()
roundtrip ops label expr = do
  let src = prettyPExpr ops expr
      input = T.pack (src ++ ".")
  case parseTerms ops "<roundtrip>" input of
    Left err -> assertFailure (label ++ ": parse failed on: " ++ show src ++ "\n" ++ show err)
    Right [ann] -> strip ann @?= expr
    Right ts -> assertFailure (label ++ ": expected 1 term, got " ++ show (length ts))

roundtripTests :: TestTree
roundtripTests =
  testGroup
    "roundtrip (parse . pretty = id)"
    [ testCase "atom" $ roundtrip emptyOps "atom" (Atom "foo"),
      testCase "quoted atom" $ roundtrip emptyOps "quoted atom" (Atom "Hello World"),
      testCase "atom with quote" $ roundtrip emptyOps "atom with quote" (Atom "it's"),
      testCase "empty atom" $ roundtrip emptyOps "empty atom" (Atom ""),
      testCase "variable" $ roundtrip emptyOps "variable" (Var "X"),
      testCase "wildcard" $ roundtrip emptyOps "wildcard" Wildcard,
      testCase "positive int" $ roundtrip emptyOps "positive int" (Int 42),
      testCase "negative int" $ roundtrip emptyOps "negative int" (Int (-7)),
      testCase "zero" $ roundtrip emptyOps "zero" (Int 0),
      testCase "string" $ roundtrip emptyOps "string" (Str "hello"),
      testCase "string with escapes" $ roundtrip emptyOps "string escapes" (Str "say \"hi\"\n\\"),
      testCase "compound" $
        roundtrip emptyOps "compound" (Compound "f" [noAnn (Var "X"), noAnn (Atom "a")]),
      testCase "nested compound" $
        roundtrip emptyOps "nested" (Compound "f" [noAnn (Compound "g" [noAnn (Atom "a")])]),
      testCase "zero-arg compound" $
        roundtrip emptyOps "zero-arg" (Compound "f" []),
      testCase "list" $
        roundtrip emptyOps "list" $
          Compound "." [noAnn (Atom "a"), noAnn (Compound "." [noAnn (Atom "b"), noAnn (Atom "[]")])],
      testCase "list with tail" $
        roundtrip emptyOps "list with tail" $
          Compound "." [noAnn (Atom "a"), noAnn (Var "T")],
      testCase "infix operator" $
        roundtrip testOps "infix" (Compound "+" [noAnn (Var "X"), noAnn (Var "Y")]),
      testCase "nested operators" $
        roundtrip testOps "nested ops" $
          Compound "+" [noAnn (Var "X"), noAnn (Compound "*" [noAnn (Var "Y"), noAnn (Var "Z")])],
      testCase "parens needed" $
        roundtrip testOps "parens" $
          Compound "*" [noAnn (Compound "+" [noAnn (Var "X"), noAnn (Var "Y")]), noAnn (Var "Z")],
      testCase "left assoc" $
        roundtrip testOps "left assoc" $
          Compound "+" [noAnn (Compound "+" [noAnn (Var "X"), noAnn (Var "Y")]), noAnn (Var "Z")],
      testCase "right grouping" $
        roundtrip testOps "right grouping" $
          Compound "+" [noAnn (Var "X"), noAnn (Compound "+" [noAnn (Var "Y"), noAnn (Var "Z")])],
      testCase "prefix operator" $
        roundtrip testOps "prefix" (Compound "~" [noAnn (Var "X")]),
      testCase "word operator" $
        roundtrip testOps "word op" (Compound "is" [noAnn (Var "X"), noAnn (Var "Y")]),
      testCase "quoted functor" $
        roundtrip emptyOps "quoted functor" (Compound "Hello" [noAnn (Var "X")]),
      testCase "word op as 3-arg functor" $
        roundtrip testOps "word op 3-arg" (Compound "is" [noAnn (Var "X"), noAnn (Var "Y"), noAnn (Var "Z")]),
      testCase "empty list" $
        roundtrip emptyOps "empty list" (Atom "[]")
    ]
