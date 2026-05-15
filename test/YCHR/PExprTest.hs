{-# LANGUAGE OverloadedStrings #-}

module YCHR.PExprTest (tests) where

import Data.Either (isLeft)
import Data.List (sort)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust, isNothing)
import Data.Text (Text)
import Data.Text qualified as T
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import Text.Parsec (ParseError)
import YCHR.Loc (Ann (..), SourceLoc (..), noAnn)
import YCHR.PExpr

tests :: TestTree
tests =
  testGroup
    "YCHR.PExpr"
    [ atomTests,
      variableTests,
      wildcardTests,
      intTests,
      floatTests,
      stringTests,
      stringEdgeTests,
      quotedAtomEdgeTests,
      compoundTests,
      listTests,
      operatorTests,
      maxPrecTests,
      dualRoleTests,
      postfixTests,
      prefixChainingTests,
      lambdaTests,
      symbolOpTokenTests,
      precedenceBoundaryTests,
      dotTerminationTests,
      commentTests,
      errorTests,
      opTypePredicateTests,
      mergeOpsTests,
      opTableEntriesTests,
      singleTermApiTests,
      renderAtomTests,
      prettyTests,
      floatAndPostfixPrettyTests,
      roundtripTests
    ]

-- | Parse with no operators.
p :: Text -> Either (ParseError) [Ann PExpr]
p = parseTerms emptyOps ""

-- | Parse with standard arithmetic operators.
pOps :: Text -> Either (ParseError) [Ann PExpr]
pOps = parseTerms testOps ""

-- | An empty operator table.
emptyOps :: OpTable
emptyOps = mkOpTable []

-- | A small operator table for testing.
testOps :: OpTable
testOps =
  mkOpTable
    [ (200, [(Yfx, "*")]),
      (300, [(Yfx, "+"), (Yfx, "-")]),
      (700, [(Xfx, "is")]),
      (500, [(Fx, "~")])
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
      testCase "infix word operator allowed as atom" $
        stripAll (pOps "is.") @?= Right [Atom "is"],
      testCase "infix word operator as functor" $
        stripAll (pOps "is(X, Y).")
          @?= Right [Compound "is" [noAnn (Var "X"), noAnn (Var "Y")]],
      testCase "prefix word operator rejected as atom" $
        let ops = mkOpTable [(500, [(Fx, "pre")])]
         in assertBool "should fail" (isLeft (parseTerms ops "" "pre.")),
      testCase "prefix word operator allowed as functor" $
        let ops = mkOpTable [(500, [(Fx, "pre")])]
         in stripAll (parseTerms ops "" "pre(X).")
              @?= Right [Compound "pre" [noAnn (Var "X")]]
    ]

-- ---------------------------------------------------------------------------
-- Max-precedence tests (comma and pipe as operators)
-- ---------------------------------------------------------------------------

-- | Operator table with comma and pipe as operators.
commaOps :: OpTable
commaOps =
  mkOpTable
    [ (200, [(Yfx, "*")]),
      (300, [(Yfx, "+")]),
      (700, [(Xfx, "=")]),
      (1000, [(Xfy, ",")]),
      (1100, [(Xfy, "|")])
    ]

-- | Parse with comma/pipe operators.
pComma :: Text -> Either (ParseError) [Ann PExpr]
pComma = parseTerms commaOps ""

maxPrecTests :: TestTree
maxPrecTests =
  testGroup
    "max-precedence"
    [ testCase "comma as operator at top level" $
        stripAll (pComma "a, b.")
          @?= Right [Compound "," [noAnn (Atom "a"), noAnn (Atom "b")]],
      testCase "comma suppressed in compound args" $
        stripAll (pComma "f(a, b).")
          @?= Right [Compound "f" [noAnn (Atom "a"), noAnn (Atom "b")]],
      testCase "pipe as operator at top level" $
        stripAll (pComma "a | b.")
          @?= Right [Compound "|" [noAnn (Atom "a"), noAnn (Atom "b")]],
      testCase "pipe suppressed in list tail" $
        stripAll (pComma "[a | T].")
          @?= Right [Compound "." [noAnn (Atom "a"), noAnn (Var "T")]],
      testCase "comma suppressed in list elements" $
        stripAll (pComma "[a, b].")
          @?= Right
            [ Compound
                "."
                [ noAnn (Atom "a"),
                  noAnn (Compound "." [noAnn (Atom "b"), noAnn (Atom "[]")])
                ]
            ],
      testCase "precedence: + binds tighter than comma" $
        stripAll (pComma "a + b, c.")
          @?= Right
            [ Compound
                ","
                [ noAnn (Compound "+" [noAnn (Atom "a"), noAnn (Atom "b")]),
                  noAnn (Atom "c")
                ]
            ],
      testCase "comma is right-associative" $
        stripAll (pComma "a, b, c.")
          @?= Right
            [ Compound
                ","
                [ noAnn (Atom "a"),
                  noAnn (Compound "," [noAnn (Atom "b"), noAnn (Atom "c")])
                ]
            ],
      testCase "pipe binds looser than comma" $
        stripAll (pComma "a, b | c.")
          @?= Right
            [ Compound
                "|"
                [ noAnn (Compound "," [noAnn (Atom "a"), noAnn (Atom "b")]),
                  noAnn (Atom "c")
                ]
            ],
      testCase "non-associative operator rejects chaining" $
        assertBool "should fail" (isLeft (pComma "a = b = c.")),
      testCase "parenthesized comma in compound arg" $
        stripAll (pComma "f((a, b)).")
          @?= Right [Compound "f" [noAnn (Compound "," [noAnn (Atom "a"), noAnn (Atom "b")])]],
      testCase "comma roundtrip" $
        roundtrip commaOps "comma" (Compound "," [noAnn (Atom "a"), noAnn (Atom "b")]),
      testCase "comma in compound arg roundtrip" $
        roundtrip commaOps "comma in arg" $
          Compound "f" [noAnn (Compound "," [noAnn (Atom "a"), noAnn (Atom "b")])]
    ]

-- ---------------------------------------------------------------------------
-- Dual-role operator tests
-- ---------------------------------------------------------------------------

-- | Operator table with - as both prefix (fy 200) and infix (yfx 500).
dualOps :: OpTable
dualOps =
  mkOpTable
    [ (200, [(Fy, "-")]),
      (500, [(Yfx, "-")]),
      (300, [(Yfx, "+")]),
      (200, [(Yfx, "*")])
    ]

-- | Parse with dual-role operators.
pDual :: Text -> Either (ParseError) [Ann PExpr]
pDual = parseTerms dualOps ""

dualRoleTests :: TestTree
dualRoleTests =
  testGroup
    "dual-role operators"
    [ testCase "prefix minus" $
        stripAll (pDual "- X.")
          @?= Right [Compound "-" [noAnn (Var "X")]],
      testCase "infix minus" $
        stripAll (pDual "X - Y.")
          @?= Right [Compound "-" [noAnn (Var "X"), noAnn (Var "Y")]],
      testCase "prefix and infix combined" $
        stripAll (pDual "X - - Y.")
          @?= Right
            [ Compound
                "-"
                [ noAnn (Var "X"),
                  noAnn (Compound "-" [noAnn (Var "Y")])
                ]
            ],
      testCase "negative integer literal preserved" $
        stripAll (pDual "-7.")
          @?= Right [Int (-7)]
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
        pp
          ( Compound
              "."
              [ noAnn (Atom "a"),
                noAnn
                  ( Compound
                      "."
                      [ noAnn (Atom "b"),
                        noAnn (Atom "[]")
                      ]
                  )
              ]
          )
          @?= "[a, b]",
      testCase "list with tail" $
        pp (Compound "." [noAnn (Atom "a"), noAnn (Var "T")])
          @?= "[a | T]",
      testCase "infix operator" $
        ppOps (Compound "+" [noAnn (Var "X"), noAnn (Var "Y")])
          @?= "X + Y",
      testCase "operator precedence (no parens needed)" $
        ppOps
          ( Compound
              "+"
              [ noAnn (Var "X"),
                noAnn
                  ( Compound
                      "*"
                      [ noAnn (Var "Y"),
                        noAnn (Var "Z")
                      ]
                  )
              ]
          )
          @?= "X + Y * Z",
      testCase "operator precedence (parens needed)" $
        ppOps
          ( Compound
              "*"
              [ noAnn (Compound "+" [noAnn (Var "X"), noAnn (Var "Y")]),
                noAnn (Var "Z")
              ]
          )
          @?= "(X + Y) * Z",
      testCase "left associativity (no parens)" $
        ppOps
          ( Compound
              "+"
              [ noAnn (Compound "+" [noAnn (Var "X"), noAnn (Var "Y")]),
                noAnn (Var "Z")
              ]
          )
          @?= "X + Y + Z",
      testCase "left associativity (parens on right)" $
        ppOps
          ( Compound
              "+"
              [ noAnn (Var "X"),
                noAnn
                  ( Compound
                      "+"
                      [ noAnn (Var "Y"),
                        noAnn (Var "Z")
                      ]
                  )
              ]
          )
          @?= "X + (Y + Z)",
      testCase "prefix operator" $
        ppOps (Compound "~" [noAnn (Var "X")])
          @?= "~ X",
      testCase "word operator" $
        ppOps (Compound "is" [noAnn (Var "X"), noAnn (Var "Y")])
          @?= "X is Y"
    ]

-- ---------------------------------------------------------------------------
-- Floats
-- ---------------------------------------------------------------------------

floatTests :: TestTree
floatTests =
  testGroup
    "floats"
    [ testCase "positive float" $
        stripAll (p "3.14.") @?= Right [Float 3.14],
      testCase "zero float" $
        stripAll (p "0.0.") @?= Right [Float 0.0],
      testCase "negative float" $
        stripAll (p "-2.5.") @?= Right [Float (-2.5)],
      testCase "many fractional digits" $
        stripAll (p "100.001.") @?= Right [Float 100.001],
      testCase "trailing zeros preserved as float" $
        stripAll (p "1.000.") @?= Right [Float 1.0],
      testCase "integer followed by dot terminator (not float)" $
        -- "3." is Int 3 with the dot acting as terminator (float needs
        -- at least one digit after '.').
        stripAll (p "3.") @?= Right [Int 3],
      testCase "float inside compound argument" $
        stripAll (p "f(1.5).") @?= Right [Compound "f" [noAnn (Float 1.5)]],
      testCase "float inside operator expression" $
        stripAll (pOps "1.5 + 2.5.")
          @?= Right [Compound "+" [noAnn (Float 1.5), noAnn (Float 2.5)]]
    ]

-- ---------------------------------------------------------------------------
-- String edge cases
-- ---------------------------------------------------------------------------

stringEdgeTests :: TestTree
stringEdgeTests =
  testGroup
    "string edge cases"
    [ testCase "empty string" $
        stripAll (p "\"\".") @?= Right [Str ""],
      testCase "tab escape" $
        stripAll (p "\"x\\ty\".") @?= Right [Str "x\ty"],
      testCase "newline escape" $
        stripAll (p "\"x\\ny\".") @?= Right [Str "x\ny"],
      testCase "backslash escape" $
        stripAll (p "\"x\\\\y\".") @?= Right [Str "x\\y"],
      testCase "double-quote escape" $
        stripAll (p "\"\\\"\".") @?= Right [Str "\""],
      testCase "unknown escape passes through (catch-all)" $
        -- '\a' is not a recognised escape; the catch-all anyChar yields 'a'.
        stripAll (p "\"\\a\".") @?= Right [Str "a"]
    ]

-- ---------------------------------------------------------------------------
-- Quoted-atom edge cases
-- ---------------------------------------------------------------------------

quotedAtomEdgeTests :: TestTree
quotedAtomEdgeTests =
  testGroup
    "quoted-atom edge cases"
    [ testCase "empty quoted atom" $
        stripAll (p "''.") @?= Right [Atom ""],
      testCase "tab escape" $
        stripAll (p "'a\\tb'.") @?= Right [Atom "a\tb"],
      testCase "newline escape" $
        stripAll (p "'a\\nb'.") @?= Right [Atom "a\nb"],
      testCase "backslash escape" $
        stripAll (p "'a\\\\b'.") @?= Right [Atom "a\\b"],
      testCase "apostrophe via backslash escape" $
        stripAll (p "'a\\'b'.") @?= Right [Atom "a'b"],
      testCase "apostrophe via doubled-quote form" $
        stripAll (p "'don''t'.") @?= Right [Atom "don't"],
      testCase "unknown escape passes through (catch-all)" $
        -- '\a' isn't a recognised escape; the catch-all anyChar yields 'a'.
        stripAll (p "'\\a'.") @?= Right [Atom "a"]
    ]

-- ---------------------------------------------------------------------------
-- Postfix operators
-- ---------------------------------------------------------------------------

-- | Operator table with postfix operators.
postfixOps :: OpTable
postfixOps =
  mkOpTable
    [ (300, [(Yfx, "+")]),
      (200, [(Xf, "!")]),
      (200, [(Yf, "++")])
    ]

pPostfix :: Text -> Either ParseError [Ann PExpr]
pPostfix = parseTerms postfixOps ""

postfixTests :: TestTree
postfixTests =
  testGroup
    "postfix operators"
    [ testCase "Xf postfix" $
        stripAll (pPostfix "X !.")
          @?= Right [Compound "!" [noAnn (Var "X")]],
      testCase "Yf postfix" $
        stripAll (pPostfix "X ++.")
          @?= Right [Compound "++" [noAnn (Var "X")]],
      testCase "Yf postfix chains" $
        stripAll (pPostfix "X ++ ++.")
          @?= Right
            [Compound "++" [noAnn (Compound "++" [noAnn (Var "X")])]],
      testCase "Xf postfix does not chain" $
        -- After consuming the first '!', the led-loop will not consume a
        -- second '!' because Xf requires the left operand to have strictly
        -- lower fixity than the operator.
        assertBool "should fail" (isLeft (pPostfix "X ! !.")),
      testCase "postfix combined with infix" $
        -- Postfix '!' (fix 200) binds tighter than infix '+' (fix 300).
        stripAll (pPostfix "X + Y !.")
          @?= Right
            [ Compound
                "+"
                [ noAnn (Var "X"),
                  noAnn (Compound "!" [noAnn (Var "Y")])
                ]
            ]
    ]

-- ---------------------------------------------------------------------------
-- Prefix chaining
-- ---------------------------------------------------------------------------

-- | Operator table mixing Fx (non-chaining) and Fy (chaining) prefix ops.
prefixChainOps :: OpTable
prefixChainOps =
  mkOpTable
    [ (200, [(Fy, "-")]),
      (500, [(Fx, "neg")])
    ]

pPrefixChain :: Text -> Either ParseError [Ann PExpr]
pPrefixChain = parseTerms prefixChainOps ""

prefixChainingTests :: TestTree
prefixChainingTests =
  testGroup
    "prefix chaining"
    [ testCase "Fy chains" $
        stripAll (pPrefixChain "- - X.")
          @?= Right
            [Compound "-" [noAnn (Compound "-" [noAnn (Var "X")])]],
      testCase "Fx does not chain" $
        -- 'neg' is Fx at 500; its operand parses at 499, where 'neg'
        -- (fixity 500) is no longer a legal prefix.  The whole parse
        -- fails.
        assertBool "should fail" (isLeft (pPrefixChain "neg neg X.")),
      testCase "Fx single use is fine" $
        stripAll (pPrefixChain "neg X.")
          @?= Right [Compound "neg" [noAnn (Var "X")]],
      testCase "prefix op at insufficient context (in compound arg)" $
        -- 'neg' at fixity 500 fits comfortably inside maxArgPrec=999.
        -- Lift its fixity above maxArgPrec to exercise the "not a prefix
        -- operator in this context" failure path.
        let hi = mkOpTable [(1100, [(Fx, "high")])]
         in assertBool "should fail" (isLeft (parseTerms hi "" "f(high X)."))
    ]

-- ---------------------------------------------------------------------------
-- Lambdas
-- ---------------------------------------------------------------------------

lambdaTests :: TestTree
lambdaTests =
  testGroup
    "lambdas"
    [ testCase "zero-arg lambda" $
        stripAll (p "fun() -> 42 end.")
          @?= Right [Compound "->" [noAnn (Compound "fun" []), noAnn (Int 42)]],
      testCase "one-arg lambda" $
        stripAll (p "fun(X) -> X end.")
          @?= Right
            [Compound "->" [noAnn (Compound "fun" [noAnn (Var "X")]), noAnn (Var "X")]],
      testCase "multi-arg lambda with operator body" $
        stripAll (pOps "fun(X, Y) -> X + Y end.")
          @?= Right
            [ Compound
                "->"
                [ noAnn (Compound "fun" [noAnn (Var "X"), noAnn (Var "Y")]),
                  noAnn (Compound "+" [noAnn (Var "X"), noAnn (Var "Y")])
                ]
            ],
      testCase "lambda body parses at maxPrec (comma as operator)" $
        stripAll (pComma "fun(X) -> X, X end.")
          @?= Right
            [ Compound
                "->"
                [ noAnn (Compound "fun" [noAnn (Var "X")]),
                  noAnn (Compound "," [noAnn (Var "X"), noAnn (Var "X")])
                ]
            ],
      testCase "lambda inside compound arg without parens" $
        stripAll (p "f(fun(X) -> X end, Y).")
          @?= Right
            [ Compound
                "f"
                [ noAnn
                    ( Compound
                        "->"
                        [ noAnn (Compound "fun" [noAnn (Var "X")]),
                          noAnn (Var "X")
                        ]
                    ),
                  noAnn (Var "Y")
                ]
            ],
      testCase "nested lambda" $
        stripAll (p "fun(X) -> fun(Y) -> Y end end.")
          @?= Right
            [ Compound
                "->"
                [ noAnn (Compound "fun" [noAnn (Var "X")]),
                  noAnn
                    ( Compound
                        "->"
                        [ noAnn (Compound "fun" [noAnn (Var "Y")]),
                          noAnn (Var "Y")
                        ]
                    )
                ]
            ],
      testCase "'fun' followed by identifier char is not a lambda keyword" $
        -- 'funky' is just an atom; lambdaP must not consume the 'fun'.
        stripAll (p "funky.") @?= Right [Atom "funky"],
      testCase "'end' followed by identifier char is not the lambda terminator" $
        -- 'endure' is parsed as a body atom; the real 'end' terminates the
        -- lambda after it.
        stripAll (p "fun(X) -> endure end.")
          @?= Right
            [ Compound
                "->"
                [ noAnn (Compound "fun" [noAnn (Var "X")]),
                  noAnn (Atom "endure")
                ]
            ]
    ]

-- ---------------------------------------------------------------------------
-- Symbol-operator tokenization
-- ---------------------------------------------------------------------------

-- | Operator table exercising symbol-op greedy matching.
greedyOps :: OpTable
greedyOps =
  mkOpTable
    [ (300, [(Yfx, "+")]),
      (200, [(Yfx, "++")])
    ]

pGreedy :: Text -> Either ParseError [Ann PExpr]
pGreedy = parseTerms greedyOps ""

symbolOpTokenTests :: TestTree
symbolOpTokenTests =
  testGroup
    "symbol operator tokenization"
    [ testCase "greedy match prefers '++' over '+ +'" $
        stripAll (pGreedy "X ++ Y.")
          @?= Right [Compound "++" [noAnn (Var "X"), noAnn (Var "Y")]],
      testCase "single '+' still works alongside '++'" $
        stripAll (pGreedy "X + Y.")
          @?= Right [Compound "+" [noAnn (Var "X"), noAnn (Var "Y")]],
      testCase "unknown symbol sequence fails" $
        -- '?' is a symbolChar but '??' is not declared as an operator.
        assertBool "should fail" (isLeft (pGreedy "X ?? Y.")),
      testCase "symbol operator usable as functor via quoting" $
        stripAll (pGreedy "'+'(X, Y).")
          @?= Right [Compound "+" [noAnn (Var "X"), noAnn (Var "Y")]]
    ]

-- ---------------------------------------------------------------------------
-- Precedence boundaries
-- ---------------------------------------------------------------------------

precedenceBoundaryTests :: TestTree
precedenceBoundaryTests =
  testGroup
    "precedence boundaries"
    [ testCase "operator at fixity 999 works inside compound" $
        -- maxArgPrec = 999; an op at exactly 999 is consumed inside f(...).
        let ops = mkOpTable [(999, [(Xfy, "@")])]
         in stripAll (parseTerms ops "" "f(a @ b).")
              @?= Right
                [ Compound
                    "f"
                    [noAnn (Compound "@" [noAnn (Atom "a"), noAnn (Atom "b")])]
                ],
      testCase "operator at fixity 1000 suppressed inside compound" $
        -- An op at 1000 (just above maxArgPrec) is not consumed inside f(...);
        -- it acts as a separator-like token causing a parse failure on the
        -- malformed argument list.
        let ops = mkOpTable [(1000, [(Xfy, "@")])]
         in assertBool "should fail" (isLeft (parseTerms ops "" "f(a @ b).")),
      testCase "operator at fixity 1000 works at top level" $
        let ops = mkOpTable [(1000, [(Xfy, "@")])]
         in stripAll (parseTerms ops "" "a @ b.")
              @?= Right [Compound "@" [noAnn (Atom "a"), noAnn (Atom "b")]],
      testCase "operator at fixity 1200 works at top level (maxPrec)" $
        let ops = mkOpTable [(1200, [(Xfx, ":-")])]
         in stripAll (parseTerms ops "" "a :- b.")
              @?= Right [Compound ":-" [noAnn (Atom "a"), noAnn (Atom "b")]]
    ]

-- ---------------------------------------------------------------------------
-- OpType predicates
-- ---------------------------------------------------------------------------

opTypePredicateTests :: TestTree
opTypePredicateTests =
  testGroup
    "opType predicates"
    [ testCase "isInfix" $ do
        isInfix Xfx @?= True
        isInfix Xfy @?= True
        isInfix Yfx @?= True
        isInfix Fx @?= False
        isInfix Fy @?= False
        isInfix Xf @?= False
        isInfix Yf @?= False,
      testCase "isPrefix" $ do
        isPrefix Fx @?= True
        isPrefix Fy @?= True
        isPrefix Xfx @?= False
        isPrefix Xfy @?= False
        isPrefix Yfx @?= False
        isPrefix Xf @?= False
        isPrefix Yf @?= False,
      testCase "isPostfix" $ do
        isPostfix Xf @?= True
        isPostfix Yf @?= True
        isPostfix Xfx @?= False
        isPostfix Xfy @?= False
        isPostfix Yfx @?= False
        isPostfix Fx @?= False
        isPostfix Fy @?= False
    ]

-- ---------------------------------------------------------------------------
-- mergeOps
-- ---------------------------------------------------------------------------

mergeOpsTests :: TestTree
mergeOpsTests =
  testGroup
    "mergeOps"
    [ testCase "adds new operator usable by parser" $
        case mergeOps emptyOps [(500, Yfx, "++")] of
          Left n -> assertFailure ("unexpected conflict: " ++ T.unpack n)
          Right merged ->
            stripAll (parseTerms merged "" "X ++ Y.")
              @?= Right [Compound "++" [noAnn (Var "X"), noAnn (Var "Y")]],
      testCase "identical re-declaration is a no-op" $
        let base = mkOpTable [(500, [(Yfx, "**")])]
         in case mergeOps base [(500, Yfx, "**")] of
              Left n -> assertFailure ("unexpected conflict: " ++ T.unpack n)
              Right _ -> pure (),
      testCase "prefix conflict (different fixity) returns Left" $
        let base = mkOpTable [(500, [(Fx, "foo")])]
         in case mergeOps base [(600, Fx, "foo")] of
              Left n -> n @?= "foo"
              Right _ -> assertFailure "expected conflict",
      testCase "prefix conflict (different type) returns Left" $
        let base = mkOpTable [(500, [(Fx, "foo")])]
         in case mergeOps base [(500, Fy, "foo")] of
              Left n -> n @?= "foo"
              Right _ -> assertFailure "expected conflict",
      testCase "infix conflict returns Left" $
        let base = mkOpTable [(500, [(Yfx, "@")])]
         in case mergeOps base [(600, Yfx, "@")] of
              Left n -> n @?= "@"
              Right _ -> assertFailure "expected conflict",
      testCase "dual-role allowed: prefix added when infix exists" $
        let base = mkOpTable [(500, [(Yfx, "-")])]
         in case mergeOps base [(200, Fy, "-")] of
              Left n -> assertFailure ("unexpected conflict: " ++ T.unpack n)
              Right merged -> do
                Map.lookup "-" merged.prefixByName @?= Just (200, Fy)
                Map.lookup "-" merged.infixByName @?= Just (500, Yfx),
      testCase "postfix declarations populate infixByName" $
        case mergeOps emptyOps [(200, Xf, "!")] of
          Left n -> assertFailure ("unexpected conflict: " ++ T.unpack n)
          Right merged -> Map.lookup "!" merged.infixByName @?= Just (200, Xf),
      testCase "non-symbolic op extends wordOpSet" $
        case mergeOps emptyOps [(700, Xfx, "is")] of
          Left n -> assertFailure ("unexpected conflict: " ++ T.unpack n)
          Right merged ->
            assertBool "is should be in wordOpSet" $
              "is" `elem` [name | (_, _, name) <- opTableEntries merged]
    ]

-- ---------------------------------------------------------------------------
-- opTableEntries
-- ---------------------------------------------------------------------------

opTableEntriesTests :: TestTree
opTableEntriesTests =
  testGroup
    "opTableEntries"
    [ testCase "roundtrip mkOpTable -> opTableEntries" $
        let entries =
              [ (200, Yfx, "*"),
                (300, Yfx, "+"),
                (500, Fx, "neg"),
                (200, Xf, "!"),
                (700, Xfx, "is")
              ]
            grouped =
              [ (200, [(Yfx, "*"), (Xf, "!")]),
                (300, [(Yfx, "+")]),
                (500, [(Fx, "neg")]),
                (700, [(Xfx, "is")])
              ]
            table = mkOpTable grouped
            -- OpType lacks Ord, so compare via Show as a stable key.
            key (fix, ty, name) = (fix, show ty, name)
         in sort (map key (opTableEntries table)) @?= sort (map key entries)
    ]

-- ---------------------------------------------------------------------------
-- Single-term API (parseTermNoDot, parseFirstTerm, parseLeadingTerms)
-- ---------------------------------------------------------------------------

singleTermApiTests :: TestTree
singleTermApiTests =
  testGroup
    "single-term APIs"
    [ testCase "parseTermNoDot accepts a bare term" $
        case parseTermNoDot emptyOps "" "f(X)" of
          Left err -> assertFailure (show err)
          Right ann -> strip ann @?= Compound "f" [noAnn (Var "X")],
      testCase "parseTermNoDot rejects trailing dot" $
        assertBool "should fail" (isLeft (parseTermNoDot emptyOps "" "foo.")),
      testCase "parseFirstTerm on empty input is Nothing" $
        case parseFirstTerm emptyOps "" "" of
          Left err -> assertFailure (show err)
          Right m -> assertBool "should be Nothing" (isNothing m),
      testCase "parseFirstTerm returns first term, ignores rest" $
        case parseFirstTerm emptyOps "" "foo. bar. baz." of
          Left err -> assertFailure (show err)
          Right (Just ann) -> strip ann @?= Atom "foo"
          Right Nothing -> assertFailure "expected Just foo",
      testCase "parseFirstTerm with no dot returns Nothing" $
        -- No dot anywhere means no complete term — the inner try backtracks.
        case parseFirstTerm emptyOps "" "foo bar" of
          Left err -> assertFailure (show err)
          Right m -> assertBool "should be Nothing" (isNothing m),
      testCase "parseLeadingTerms: all parse" $
        case parseLeadingTerms emptyOps "" "foo. bar." of
          Left err -> assertFailure (show err)
          Right (terms, mLoc) -> do
            map strip terms @?= [Atom "foo", Atom "bar"]
            assertBool "no remainder expected" (isNothing mLoc),
      testCase "parseLeadingTerms: partial parse leaves remainder" $
        case parseLeadingTerms emptyOps "" "foo. ???" of
          Left err -> assertFailure (show err)
          Right (terms, mLoc) -> do
            map strip terms @?= [Atom "foo"]
            assertBool "remainder expected" (isJust mLoc),
      testCase "parseLeadingTerms: failure at start yields empty list" $
        case parseLeadingTerms emptyOps "" "???" of
          Left err -> assertFailure (show err)
          Right (terms, mLoc) -> do
            map strip terms @?= []
            assertBool "remainder expected" (isJust mLoc),
      testCase "parseLeadingTerms: empty input yields empty list, no remainder" $
        case parseLeadingTerms emptyOps "" "" of
          Left err -> assertFailure (show err)
          Right (terms, mLoc) -> do
            terms @?= []
            assertBool "no remainder expected" (isNothing mLoc),
      testCase "parseLeadingTerms: remainder location is after the consumed prefix" $
        case parseLeadingTerms emptyOps "<src>" "foo.\n???" of
          Left err -> assertFailure (show err)
          Right (_, Just loc) -> do
            -- The remainder starts on line 2 (after the newline following 'foo.').
            loc.line @?= 2
            loc.file @?= "<src>"
          Right (_, Nothing) -> assertFailure "expected remainder location"
    ]

-- ---------------------------------------------------------------------------
-- renderAtom
-- ---------------------------------------------------------------------------

renderAtomTests :: TestTree
renderAtomTests =
  testGroup
    "renderAtom"
    [ testCase "plain lowercase unquoted" $
        renderAtom mempty "foo" @?= "foo",
      testCase "uppercase start quoted" $
        renderAtom mempty "Foo" @?= "'Foo'",
      testCase "empty atom quoted" $
        renderAtom mempty "" @?= "''",
      testCase "embedded apostrophe doubled inside quotes" $
        renderAtom mempty "it's" @?= "'it''s'",
      testCase "word operator must be quoted" $
        -- 'is' is a word operator in testOps; it must be quoted to disambiguate.
        renderAtom testOps.wordOpSet "is" @?= "'is'",
      testCase "double underscore forces quoting" $
        renderAtom mempty "foo__bar" @?= "'foo__bar'",
      testCase "symbol-only name forces quoting" $
        renderAtom mempty "+" @?= "'+'"
    ]

-- ---------------------------------------------------------------------------
-- Float and postfix pretty-printing
-- ---------------------------------------------------------------------------

floatAndPostfixPrettyTests :: TestTree
floatAndPostfixPrettyTests =
  testGroup
    "pretty-printing: floats and postfix"
    [ testCase "positive float" $
        pp (Float 3.14) @?= "3.14",
      testCase "negative float wraps in parens" $
        pp (Float (-2.5)) @?= "(-2.5)",
      testCase "whole-valued float keeps '.0'" $
        pp (Float 1.0) @?= "1.0",
      testCase "zero float" $
        pp (Float 0.0) @?= "0.0",
      testCase "Xf postfix" $
        prettyPExpr postfixOps (Compound "!" [noAnn (Var "X")])
          @?= "X !",
      testCase "Yf postfix chains without parens" $
        prettyPExpr
          postfixOps
          (Compound "++" [noAnn (Compound "++" [noAnn (Var "X")])])
          @?= "X ++ ++",
      testCase "Fy prefix chains without parens" $
        prettyPExpr
          prefixChainOps
          (Compound "-" [noAnn (Compound "-" [noAnn (Var "X")])])
          @?= "- - X",
      testCase "lambda pretty-prints with intercalated params" $
        pp
          ( Compound
              "->"
              [ noAnn (Compound "fun" [noAnn (Var "X"), noAnn (Var "Y")]),
                noAnn (Var "X")
              ]
          )
          @?= "fun(X, Y) -> X end"
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
      testCase "string with escapes" $
        roundtrip emptyOps "string escapes" (Str "say \"hi\"\n\\"),
      testCase "compound" $
        roundtrip emptyOps "compound" (Compound "f" [noAnn (Var "X"), noAnn (Atom "a")]),
      testCase "nested compound" $
        roundtrip emptyOps "nested" (Compound "f" [noAnn (Compound "g" [noAnn (Atom "a")])]),
      testCase "zero-arg compound" $
        roundtrip emptyOps "zero-arg" (Compound "f" []),
      testCase "list" $
        roundtrip emptyOps "list" $
          Compound
            "."
            [ noAnn (Atom "a"),
              noAnn
                ( Compound
                    "."
                    [ noAnn (Atom "b"),
                      noAnn (Atom "[]")
                    ]
                )
            ],
      testCase "list with tail" $
        roundtrip emptyOps "list with tail" $
          Compound "." [noAnn (Atom "a"), noAnn (Var "T")],
      testCase "infix operator" $
        roundtrip testOps "infix" (Compound "+" [noAnn (Var "X"), noAnn (Var "Y")]),
      testCase "nested operators" $
        roundtrip testOps "nested ops" $
          Compound
            "+"
            [ noAnn (Var "X"),
              noAnn
                ( Compound
                    "*"
                    [ noAnn (Var "Y"),
                      noAnn (Var "Z")
                    ]
                )
            ],
      testCase "parens needed" $
        roundtrip testOps "parens" $
          Compound
            "*"
            [ noAnn (Compound "+" [noAnn (Var "X"), noAnn (Var "Y")]),
              noAnn (Var "Z")
            ],
      testCase "left assoc" $
        roundtrip testOps "left assoc" $
          Compound
            "+"
            [ noAnn (Compound "+" [noAnn (Var "X"), noAnn (Var "Y")]),
              noAnn (Var "Z")
            ],
      testCase "right grouping" $
        roundtrip testOps "right grouping" $
          Compound
            "+"
            [ noAnn (Var "X"),
              noAnn
                ( Compound
                    "+"
                    [ noAnn (Var "Y"),
                      noAnn (Var "Z")
                    ]
                )
            ],
      testCase "prefix operator" $
        roundtrip testOps "prefix" (Compound "~" [noAnn (Var "X")]),
      testCase "word operator" $
        roundtrip testOps "word op" (Compound "is" [noAnn (Var "X"), noAnn (Var "Y")]),
      testCase "quoted functor" $
        roundtrip emptyOps "quoted functor" (Compound "Hello" [noAnn (Var "X")]),
      testCase "word op as 3-arg functor" $
        roundtrip
          testOps
          "word op 3-arg"
          ( Compound
              "is"
              [ noAnn (Var "X"),
                noAnn (Var "Y"),
                noAnn (Var "Z")
              ]
          ),
      testCase "empty list" $
        roundtrip emptyOps "empty list" (Atom "[]")
    ]
