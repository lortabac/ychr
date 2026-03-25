{-# LANGUAGE OverloadedStrings #-}

module YCHR.ParserTest (tests) where

import Data.Either (isLeft)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Void (Void)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import Text.Megaparsec (ParseErrorBundle)
import YCHR.Parsed
import YCHR.Parser (parseModule)
import YCHR.Types

tests :: TestTree
tests =
  testGroup
    "YCHR.Parser"
    [ directiveTests,
      termTests,
      negativeIntTests,
      operatorTests,
      ruleTests,
      moduleTests,
      commentTests,
      errorTests
    ]

-- | Parse a source string with no filename.
p :: Text -> Either (ParseErrorBundle Text Void) Module
p = parseModule ""

-- ---------------------------------------------------------------------------
-- Directives
-- ---------------------------------------------------------------------------

directiveTests :: TestTree
directiveTests =
  testGroup
    "directives"
    [ testCase "module name" $
        modName <$> p ":- module(order, [])." @?= Right "order",
      testCase "module name with export list" $
        modName <$> p ":- module(order, [leq/2, foo/1])." @?= Right "order",
      testCase "empty export list" $
        modExports <$> p ":- module(order, [])." @?= Right (Just []),
      testCase "export list parsed correctly" $
        modExports <$> p ":- module(order, [leq/2, foo/1])."
          @?= Right (Just [ConstraintDecl "leq" 2, ConstraintDecl "foo" 1]),
      testCase "use_module" $
        modImports <$> p ":- use_module(stdlib)." @?= Right ["stdlib"],
      testCase "multiple use_module" $
        modImports
          <$> p ":- use_module(stdlib).\n:- use_module(lists)."
          @?= Right ["stdlib", "lists"],
      testCase "chr_constraint single" $
        modDecls <$> p ":- chr_constraint leq/2."
          @?= Right [ConstraintDecl "leq" 2],
      testCase "chr_constraint multiple in one directive" $
        modDecls <$> p ":- chr_constraint fib/2, upto/1."
          @?= Right [ConstraintDecl "fib" 2, ConstraintDecl "upto" 1],
      testCase "chr_constraint zero arity" $
        modDecls <$> p ":- chr_constraint fire/0."
          @?= Right [ConstraintDecl "fire" 0],
      testCase "unknown directive is skipped" $
        modDecls <$> p ":- dynamic foo/1.\n:- chr_constraint leq/2."
          @?= Right [ConstraintDecl "leq" 2]
    ]

-- ---------------------------------------------------------------------------
-- Terms (tested via rule bodies)
-- ---------------------------------------------------------------------------

termTests :: TestTree
termTests =
  testGroup
    "terms"
    [ testCase "variable in body" $
        bodyOf "c(X) <=> X." >>= (@?= [VarTerm "X"]),
      testCase "wildcard in head" $
        headOf "c(_) <=> true."
          >>= (@?= Simplification [Constraint (Unqualified "c") [Wildcard]]),
      testCase "integer in body" $
        bodyOf "c <=> f(1)."
          >>= (@?= [CompoundTerm (Unqualified "f") [IntTerm 1]]),
      testCase "bare atom in body" $
        bodyOf "c <=> true." >>= (@?= [AtomTerm "true"]),
      testCase "compound term in body" $
        bodyOf "c(X) <=> f(X, a)."
          >>= (@?= [CompoundTerm (Unqualified "f") [VarTerm "X", AtomTerm "a"]]),
      testCase "quoted atom as functor" $
        bodyOf "c <=> 'hello'."
          >>= (@?= [AtomTerm "hello"]),
      testCase "quoted atom with space" $
        bodyOf "c <=> 'hello world'."
          >>= (@?= [AtomTerm "hello world"]),
      testCase "empty quoted atom" $
        bodyOf "c <=> ''."
          >>= (@?= [AtomTerm ""]),
      testCase "quoted atom with '' escape (ISO Prolog)" $
        bodyOf "c <=> 'it''s'."
          >>= (@?= [AtomTerm "it's"]),
      testCase "quoted atom with \\' escape (SWI-Prolog)" $
        bodyOf "c <=> 'a\\'b'."
          >>= (@?= [AtomTerm "a'b"]),
      testCase "quoted atom with \\\\ escape" $
        bodyOf "c <=> 'back\\\\slash'."
          >>= (@?= [AtomTerm "back\\slash"]),
      testCase "zero-arity compound via quoted atom" $
        bodyOf "c <=> 'foo'(X, 1)."
          >>= (@?= [CompoundTerm (Unqualified "foo") [VarTerm "X", IntTerm 1]]),
      testCase "nested compound" $
        bodyOf "c <=> f(g(X))."
          >>= (@?= [CompoundTerm (Unqualified "f") [CompoundTerm (Unqualified "g") [VarTerm "X"]]])
    ]

-- ---------------------------------------------------------------------------
-- Negative integer literals
-- ---------------------------------------------------------------------------

negativeIntTests :: TestTree
negativeIntTests =
  testGroup
    "negative integer literals"
    [ testCase "negative literal as standalone term" $
        bodyOf "c <=> f(-5)."
          >>= (@?= [CompoundTerm (Unqualified "f") [IntTerm (-5)]]),
      testCase "negative literal as constraint argument" $
        headOf "c(-3, X) <=> true."
          >>= (@?= Simplification [Constraint (Unqualified "c") [IntTerm (-3), VarTerm "X"]]),
      testCase "negative literal in guard" $
        guardOf "r @ c(X) <=> X >= -1 | true."
          >>= (@?= [CompoundTerm (Unqualified ">=") [VarTerm "X", IntTerm (-1)]]),
      testCase "binary minus with negative literal on right" $
        bodyOf "c <=> 3 - -5."
          >>= ( @?=
                  [ CompoundTerm
                      (Unqualified "-")
                      [IntTerm 3, IntTerm (-5)]
                  ]
              ),
      testCase "negative zero" $
        bodyOf "c <=> f(-0)."
          >>= (@?= [CompoundTerm (Unqualified "f") [IntTerm 0]])
    ]

-- ---------------------------------------------------------------------------
-- Operator expressions
-- ---------------------------------------------------------------------------

operatorTests :: TestTree
operatorTests =
  testGroup
    "operator expressions"
    [ -- Arithmetic precedence and associativity
      testCase "multiplication binds tighter than addition" $
        bodyOf "c <=> 1 + 2 * 3."
          >>= ( @?=
                  [ CompoundTerm
                      (Unqualified "+")
                      [IntTerm 1, CompoundTerm (Unqualified "*") [IntTerm 2, IntTerm 3]]
                  ]
              ),
      testCase "subtraction is left-associative" $
        bodyOf "c <=> 1 - 2 - 3."
          >>= ( @?=
                  [ CompoundTerm
                      (Unqualified "-")
                      [CompoundTerm (Unqualified "-") [IntTerm 1, IntTerm 2], IntTerm 3]
                  ]
              ),
      testCase "parentheses override precedence" $
        bodyOf "c <=> (1 + 2) * 3."
          >>= ( @?=
                  [ CompoundTerm
                      (Unqualified "*")
                      [CompoundTerm (Unqualified "+") [IntTerm 1, IntTerm 2], IntTerm 3]
                  ]
              ),
      -- Comparison operators
      testCase "less-than operator" $
        bodyOf "c <=> X < Y."
          >>= (@?= [CompoundTerm (Unqualified "<") [VarTerm "X", VarTerm "Y"]]),
      testCase "less-than-or-equal operator" $
        bodyOf "c <=> X =< Y."
          >>= (@?= [CompoundTerm (Unqualified "=<") [VarTerm "X", VarTerm "Y"]]),
      testCase "greater-than-or-equal operator" $
        bodyOf "c <=> X >= Y."
          >>= (@?= [CompoundTerm (Unqualified ">=") [VarTerm "X", VarTerm "Y"]]),
      testCase "structural equality operator" $
        bodyOf "c <=> X == Y."
          >>= (@?= [CompoundTerm (Unqualified "==") [VarTerm "X", VarTerm "Y"]]),
      testCase "unification operator" $
        bodyOf "c <=> X = Y."
          >>= (@?= [CompoundTerm (Unqualified "=") [VarTerm "X", VarTerm "Y"]]),
      testCase "greater-than operator" $
        bodyOf "c <=> X > Y."
          >>= (@?= [CompoundTerm (Unqualified ">") [VarTerm "X", VarTerm "Y"]]),
      testCase "assignment operator" $
        bodyOf "c <=> X := Y."
          >>= (@?= [CompoundTerm (Unqualified ":=") [VarTerm "X", VarTerm "Y"]]),
      -- Word operators
      testCase "is operator with arithmetic" $
        bodyOf "c <=> N is X + 1."
          >>= ( @?=
                  [ CompoundTerm
                      (Unqualified "is")
                      [VarTerm "N", CompoundTerm (Unqualified "+") [VarTerm "X", IntTerm 1]]
                  ]
              ),
      testCase "div operator" $
        bodyOf "c <=> X div Y."
          >>= (@?= [CompoundTerm (Unqualified "div") [VarTerm "X", VarTerm "Y"]]),
      testCase "mod operator" $
        bodyOf "c <=> X mod Y."
          >>= (@?= [CompoundTerm (Unqualified "mod") [VarTerm "X", VarTerm "Y"]]),
      testCase "div is left-associative at same precedence as mul" $
        bodyOf "c <=> X div Y * Z."
          >>= ( @?=
                  [ CompoundTerm
                      (Unqualified "*")
                      [CompoundTerm (Unqualified "div") [VarTerm "X", VarTerm "Y"], VarTerm "Z"]
                  ]
              ),
      -- Operators in guard position
      testCase "operator in guard" $
        guardOf "r @ c(X) <=> X > 0 | b(X)."
          >>= (@?= [CompoundTerm (Unqualified ">") [VarTerm "X", IntTerm 0]]),
      -- Operators as compound term arguments
      testCase "operator expressions as arguments" $
        bodyOf "c <=> f(X + 1, Y * 2)."
          >>= ( @?=
                  [ CompoundTerm
                      (Unqualified "f")
                      [ CompoundTerm (Unqualified "+") [VarTerm "X", IntTerm 1],
                        CompoundTerm (Unqualified "*") [VarTerm "Y", IntTerm 2]
                      ]
                  ]
              ),
      -- Non-associativity
      testCase "chained non-associative operator fails" $
        assertBool "expected parse failure" (isLeft (p "c <=> X < Y < Z."))
    ]

-- ---------------------------------------------------------------------------
-- Rules
-- ---------------------------------------------------------------------------

ruleTests :: TestTree
ruleTests =
  testGroup
    "rules"
    [ testCase "named simplification" $
        modRules <$> p "refl @ leq(X, X) <=> true."
          @?= Right
            [ Rule
                (Just "refl")
                (Simplification [Constraint (Unqualified "leq") [VarTerm "X", VarTerm "X"]])
                []
                [AtomTerm "true"]
            ],
      testCase "unnamed simplification" $
        modRules <$> p "leq(X, X) <=> true."
          @?= Right
            [ Rule
                Nothing
                (Simplification [Constraint (Unqualified "leq") [VarTerm "X", VarTerm "X"]])
                []
                [AtomTerm "true"]
            ],
      testCase "propagation" $
        modRules <$> p "trans @ leq(X, Y), leq(Y, Z) ==> leq(X, Z)."
          @?= Right
            [ Rule
                (Just "trans")
                ( Propagation
                    [ Constraint (Unqualified "leq") [VarTerm "X", VarTerm "Y"],
                      Constraint (Unqualified "leq") [VarTerm "Y", VarTerm "Z"]
                    ]
                )
                []
                [CompoundTerm (Unqualified "leq") [VarTerm "X", VarTerm "Z"]]
            ],
      testCase "simpagation" $
        modRules <$> p "s @ kept \\ removed <=> body."
          @?= Right
            [ Rule
                (Just "s")
                ( Simpagation
                    [Constraint (Unqualified "kept") []]
                    [Constraint (Unqualified "removed") []]
                )
                []
                [AtomTerm "body"]
            ],
      testCase "rule with guard" $
        modRules <$> p "r @ c(X, Y) <=> g(X) | b(Y)."
          @?= Right
            [ Rule
                (Just "r")
                (Simplification [Constraint (Unqualified "c") [VarTerm "X", VarTerm "Y"]])
                [CompoundTerm (Unqualified "g") [VarTerm "X"]]
                [CompoundTerm (Unqualified "b") [VarTerm "Y"]]
            ],
      testCase "multiple body goals" $
        bodyOf "c <=> a, b, c2."
          >>= (@?= [AtomTerm "a", AtomTerm "b", AtomTerm "c2"]),
      testCase "zero-arity constraint in head" $
        headOf "fire <=> true."
          >>= (@?= Simplification [Constraint (Unqualified "fire") []])
    ]

-- ---------------------------------------------------------------------------
-- Full module
-- ---------------------------------------------------------------------------

moduleTests :: TestTree
moduleTests =
  testGroup
    "full module"
    [ testCase "leq module" $
        p leqSource
          @?= Right
            ( Module
                "order"
                []
                [ConstraintDecl "leq" 2]
                [ Rule
                    (Just "refl")
                    (Simplification [Constraint (Unqualified "leq") [VarTerm "X", VarTerm "X"]])
                    []
                    [AtomTerm "true"],
                  Rule
                    (Just "antisymmetry")
                    ( Simplification
                        [ Constraint (Unqualified "leq") [VarTerm "X", VarTerm "Y"],
                          Constraint (Unqualified "leq") [VarTerm "Y", VarTerm "X"]
                        ]
                    )
                    []
                    [CompoundTerm (Unqualified "leq") [VarTerm "X", VarTerm "Y"]],
                  Rule
                    (Just "trans")
                    ( Propagation
                        [ Constraint (Unqualified "leq") [VarTerm "X", VarTerm "Y"],
                          Constraint (Unqualified "leq") [VarTerm "Y", VarTerm "Z"]
                        ]
                    )
                    []
                    [CompoundTerm (Unqualified "leq") [VarTerm "X", VarTerm "Z"]]
                ]
                (Just [])
            ),
      testCase "no module directive gives empty name" $
        modName <$> p ":- chr_constraint foo/1.\nfoo(X) <=> true."
          @?= Right ""
    ]

leqSource :: Text
leqSource =
  Text.unlines
    [ ":- module(order, []).",
      ":- chr_constraint leq/2.",
      "",
      "refl @ leq(X, X) <=> true.",
      "antisymmetry @ leq(X, Y), leq(Y, X) <=> leq(X, Y).",
      "trans @ leq(X, Y), leq(Y, Z) ==> leq(X, Z)."
    ]

-- ---------------------------------------------------------------------------
-- Comments
-- ---------------------------------------------------------------------------

commentTests :: TestTree
commentTests =
  testGroup
    "comments"
    [ testCase "line comment before rule" $
        modRules <$> p "% a comment\nfoo <=> bar."
          @?= Right [Rule Nothing (Simplification [Constraint (Unqualified "foo") []]) [] [AtomTerm "bar"]],
      testCase "inline comment after rule" $
        modRules <$> p "foo <=> bar. % comment"
          @?= Right [Rule Nothing (Simplification [Constraint (Unqualified "foo") []]) [] [AtomTerm "bar"]],
      testCase "only comments parses to empty module" $
        modRules <$> p "% just a comment\n% another"
          @?= Right []
    ]

-- ---------------------------------------------------------------------------
-- Errors
-- ---------------------------------------------------------------------------

errorTests :: TestTree
errorTests =
  testGroup
    "errors"
    [ testCase "missing dot returns Left" $
        assertBool "expected parse failure" (isLeft (p "foo <=> bar")),
      testCase "invalid character returns Left" $
        assertBool "expected parse failure" (isLeft (p "!foo <=> bar."))
    ]

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

bodyOf :: Text -> IO [Term]
bodyOf src = case p src of
  Left err -> assertFailure (show err)
  Right m -> case modRules m of
    [] -> assertFailure "expected at least one rule, got none"
    (r : _) -> pure (ruleBody r)

headOf :: Text -> IO Head
headOf src = case p src of
  Left err -> assertFailure (show err)
  Right m -> case modRules m of
    [] -> assertFailure "expected at least one rule, got none"
    (r : _) -> pure (ruleHead r)

guardOf :: Text -> IO [Term]
guardOf src = case p src of
  Left err -> assertFailure (show err)
  Right m -> case modRules m of
    [] -> assertFailure "expected at least one rule, got none"
    (r : _) -> pure (ruleGuard r)
