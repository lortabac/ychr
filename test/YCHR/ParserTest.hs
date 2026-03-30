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

-- | Strip source locations from a Rule for structural comparison.
stripRuleLoc :: Rule -> Rule
stripRuleLoc r =
  r
    { name = fmap (noAnn . (.node)) r.name,
      head = noAnn r.head.node,
      guard = noAnn r.guard.node,
      body = noAnn r.body.node
    }

-- | Strip source locations from a Module for structural comparison.
stripModLoc :: Module -> Module
stripModLoc m =
  m
    { imports = map (noAnn . (.node)) m.imports,
      decls = map (noAnn . (.node)) m.decls,
      rules = map stripRuleLoc m.rules,
      equations = map (noAnn . (.node)) m.equations
    }

-- ---------------------------------------------------------------------------
-- Directives
-- ---------------------------------------------------------------------------

directiveTests :: TestTree
directiveTests =
  testGroup
    "directives"
    [ testCase "module name" $
        (.name) <$> p ":- module(order, [])." @?= Right "order",
      testCase "module name with export list" $
        (.name) <$> p ":- module(order, [leq/2, foo/1])." @?= Right "order",
      testCase "empty export list" $
        (.exports) <$> p ":- module(order, [])." @?= Right (Just []),
      testCase "export list parsed correctly" $
        (.exports) <$> p ":- module(order, [leq/2, foo/1])."
          @?= Right (Just [ConstraintDecl "leq" 2, ConstraintDecl "foo" 1]),
      testCase "use_module" $
        (map (.node) . (.imports)) <$> p ":- use_module(stdlib)." @?= Right [ModuleImport "stdlib"],
      testCase "multiple use_module" $
        (map (.node) . (.imports))
          <$> p ":- use_module(stdlib).\n:- use_module(lists)."
          @?= Right [ModuleImport "stdlib", ModuleImport "lists"],
      testCase "use_module library" $
        (map (.node) . (.imports)) <$> p ":- use_module(library(mylib))." @?= Right [LibraryImport "mylib"],
      testCase "chr_constraint single" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint leq/2."
          @?= Right [ConstraintDecl "leq" 2],
      testCase "chr_constraint multiple in one directive" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint fib/2, upto/1."
          @?= Right [ConstraintDecl "fib" 2, ConstraintDecl "upto" 1],
      testCase "chr_constraint zero arity" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint fire/0."
          @?= Right [ConstraintDecl "fire" 0],
      testCase "unknown directive is skipped" $
        (map (.node) . (.decls)) <$> p ":- dynamic foo/1.\n:- chr_constraint leq/2."
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
        guardOf "r @ c(X) <=> host:'>='(X, -1) | true."
          >>= (@?= [CompoundTerm (Qualified "host" ">=") [VarTerm "X", IntTerm (-1)]]),
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
    [ testCase "unification operator" $
        bodyOf "c <=> X = Y."
          >>= (@?= [CompoundTerm (Unqualified "=") [VarTerm "X", VarTerm "Y"]]),
      testCase "is operator with arithmetic" $
        bodyOf "c <=> N is host:'+'(X, 1)."
          >>= ( @?=
                  [ CompoundTerm
                      (Unqualified "is")
                      [VarTerm "N", CompoundTerm (Qualified "host" "+") [VarTerm "X", IntTerm 1]]
                  ]
              ),
      testCase "qualified name in term" $
        bodyOf "c <=> host:print(X)."
          >>= (@?= [CompoundTerm (Qualified "host" "print") [VarTerm "X"]]),
      testCase "zero-arity qualified name" $
        bodyOf "c <=> host:done."
          >>= (@?= [CompoundTerm (Qualified "host" "done") []])
    ]

-- ---------------------------------------------------------------------------
-- Rules
-- ---------------------------------------------------------------------------

ruleTests :: TestTree
ruleTests =
  testGroup
    "rules"
    [ testCase "named simplification" $
        (map stripRuleLoc . (.rules)) <$> p "refl @ leq(X, X) <=> true."
          @?= Right
            [ Rule
                (Just (noAnn "refl"))
                (noAnn (Simplification [Constraint (Unqualified "leq") [VarTerm "X", VarTerm "X"]]))
                (noAnn [])
                (noAnn [AtomTerm "true"])
            ],
      testCase "unnamed simplification" $
        (map stripRuleLoc . (.rules)) <$> p "leq(X, X) <=> true."
          @?= Right
            [ Rule
                Nothing
                (noAnn (Simplification [Constraint (Unqualified "leq") [VarTerm "X", VarTerm "X"]]))
                (noAnn [])
                (noAnn [AtomTerm "true"])
            ],
      testCase "propagation" $
        (map stripRuleLoc . (.rules)) <$> p "trans @ leq(X, Y), leq(Y, Z) ==> leq(X, Z)."
          @?= Right
            [ Rule
                (Just (noAnn "trans"))
                ( noAnn
                    ( Propagation
                        [ Constraint (Unqualified "leq") [VarTerm "X", VarTerm "Y"],
                          Constraint (Unqualified "leq") [VarTerm "Y", VarTerm "Z"]
                        ]
                    )
                )
                (noAnn [])
                (noAnn [CompoundTerm (Unqualified "leq") [VarTerm "X", VarTerm "Z"]])
            ],
      testCase "simpagation" $
        (map stripRuleLoc . (.rules)) <$> p "s @ kept \\ removed <=> body."
          @?= Right
            [ Rule
                (Just (noAnn "s"))
                ( noAnn
                    ( Simpagation
                        [Constraint (Unqualified "kept") []]
                        [Constraint (Unqualified "removed") []]
                    )
                )
                (noAnn [])
                (noAnn [AtomTerm "body"])
            ],
      testCase "rule with guard" $
        (map stripRuleLoc . (.rules)) <$> p "r @ c(X, Y) <=> g(X) | b(Y)."
          @?= Right
            [ Rule
                (Just (noAnn "r"))
                (noAnn (Simplification [Constraint (Unqualified "c") [VarTerm "X", VarTerm "Y"]]))
                (noAnn [CompoundTerm (Unqualified "g") [VarTerm "X"]])
                (noAnn [CompoundTerm (Unqualified "b") [VarTerm "Y"]])
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
        stripModLoc <$> p leqSource
          @?= Right
            ( Module
                "order"
                []
                [noAnn (ConstraintDecl "leq" 2)]
                [ Rule
                    (Just (noAnn "refl"))
                    (noAnn (Simplification [Constraint (Unqualified "leq") [VarTerm "X", VarTerm "X"]]))
                    (noAnn [])
                    (noAnn [AtomTerm "true"]),
                  Rule
                    (Just (noAnn "antisymmetry"))
                    ( noAnn
                        ( Simplification
                            [ Constraint (Unqualified "leq") [VarTerm "X", VarTerm "Y"],
                              Constraint (Unqualified "leq") [VarTerm "Y", VarTerm "X"]
                            ]
                        )
                    )
                    (noAnn [])
                    (noAnn [CompoundTerm (Unqualified "leq") [VarTerm "X", VarTerm "Y"]]),
                  Rule
                    (Just (noAnn "trans"))
                    ( noAnn
                        ( Propagation
                            [ Constraint (Unqualified "leq") [VarTerm "X", VarTerm "Y"],
                              Constraint (Unqualified "leq") [VarTerm "Y", VarTerm "Z"]
                            ]
                        )
                    )
                    (noAnn [])
                    (noAnn [CompoundTerm (Unqualified "leq") [VarTerm "X", VarTerm "Z"]])
                ]
                []
                (Just [])
            ),
      testCase "no module directive gives default name" $
        (.name) <$> p ":- chr_constraint foo/1.\nfoo(X) <=> true."
          @?= Right "<no_module>"
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
        (map stripRuleLoc . (.rules)) <$> p "% a comment\nfoo <=> bar."
          @?= Right [Rule Nothing (noAnn (Simplification [Constraint (Unqualified "foo") []])) (noAnn []) (noAnn [AtomTerm "bar"])],
      testCase "inline comment after rule" $
        (map stripRuleLoc . (.rules)) <$> p "foo <=> bar. % comment"
          @?= Right [Rule Nothing (noAnn (Simplification [Constraint (Unqualified "foo") []])) (noAnn []) (noAnn [AtomTerm "bar"])],
      testCase "only comments parses to empty module" $
        (.rules) <$> p "% just a comment\n% another"
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
  Right m -> case m.rules of
    [] -> assertFailure "expected at least one rule, got none"
    (r : _) -> pure r.body.node

headOf :: Text -> IO Head
headOf src = case p src of
  Left err -> assertFailure (show err)
  Right m -> case m.rules of
    [] -> assertFailure "expected at least one rule, got none"
    (r : _) -> pure r.head.node

guardOf :: Text -> IO [Term]
guardOf src = case p src of
  Left err -> assertFailure (show err)
  Right m -> case m.rules of
    [] -> assertFailure "expected at least one rule, got none"
    (r : _) -> pure r.guard.node
