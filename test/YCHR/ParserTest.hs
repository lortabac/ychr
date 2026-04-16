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
import YCHR.Parser (ModuleHeader (..), collectModuleHeader, parseModule)
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
      typeTests,
      moduleTests,
      commentTests,
      errorTests,
      firstPassTests
    ]

-- | Parse a source string with no filename.
p :: Text -> Either (ParseErrorBundle Text Void) Module
p = parseModule ""

-- | Strip source locations from a Rule for structural comparison.
stripRuleLoc :: Rule -> Rule
stripRuleLoc r =
  r
    { name = fmap (noAnn . (.node)) r.name,
      head = noAnnP r.head.node,
      guard = noAnnP r.guard.node,
      body = noAnnP r.body.node
    }

-- | Strip source locations from a Module for structural comparison.
stripModLoc :: Module -> Module
stripModLoc m =
  m
    { imports = map (noAnnP . (.node)) m.imports,
      decls = map (noAnn . (.node)) m.decls,
      typeDecls = map (noAnn . (.node)) m.typeDecls,
      rules = map stripRuleLoc m.rules,
      equations = map (noAnnP . (.node)) m.equations,
      exports = fmap (noAnnP . (.node)) m.exports
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
        fmap (.node) . (.exports) <$> p ":- module(order, [])." @?= Right (Just []),
      testCase "export list parsed correctly" $
        fmap (.node) . (.exports) <$> p ":- module(order, [leq/2, foo/1])."
          @?= Right (Just [ConstraintDecl "leq" 2 Nothing, ConstraintDecl "foo" 1 Nothing]),
      testCase "use_module" $
        (map (.node) . (.imports)) <$> p ":- use_module(stdlib)." @?= Right [ModuleImport "stdlib" Nothing],
      testCase "multiple use_module" $
        (map (.node) . (.imports))
          <$> p ":- use_module(stdlib).\n:- use_module(lists)."
          @?= Right [ModuleImport "stdlib" Nothing, ModuleImport "lists" Nothing],
      testCase "use_module library" $
        (map (.node) . (.imports)) <$> p ":- use_module(library(mylib))." @?= Right [LibraryImport "mylib" Nothing],
      testCase "use_module with import list" $
        (map (.node) . (.imports)) <$> p ":- use_module(order, [leq/2])."
          @?= Right [ModuleImport "order" (Just [ConstraintDecl "leq" 2 Nothing])],
      testCase "use_module library with import list" $
        (map (.node) . (.imports)) <$> p ":- use_module(library(mylib), [foo/1, type(tree/0)])."
          @?= Right [LibraryImport "mylib" (Just [ConstraintDecl "foo" 1 Nothing, TypeExportDecl "tree" 0])],
      testCase "chr_constraint single" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint leq/2."
          @?= Right [ConstraintDecl "leq" 2 Nothing],
      testCase "chr_constraint multiple in one directive" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint fib/2, upto/1."
          @?= Right [ConstraintDecl "fib" 2 Nothing, ConstraintDecl "upto" 1 Nothing],
      testCase "chr_constraint zero arity" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint fire/0."
          @?= Right [ConstraintDecl "fire" 0 Nothing],
      testCase "type export in export list" $
        fmap (.node) . (.exports) <$> p ":- module(m, [type(tree/0), leq/2])."
          @?= Right (Just [TypeExportDecl "tree" 0, ConstraintDecl "leq" 2 Nothing]),
      testCase "parameterized type export" $
        fmap (.node) . (.exports) <$> p ":- module(m, [type(list/1)])."
          @?= Right (Just [TypeExportDecl "list" 1]),
      testCase "unknown directive is skipped" $
        (map (.node) . (.decls)) <$> p ":- dynamic foo/1.\n:- chr_constraint leq/2."
          @?= Right [ConstraintDecl "leq" 2 Nothing],
      testCase "chr_constraint typed" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint leq(int, int)."
          @?= Right [ConstraintDecl "leq" 2 (Just [TypeCon (Unqualified "int") [], TypeCon (Unqualified "int") []])],
      testCase "chr_constraint typed with type variables" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint foo(list(T), T)."
          @?= Right
            [ ConstraintDecl
                "foo"
                2
                (Just [TypeCon (Unqualified "list") [TypeVar "T"], TypeVar "T"])
            ],
      testCase "chr_constraint typed zero arity" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint fire()."
          @?= Right [ConstraintDecl "fire" 0 (Just [])],
      testCase "function typed" $
        (map (.node) . (.decls)) <$> p ":- function factorial(int) -> int."
          @?= Right
            [ FunctionDecl
                "factorial"
                1
                (Just [TypeCon (Unqualified "int") []])
                (Just (TypeCon (Unqualified "int") []))
            ],
      testCase "function typed multiple args" $
        (map (.node) . (.decls)) <$> p ":- function add(int, int) -> int."
          @?= Right
            [ FunctionDecl
                "add"
                2
                (Just [TypeCon (Unqualified "int") [], TypeCon (Unqualified "int") []])
                (Just (TypeCon (Unqualified "int") []))
            ],
      testCase "function untyped" $
        (map (.node) . (.decls)) <$> p ":- function foo/2."
          @?= Right [FunctionDecl "foo" 2 Nothing Nothing]
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
          >>= (@?= [CompoundTerm (Qualified "host" "done") []]),
      testCase "is operator used as functor" $
        bodyOf "c <=> is(X, Y)."
          >>= (@?= [CompoundTerm (Unqualified "is") [VarTerm "X", VarTerm "Y"]]),
      testCase "= operator used as functor" $
        bodyOf "c <=> '='(X, Y)."
          >>= (@?= [CompoundTerm (Unqualified "=") [VarTerm "X", VarTerm "Y"]])
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
                (noAnnP (Simplification [Constraint (Unqualified "leq") [VarTerm "X", VarTerm "X"]]))
                (noAnnP [])
                (noAnnP [AtomTerm "true"])
            ],
      testCase "unnamed simplification" $
        (map stripRuleLoc . (.rules)) <$> p "leq(X, X) <=> true."
          @?= Right
            [ Rule
                Nothing
                (noAnnP (Simplification [Constraint (Unqualified "leq") [VarTerm "X", VarTerm "X"]]))
                (noAnnP [])
                (noAnnP [AtomTerm "true"])
            ],
      testCase "propagation" $
        (map stripRuleLoc . (.rules)) <$> p "trans @ leq(X, Y), leq(Y, Z) ==> leq(X, Z)."
          @?= Right
            [ Rule
                (Just (noAnn "trans"))
                ( noAnnP
                    ( Propagation
                        [ Constraint (Unqualified "leq") [VarTerm "X", VarTerm "Y"],
                          Constraint (Unqualified "leq") [VarTerm "Y", VarTerm "Z"]
                        ]
                    )
                )
                (noAnnP [])
                (noAnnP [CompoundTerm (Unqualified "leq") [VarTerm "X", VarTerm "Z"]])
            ],
      testCase "simpagation" $
        (map stripRuleLoc . (.rules)) <$> p "s @ kept \\ removed <=> body."
          @?= Right
            [ Rule
                (Just (noAnn "s"))
                ( noAnnP
                    ( Simpagation
                        [Constraint (Unqualified "kept") []]
                        [Constraint (Unqualified "removed") []]
                    )
                )
                (noAnnP [])
                (noAnnP [AtomTerm "body"])
            ],
      testCase "rule with guard" $
        (map stripRuleLoc . (.rules)) <$> p "r @ c(X, Y) <=> g(X) | b(Y)."
          @?= Right
            [ Rule
                (Just (noAnn "r"))
                (noAnnP (Simplification [Constraint (Unqualified "c") [VarTerm "X", VarTerm "Y"]]))
                (noAnnP [CompoundTerm (Unqualified "g") [VarTerm "X"]])
                (noAnnP [CompoundTerm (Unqualified "b") [VarTerm "Y"]])
            ],
      testCase "multiple body goals" $
        bodyOf "c <=> a, b, c2."
          >>= (@?= [AtomTerm "a", AtomTerm "b", AtomTerm "c2"]),
      testCase "zero-arity constraint in head" $
        headOf "fire <=> true."
          >>= (@?= Simplification [Constraint (Unqualified "fire") []])
    ]

-- ---------------------------------------------------------------------------
-- Type declarations
-- ---------------------------------------------------------------------------

typeTests :: TestTree
typeTests =
  testGroup
    "type declarations"
    [ testCase "simple enum type" $
        typeDefsOf ":- chr_type color ---> red ; green ; blue."
          >>= ( @?=
                  [ TypeDefinition (Unqualified "color") [] $
                      [ DataConstructor (Unqualified "red") [],
                        DataConstructor (Unqualified "green") [],
                        DataConstructor (Unqualified "blue") []
                      ]
                  ]
              ),
      testCase "type with constructor args" $
        typeDefsOf ":- chr_type tree ---> empty ; leaf(int) ; branch(tree, tree)."
          >>= ( @?=
                  [ TypeDefinition (Unqualified "tree") [] $
                      [ DataConstructor (Unqualified "empty") [],
                        DataConstructor (Unqualified "leaf") [TypeCon (Unqualified "int") []],
                        DataConstructor (Unqualified "branch") [TypeCon (Unqualified "tree") [], TypeCon (Unqualified "tree") []]
                      ]
                  ]
              ),
      testCase "parameterized type" $
        typeDefsOf ":- chr_type pair(A, B) ---> pair(A, B)."
          >>= ( @?=
                  [ TypeDefinition (Unqualified "pair") ["A", "B"] $
                      [ DataConstructor (Unqualified "pair") [TypeVar "A", TypeVar "B"]
                      ]
                  ]
              ),
      testCase "list type with list sugar" $
        typeDefsOf ":- chr_type list(T) ---> [] ; [T | list(T)]."
          >>= ( @?=
                  [ TypeDefinition (Unqualified "list") ["T"] $
                      [ DataConstructor (Unqualified "[]") [],
                        DataConstructor (Unqualified ".") [TypeVar "T", TypeCon (Unqualified "list") [TypeVar "T"]]
                      ]
                  ]
              ),
      testCase "type with nested type args" $
        typeDefsOf ":- chr_type nested ---> wrap(pair(int, int))."
          >>= ( @?=
                  [ TypeDefinition (Unqualified "nested") [] $
                      [ DataConstructor (Unqualified "wrap") [TypeCon (Unqualified "pair") [TypeCon (Unqualified "int") [], TypeCon (Unqualified "int") []]]
                      ]
                  ]
              ),
      testCase "type decl doesn't affect constraint decls" $
        case p ":- chr_type t ---> a.\n:- chr_constraint c/1." of
          Left err -> assertFailure (show err)
          Right m -> do
            map (.node) m.decls @?= [ConstraintDecl "c" 1 Nothing]
            map (.node) m.typeDecls
              @?= [TypeDefinition (Unqualified "t") [] [DataConstructor (Unqualified "a") []]],
      testCase "multiple type decls" $
        typeDefsOf ":- chr_type a ---> x.\n:- chr_type b ---> y."
          >>= ( @?=
                  [ TypeDefinition (Unqualified "a") [] [DataConstructor (Unqualified "x") []],
                    TypeDefinition (Unqualified "b") [] [DataConstructor (Unqualified "y") []]
                  ]
              )
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
                [noAnn (ConstraintDecl "leq" 2 Nothing)]
                []
                [ Rule
                    (Just (noAnn "refl"))
                    (noAnnP (Simplification [Constraint (Unqualified "leq") [VarTerm "X", VarTerm "X"]]))
                    (noAnnP [])
                    (noAnnP [AtomTerm "true"]),
                  Rule
                    (Just (noAnn "antisymmetry"))
                    ( noAnnP
                        ( Simplification
                            [ Constraint (Unqualified "leq") [VarTerm "X", VarTerm "Y"],
                              Constraint (Unqualified "leq") [VarTerm "Y", VarTerm "X"]
                            ]
                        )
                    )
                    (noAnnP [])
                    (noAnnP [CompoundTerm (Unqualified "leq") [VarTerm "X", VarTerm "Y"]]),
                  Rule
                    (Just (noAnn "trans"))
                    ( noAnnP
                        ( Propagation
                            [ Constraint (Unqualified "leq") [VarTerm "X", VarTerm "Y"],
                              Constraint (Unqualified "leq") [VarTerm "Y", VarTerm "Z"]
                            ]
                        )
                    )
                    (noAnnP [])
                    (noAnnP [CompoundTerm (Unqualified "leq") [VarTerm "X", VarTerm "Z"]])
                ]
                []
                (Just (noAnnP []))
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
          @?= Right [Rule Nothing (noAnnP (Simplification [Constraint (Unqualified "foo") []])) (noAnnP []) (noAnnP [AtomTerm "bar"])],
      testCase "inline comment after rule" $
        (map stripRuleLoc . (.rules)) <$> p "foo <=> bar. % comment"
          @?= Right [Rule Nothing (noAnnP (Simplification [Constraint (Unqualified "foo") []])) (noAnnP []) (noAnnP [AtomTerm "bar"])],
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
        assertBool "expected parse failure" (isLeft (p "!foo <=> bar.")),
      testCase "double underscore in unquoted atom is rejected" $
        assertBool "expected parse failure" (isLeft (p "foo__bar <=> true.")),
      testCase "double underscore in quoted atom is rejected" $
        assertBool "expected parse failure" (isLeft (p "'foo__bar' <=> true.")),
      testCase "double underscore in module name is rejected" $
        assertBool "expected parse failure" (isLeft (p ":- module(my__mod, []).")),
      testCase "single underscore in atom is allowed" $
        assertBool "expected parse success" (not (isLeft (p "foo_bar <=> true.")))
    ]

-- ---------------------------------------------------------------------------
-- First-pass module-header collector
-- ---------------------------------------------------------------------------

-- | Helper: collect operators from a module header.
ops :: Text -> Either (ParseErrorBundle Text Void) [OpDecl]
ops src = (.exportOps) <$> collectModuleHeader "" src

-- | Helper: collect imports from a module header.
hdrImports :: Text -> Either (ParseErrorBundle Text Void) [Import]
hdrImports src = map (.node) . (.headerImports) <$> collectModuleHeader "" src

firstPassTests :: TestTree
firstPassTests =
  testGroup
    "first-pass module-header collector"
    [ testCase "extracts operators from export list" $
        ops ":- module(m, [op(500, yfx, '+')])." @?= Right [OpDecl 500 Yfx "+"],
      testCase "skips name/arity entries" $
        ops ":- module(m, [leq/2, op(700, xfx, '<')])." @?= Right [OpDecl 700 Xfx "<"],
      testCase "skips type exports" $
        ops ":- module(m, [type(bool/0), op(500, yfx, '+')])." @?= Right [OpDecl 500 Yfx "+"],
      testCase "type export among many entries" $
        ops ":- module(m, [leq/2, type(tree/0), op(400, yfx, '*'), type(list/1)])." @?= Right [OpDecl 400 Yfx "*"],
      testCase "no module directive returns empty exports" $
        ops ":- chr_constraint leq/2." @?= Right [],
      testCase "empty export list returns empty" $
        ops ":- module(m, [])." @?= Right [],
      testCase "collects use_module imports right after the module directive" $
        hdrImports ":- module(m, []). :- use_module(foo). :- use_module(library(bar))."
          @?= Right [ModuleImport "foo" Nothing, LibraryImport "bar" Nothing],
      testCase "stops collecting imports at the first non-import directive" $
        hdrImports ":- module(m, []). :- use_module(foo). :- chr_constraint c/1. :- use_module(bar)."
          @?= Right [ModuleImport "foo" Nothing],
      testCase "import lists with op() entries parse" $
        hdrImports ":- module(m, []). :- use_module(foo, [op(700, xfx, '<-')])."
          @?= Right [ModuleImport "foo" (Just [OperatorDecl (OpDecl 700 Xfx "<-")])]
    ]

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

typeDefsOf :: Text -> IO [TypeDefinition]
typeDefsOf src = case p src of
  Left err -> assertFailure (show err)
  Right m -> pure (map (.node) m.typeDecls)

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
