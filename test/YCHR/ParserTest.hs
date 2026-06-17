{-# LANGUAGE OverloadedStrings #-}

module YCHR.ParserTest (tests) where

import Data.Either (isLeft)
import Data.Text (Text)
import Data.Text qualified as Text
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import Text.Parsec (ParseError)
import YCHR.Parsed
import YCHR.Parser
  ( ModuleHeader (..),
    ParseValidationError (..),
    builtinOps,
    collectModuleHeader,
    mergeOps,
    parseModule,
    parseModuleWith,
  )

tests :: TestTree
tests =
  testGroup
    "YCHR.Parser"
    [ directiveTests,
      termTests,
      negativeIntTests,
      floatLiteralTests,
      operatorTests,
      ruleTests,
      typeTests,
      moduleTests,
      commentTests,
      errorTests,
      firstPassTests
    ]

-- | Parse a source string with no filename.
p :: Text -> Either (ParseError) Module
p src = fst <$> parseModule "" src

-- | Parse and return only the validation errors, with each error's
-- variant extracted (location/origin discarded).
pErrs :: Text -> Either (ParseError) [ParseValidationError]
pErrs src = map (.node) . snd <$> parseModule "" src

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
    { nameLoc = dummyLoc,
      imports = map (noAnnP . (.node)) m.imports,
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
      testCase "duplicate module header is rejected" $ do
        -- The first header wins; each subsequent ':- module(...)' yields
        -- one DuplicateModuleHeader error carrying its own name.
        (.name) <$> p ":- module(a).\n:- module(b).\n:- chr_constraint c/0."
          @?= Right "a"
        pErrs ":- module(a).\n:- module(b).\n:- chr_constraint c/0."
          @?= Right [DuplicateModuleHeader "b"],
      testCase "three module headers report two duplicates" $
        pErrs ":- module(a).\n:- module(b).\n:- module(c)."
          @?= Right [DuplicateModuleHeader "b", DuplicateModuleHeader "c"],
      testCase "empty export list" $
        fmap (.node) . (.exports) <$> p ":- module(order, [])." @?= Right (Just []),
      testCase "export list parsed correctly" $
        fmap (.node) . (.exports) <$> p ":- module(order, [leq/2, foo/1])."
          @?= Right
            ( Just
                [ ConstraintDecl "leq" 2 Nothing Nothing,
                  ConstraintDecl "foo" 1 Nothing Nothing
                ]
            ),
      testCase "use_module" $
        (map (.node) . (.imports))
          <$> p ":- use_module(stdlib)."
          @?= Right [ModuleImport "stdlib" Nothing],
      testCase "multiple use_module" $
        (map (.node) . (.imports))
          <$> p ":- use_module(stdlib).\n:- use_module(lists)."
          @?= Right [ModuleImport "stdlib" Nothing, ModuleImport "lists" Nothing],
      testCase "use_module library" $
        (map (.node) . (.imports))
          <$> p ":- use_module(library(mylib))."
          @?= Right [LibraryImport "mylib" Nothing],
      testCase "use_module with import list" $
        (map (.node) . (.imports)) <$> p ":- use_module(order, [leq/2])."
          @?= Right [ModuleImport "order" (Just [ConstraintDecl "leq" 2 Nothing Nothing])],
      testCase "use_module library with import list" $
        (map (.node) . (.imports))
          <$> p ":- use_module(library(mylib), [foo/1, type(tree/0)])."
          @?= Right
            [ LibraryImport
                "mylib"
                ( Just
                    [ ConstraintDecl "foo" 1 Nothing Nothing,
                      TypeExportDecl "tree" 0 Nothing
                    ]
                )
            ],
      testCase "chr_constraint single" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint leq/2."
          @?= Right [ConstraintDecl "leq" 2 Nothing Nothing],
      testCase "chr_constraint multiple in one directive" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint fib/2, upto/1."
          @?= Right
            [ ConstraintDecl "fib" 2 Nothing Nothing,
              ConstraintDecl "upto" 1 Nothing Nothing
            ],
      testCase "chr_constraint zero arity" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint fire/0."
          @?= Right [ConstraintDecl "fire" 0 Nothing Nothing],
      testCase "type export in export list" $
        fmap (.node) . (.exports) <$> p ":- module(m, [type(tree/0), leq/2])."
          @?= Right
            ( Just
                [TypeExportDecl "tree" 0 Nothing, ConstraintDecl "leq" 2 Nothing Nothing]
            ),
      testCase "parameterized type export" $
        fmap (.node) . (.exports) <$> p ":- module(m, [type(list/1)])."
          @?= Right (Just [TypeExportDecl "list" 1 Nothing]),
      testCase "type export with constructor allowlist" $
        fmap (.node) . (.exports)
          <$> p ":- module(m, [type(foo/0, [bar, baz])])."
          @?= Right (Just [TypeExportDecl "foo" 0 (Just ["bar", "baz"])]),
      testCase "type export with empty constructor list" $
        fmap (.node) . (.exports)
          <$> p ":- module(m, [type(foo/0, [])])."
          @?= Right (Just [TypeExportDecl "foo" 0 (Just [])]),
      testCase "non-list constructor argument is rejected" $ do
        fmap (.node) . (.exports)
          <$> p ":- module(m, [type(foo/0, oops)])."
          @?= Right (Just [])
        pErrs ":- module(m, [type(foo/0, oops)])."
          @?= Right [MalformedExportItem],
      testCase "non-atom in constructor list is rejected" $ do
        -- One non-atom element (Node is a variable) drops the whole
        -- TypeExportDecl and emits one MalformedExportItem per bad
        -- element.
        fmap (.node) . (.exports)
          <$> p ":- module(m, [type(foo/0, [bar, Node])])."
          @?= Right (Just [])
        pErrs ":- module(m, [type(foo/0, [bar, Node])])."
          @?= Right [MalformedExportItem],
      testCase "multiple bad elements report multiple errors" $
        pErrs ":- module(m, [type(foo/0, [X, Y])])."
          @?= Right [MalformedExportItem, MalformedExportItem],
      testCase "unknown directive is skipped" $
        (map (.node) . (.decls)) <$> p ":- mystery_directive(foo).\n:- chr_constraint leq/2."
          @?= Right [ConstraintDecl "leq" 2 Nothing Nothing],
      testCase "chr_constraint typed" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint leq(int, int)."
          @?= Right
            [ ConstraintDecl
                "leq"
                2
                ( Just
                    [ TypeCon (Unqualified "int") [],
                      TypeCon (Unqualified "int") []
                    ]
                )
                Nothing
            ],
      testCase "chr_constraint typed with type variables" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint foo(list(T), T)."
          @?= Right
            [ ConstraintDecl
                "foo"
                2
                (Just [TypeCon (Unqualified "list") [TypeVar "T"], TypeVar "T"])
                Nothing
            ],
      testCase "chr_constraint typed zero arity" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint fire()."
          @?= Right [ConstraintDecl "fire" 0 (Just []) Nothing],
      testCase "function typed" $
        (map (.node) . (.decls)) <$> p ":- function factorial(int) -> int."
          @?= Right
            [ FunctionDecl
                "factorial"
                1
                (Just [TypeCon (Unqualified "int") []])
                (Just (TypeCon (Unqualified "int") []))
                False
                DKFunction
                Nothing
            ],
      testCase "function typed multiple args" $
        (map (.node) . (.decls)) <$> p ":- function add(int, int) -> int."
          @?= Right
            [ FunctionDecl
                "add"
                2
                (Just [TypeCon (Unqualified "int") [], TypeCon (Unqualified "int") []])
                (Just (TypeCon (Unqualified "int") []))
                False
                DKFunction
                Nothing
            ],
      testCase "function untyped" $
        (map (.node) . (.decls)) <$> p ":- function foo/2."
          @?= Right [FunctionDecl "foo" 2 Nothing Nothing False DKFunction Nothing]
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
      testCase "underscore-prefixed variable in body" $
        bodyOf "c(X) <=> _X." >>= (@?= [VarTerm "_X"]),
      testCase "underscore-prefixed variable in head" $
        headOf "c(_X) <=> true."
          >>= (@?= Simplification [Constraint (Unqualified "c") [VarTerm "_X"]]),
      testCase "underscore-prefixed variable as list tail" $
        bodyOf "c <=> f([H | _Tail])."
          >>= ( @?=
                  [ CompoundTerm
                      (Unqualified "f")
                      [CompoundTerm (Unqualified ".") [VarTerm "H", VarTerm "_Tail"]]
                  ]
              ),
      testCase "double-underscore variable" $
        bodyOf "c <=> __Foo." >>= (@?= [VarTerm "__Foo"]),
      testCase "integer in body" $
        bodyOf "c <=> f(1)."
          >>= (@?= [CompoundTerm (Unqualified "f") [IntTerm 1]]),
      testCase "bare atom in body" $
        bodyOf "c <=> true." >>= (@?= [CompoundTerm (Unqualified "true") []]),
      testCase "compound term in body" $
        bodyOf "c(X) <=> f(X, a)."
          >>= ( @?=
                  [ CompoundTerm
                      (Unqualified "f")
                      [VarTerm "X", CompoundTerm (Unqualified "a") []]
                  ]
              ),
      testCase "quoted atom as functor" $
        bodyOf "c <=> 'hello'."
          >>= (@?= [CompoundTerm (Unqualified "hello") []]),
      testCase "quoted atom with space" $
        bodyOf "c <=> 'hello world'."
          >>= (@?= [CompoundTerm (Unqualified "hello world") []]),
      testCase "empty quoted atom" $
        bodyOf "c <=> ''."
          >>= (@?= [CompoundTerm (Unqualified "") []]),
      testCase "quoted atom with '' escape (ISO Prolog)" $
        bodyOf "c <=> 'it''s'."
          >>= (@?= [CompoundTerm (Unqualified "it's") []]),
      testCase "quoted atom with \\' escape (SWI-Prolog)" $
        bodyOf "c <=> 'a\\'b'."
          >>= (@?= [CompoundTerm (Unqualified "a'b") []]),
      testCase "quoted atom with \\\\ escape" $
        bodyOf "c <=> 'back\\\\slash'."
          >>= (@?= [CompoundTerm (Unqualified "back\\slash") []]),
      testCase "zero-arity compound via quoted atom" $
        bodyOf "c <=> 'foo'(X, 1)."
          >>= (@?= [CompoundTerm (Unqualified "foo") [VarTerm "X", IntTerm 1]]),
      testCase "nested compound" $
        bodyOf "c <=> f(g(X))."
          >>= ( @?=
                  [ CompoundTerm
                      (Unqualified "f")
                      [ CompoundTerm
                          (Unqualified "g")
                          [ VarTerm
                              "X"
                          ]
                      ]
                  ]
              )
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
-- Float literals
-- ---------------------------------------------------------------------------

floatLiteralTests :: TestTree
floatLiteralTests =
  testGroup
    "float literals"
    [ testCase "positive float in body" $
        bodyOf "c <=> f(3.14)."
          >>= (@?= [CompoundTerm (Unqualified "f") [FloatTerm 3.14]]),
      testCase "negative float in body" $
        bodyOf "c <=> f(-2.5)."
          >>= (@?= [CompoundTerm (Unqualified "f") [FloatTerm (-2.5)]]),
      testCase "float in constraint argument" $
        headOf "c(1.5, X) <=> true."
          >>= ( @?=
                  Simplification
                    [Constraint (Unqualified "c") [FloatTerm 1.5, VarTerm "X"]]
              ),
      testCase "zero float" $
        bodyOf "c <=> f(0.0)."
          >>= (@?= [CompoundTerm (Unqualified "f") [FloatTerm 0.0]])
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
                      [ VarTerm "N",
                        CompoundTerm
                          (Qualified "host" "+")
                          [ VarTerm "X",
                            IntTerm 1
                          ]
                      ]
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
          >>= (@?= [CompoundTerm (Unqualified "=") [VarTerm "X", VarTerm "Y"]]),
      testCase "is with comparison RHS (no parens needed)" $
        bodyOfWithLt "c <=> B is 1 < 2."
          >>= ( @?=
                  [ CompoundTerm
                      (Unqualified "is")
                      [ VarTerm "B",
                        CompoundTerm
                          (Unqualified "<")
                          [IntTerm 1, IntTerm 2]
                      ]
                  ]
              ),
      testCase "= with comparison RHS (no parens needed)" $
        bodyOfWithLt "c <=> T = X < Y."
          >>= ( @?=
                  [ CompoundTerm
                      (Unqualified "=")
                      [ VarTerm "T",
                        CompoundTerm
                          (Unqualified "<")
                          [VarTerm "X", VarTerm "Y"]
                      ]
                  ]
              )
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
                ( noAnnP
                    ( Simplification
                        [ Constraint
                            (Unqualified "leq")
                            [ VarTerm "X",
                              VarTerm "X"
                            ]
                        ]
                    )
                )
                (noAnnP [])
                (noAnnP [CompoundTerm (Unqualified "true") []])
            ],
      testCase "unnamed simplification" $
        (map stripRuleLoc . (.rules)) <$> p "leq(X, X) <=> true."
          @?= Right
            [ Rule
                Nothing
                ( noAnnP
                    ( Simplification
                        [ Constraint
                            (Unqualified "leq")
                            [ VarTerm "X",
                              VarTerm "X"
                            ]
                        ]
                    )
                )
                (noAnnP [])
                (noAnnP [CompoundTerm (Unqualified "true") []])
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
                (noAnnP [CompoundTerm (Unqualified "body") []])
            ],
      testCase "rule with guard" $
        (map stripRuleLoc . (.rules)) <$> p "r @ c(X, Y) <=> g(X) | b(Y)."
          @?= Right
            [ Rule
                (Just (noAnn "r"))
                ( noAnnP
                    ( Simplification
                        [ Constraint
                            (Unqualified "c")
                            [ VarTerm "X",
                              VarTerm "Y"
                            ]
                        ]
                    )
                )
                (noAnnP [CompoundTerm (Unqualified "g") [VarTerm "X"]])
                (noAnnP [CompoundTerm (Unqualified "b") [VarTerm "Y"]])
            ],
      testCase "multiple body goals" $
        bodyOf "c <=> a, b, c2."
          >>= ( @?=
                  [ CompoundTerm (Unqualified "a") [],
                    CompoundTerm (Unqualified "b") [],
                    CompoundTerm (Unqualified "c2") []
                  ]
              ),
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
                  [ algebraicTD
                      (Unqualified "color")
                      []
                      [ DataConstructor (Unqualified "red") [],
                        DataConstructor (Unqualified "green") [],
                        DataConstructor (Unqualified "blue") []
                      ]
                      dummyLoc
                  ]
              ),
      testCase "type with constructor args" $
        typeDefsOf ":- chr_type tree ---> empty ; leaf(int) ; branch(tree, tree)."
          >>= ( @?=
                  [ algebraicTD
                      (Unqualified "tree")
                      []
                      [ DataConstructor (Unqualified "empty") [],
                        DataConstructor (Unqualified "leaf") [TypeCon (Unqualified "int") []],
                        DataConstructor
                          (Unqualified "branch")
                          [ TypeCon
                              (Unqualified "tree")
                              [],
                            TypeCon (Unqualified "tree") []
                          ]
                      ]
                      dummyLoc
                  ]
              ),
      testCase "parameterized type" $
        typeDefsOf ":- chr_type pair(A, B) ---> pair(A, B)."
          >>= ( @?=
                  [ algebraicTD
                      (Unqualified "pair")
                      ["A", "B"]
                      [ DataConstructor (Unqualified "pair") [TypeVar "A", TypeVar "B"]
                      ]
                      dummyLoc
                  ]
              ),
      testCase "list type with list sugar" $
        typeDefsOf ":- chr_type list(T) ---> [] ; [T | list(T)]."
          >>= ( @?=
                  [ algebraicTD
                      (Unqualified "list")
                      ["T"]
                      [ DataConstructor (Unqualified "[]") [],
                        DataConstructor
                          (Unqualified ".")
                          [ TypeVar "T",
                            TypeCon (Unqualified "list") [TypeVar "T"]
                          ]
                      ]
                      dummyLoc
                  ]
              ),
      testCase "type with nested type args" $
        typeDefsOf ":- chr_type nested ---> wrap(pair(int, int))."
          >>= ( @?=
                  [ algebraicTD
                      (Unqualified "nested")
                      []
                      [ DataConstructor
                          (Unqualified "wrap")
                          [ TypeCon
                              (Unqualified "pair")
                              [TypeCon (Unqualified "int") [], TypeCon (Unqualified "int") []]
                          ]
                      ]
                      dummyLoc
                  ]
              ),
      testCase "type decl doesn't affect constraint decls" $
        case p ":- chr_type t ---> a.\n:- chr_constraint c/1." of
          Left err -> assertFailure (show err)
          Right m -> do
            map (.node) m.decls @?= [ConstraintDecl "c" 1 Nothing Nothing]
            map (normalizeTypeDefLoc . (.node)) m.typeDecls
              @?= [ algebraicTD
                      (Unqualified "t")
                      []
                      [DataConstructor (Unqualified "a") []]
                      dummyLoc
                  ],
      testCase "multiple type decls" $
        typeDefsOf ":- chr_type a ---> x.\n:- chr_type b ---> y."
          >>= ( @?=
                  [ algebraicTD
                      (Unqualified "a")
                      []
                      [DataConstructor (Unqualified "x") []]
                      dummyLoc,
                    algebraicTD
                      (Unqualified "b")
                      []
                      [DataConstructor (Unqualified "y") []]
                      dummyLoc
                  ]
              ),
      testCase "opaque type with a parameter" $
        typeDefsOf ":- opaque_type set(X)."
          >>= ( @?=
                  [TypeDefinition (Unqualified "set") ["X"] Opaque dummyLoc]
              ),
      testCase "opaque type with no parameters" $
        typeDefsOf ":- opaque_type handle."
          >>= ( @?=
                  [TypeDefinition (Unqualified "handle") [] Opaque dummyLoc]
              ),
      testCase "opaque type with a constructor body is rejected" $
        pErrs ":- opaque_type set(X) ---> mk(X)."
          @?= Right [OpaqueTypeHasConstructors],
      testCase "opaque type exported with the shared type(...) form" $
        fmap (.node) . (.exports) <$> p ":- module(m, [type(set/1)])."
          @?= Right (Just [TypeExportDecl "set" 1 Nothing])
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
                { name = "order",
                  nameLoc = dummyLoc,
                  imports = [],
                  decls = [noAnn (ConstraintDecl "leq" 2 Nothing Nothing)],
                  extensionTypes = [],
                  typeDecls = [],
                  rules =
                    [ Rule
                        (Just (noAnn "refl"))
                        ( noAnnP
                            ( Simplification
                                [ Constraint
                                    (Unqualified "leq")
                                    [VarTerm "X", VarTerm "X"]
                                ]
                            )
                        )
                        (noAnnP [])
                        (noAnnP [CompoundTerm (Unqualified "true") []]),
                      Rule
                        (Just (noAnn "antisymmetry"))
                        ( noAnnP
                            ( Simplification
                                [ Constraint
                                    (Unqualified "leq")
                                    [VarTerm "X", VarTerm "Y"],
                                  Constraint
                                    (Unqualified "leq")
                                    [VarTerm "Y", VarTerm "X"]
                                ]
                            )
                        )
                        (noAnnP [])
                        ( noAnnP
                            [ CompoundTerm
                                (Unqualified "leq")
                                [VarTerm "X", VarTerm "Y"]
                            ]
                        ),
                      Rule
                        (Just (noAnn "trans"))
                        ( noAnnP
                            ( Propagation
                                [ Constraint
                                    (Unqualified "leq")
                                    [VarTerm "X", VarTerm "Y"],
                                  Constraint
                                    (Unqualified "leq")
                                    [VarTerm "Y", VarTerm "Z"]
                                ]
                            )
                        )
                        (noAnnP [])
                        ( noAnnP
                            [ CompoundTerm
                                (Unqualified "leq")
                                [VarTerm "X", VarTerm "Z"]
                            ]
                        )
                    ],
                  equations = [],
                  extensions = [],
                  classExtensions = [],
                  exports = Just (noAnnP [])
                }
            ),
      testCase "no module directive gives default name" $
        (.name) <$> p ":- chr_constraint foo/1.\nfoo(X) <=> true."
          @?= Right "<no_module>",
      testCase "module/1 sets name and leaves exports unset" $
        case p ":- module(foo).\n:- chr_constraint c/1.\nc(X) <=> true." of
          Right m -> do
            m.name @?= "foo"
            m.exports @?= Nothing
          Left e -> assertFailure (show e)
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
          @?= Right
            [ Rule
                Nothing
                ( noAnnP
                    ( Simplification
                        [ Constraint
                            (Unqualified "foo")
                            []
                        ]
                    )
                )
                (noAnnP [])
                (noAnnP [CompoundTerm (Unqualified "bar") []])
            ],
      testCase "inline comment after rule" $
        (map stripRuleLoc . (.rules)) <$> p "foo <=> bar. % comment"
          @?= Right
            [ Rule
                Nothing
                ( noAnnP
                    ( Simplification
                        [ Constraint
                            (Unqualified "foo")
                            []
                        ]
                    )
                )
                (noAnnP [])
                (noAnnP [CompoundTerm (Unqualified "bar") []])
            ],
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
ops :: Text -> Either (ParseError) [OpDecl]
ops src = (.exportOps) <$> collectModuleHeader "" src

-- | Helper: collect imports from a module header.
hdrImports :: Text -> Either (ParseError) [Import]
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
        ops ":- module(m, [leq/2, type(tree/0), op(400, yfx, '*'), type(list/1)])."
          @?= Right
            [OpDecl 400 Yfx "*"],
      testCase "no module directive returns empty exports" $
        ops ":- chr_constraint leq/2." @?= Right [],
      testCase "empty export list returns empty" $
        ops ":- module(m, [])." @?= Right [],
      testCase "collects use_module imports right after the module directive" $
        hdrImports ":- module(m, []). :- use_module(foo). :- use_module(library(bar))."
          @?= Right [ModuleImport "foo" Nothing, LibraryImport "bar" Nothing],
      testCase "stops collecting imports at the first non-import directive" $
        hdrImports
          ( ":- module(m, []). :- use_module(foo). "
              <> ":- chr_constraint c/1. :- use_module(bar)."
          )
          @?= Right [ModuleImport "foo" Nothing],
      testCase "import lists with op() entries parse" $
        hdrImports ":- module(m, []). :- use_module(foo, [op(700, xfx, '<-')])."
          @?= Right [ModuleImport "foo" (Just [OperatorDecl (OpDecl 700 Xfx "<-")])],
      testCase "skips fun name/arity entries" $
        ops ":- module(m, [fun double/1, op(500, yfx, '+')])." @?= Right [OpDecl 500 Yfx "+"],
      testCase "fun name/arity and name/arity coexist in export list" $
        ops ":- module(m, [leq/2, fun double/1, op(700, xfx, '<')])."
          @?= Right
            [ OpDecl
                700
                Xfx
                "<"
            ]
    ]

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

typeDefsOf :: Text -> IO [TypeDefinition]
typeDefsOf src = case p src of
  Left err -> assertFailure (show err)
  Right m -> pure (map (normalizeTypeDefLoc . (.node)) m.typeDecls)

-- | Build an algebraic type definition positionally (the constructors
-- are wrapped in the 'Algebraic' 'TypeKind').
algebraicTD :: Name -> [Text] -> [DataConstructor] -> SourceLoc -> TypeDefinition
algebraicTD n vs cs loc = TypeDefinition n vs (Algebraic cs) loc

-- | Strip the source location from a parsed 'TypeDefinition' so test
-- expected values can omit line/column numbers.
normalizeTypeDefLoc :: TypeDefinition -> TypeDefinition
normalizeTypeDefLoc td =
  TypeDefinition
    { name = td.name,
      typeVars = td.typeVars,
      kind = td.kind,
      loc = dummyLoc
    }

bodyOf :: Text -> IO [Term]
bodyOf src = case p src of
  Left err -> assertFailure (show err)
  Right m -> case m.rules of
    [] -> assertFailure "expected at least one rule, got none"
    (r : _) -> pure r.body.node

-- | Like 'bodyOf', but parses with @<@ added as a 700 xfx operator so
-- precedence interactions between @is@\/@=@ and a comparison can be tested
-- without pulling in the whole prelude.
bodyOfWithLt :: Text -> IO [Term]
bodyOfWithLt src = case mergeOps builtinOps [OpDecl 700 Xfx "<"] of
  Left e -> assertFailure ("mergeOps failed: " <> Text.unpack e)
  Right table -> case fst <$> parseModuleWith table "" src of
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
