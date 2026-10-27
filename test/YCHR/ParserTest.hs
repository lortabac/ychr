{-# LANGUAGE OverloadedStrings #-}

module YCHR.ParserTest (tests) where

import Data.Either (isLeft)
import Data.Text (Text)
import Data.Text qualified as Text
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import Text.Parsec (ParseError)
import YCHR.DSL (atom)
import YCHR.Internal.Parsed
import YCHR.Internal.Parser
  ( Converted (..),
    ModuleHeader (..),
    ParseValidationError (..),
    builtinOps,
    collectModuleHeader,
    mergeOps,
    parseModule,
    parseModuleWith,
  )
import YCHR.TestHelpers (algebraicTD)

-- | Parser tests: directives, rules, terms, operators, type declarations, and errors.
tests :: TestTree
tests =
  testGroup
    "YCHR.Internal.Parser"
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
p :: Text -> Either ParseError Module
p src = (.value) <$> parseModule "" src

-- | Parse and return only the validation errors, with each error's
-- variant extracted (location/origin discarded).
pErrs :: Text -> Either ParseError [ParseValidationError]
pErrs src = map (.node) . (.errors) <$> parseModule "" src

-- | A module's macros as @(name, arity, [(params, body)])@, with the
-- source annotations dropped.
macroShapes :: Module -> [(Text, Int, [([Term], [Term])])]
macroShapes m =
  [ (d.node.name, d.node.arity, [(c.node.params, c.node.body) | c <- d.node.clauses])
  | d <- m.macros
  ]

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

-- | Parse a module and return the first declaration's @requiring@
-- bounds, each with its location stripped for structural comparison.
firstRequiring :: Text -> Either ParseError (Maybe [BoundSig])
firstRequiring src = do
  m <- p src
  pure $ case map (.node) m.decls of
    (FunctionDecl fd : _) -> fmap (map stripBoundSigLoc) fd.requiring
    (ConstraintDecl cd : _) -> fmap (map stripBoundSigLoc) cd.requiring
    _ -> Nothing
  where
    stripBoundSigLoc :: BoundSig -> BoundSig
    stripBoundSigLoc (BoundSig n a at rt _) = BoundSig n a at rt dummyLoc

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
                [ ConstraintDecl (ConstraintDeclBody "leq" 2 Nothing Nothing),
                  ConstraintDecl (ConstraintDeclBody "foo" 1 Nothing Nothing)
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
          @?= Right
            [ ModuleImport
                "order"
                (Just [ConstraintDecl (ConstraintDeclBody "leq" 2 Nothing Nothing)])
            ],
      testCase "use_module library with import list" $
        (map (.node) . (.imports))
          <$> p ":- use_module(library(mylib), [foo/1, type(tree/0)])."
          @?= Right
            [ LibraryImport
                "mylib"
                ( Just
                    [ ConstraintDecl (ConstraintDeclBody "foo" 1 Nothing Nothing),
                      TypeExportDecl (TypeExportDeclBody "tree" 0 Nothing)
                    ]
                )
            ],
      testCase "chr_constraint single" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint leq/2."
          @?= Right [ConstraintDecl (ConstraintDeclBody "leq" 2 Nothing Nothing)],
      testCase "chr_constraint multiple in one directive" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint fib/2, upto/1."
          @?= Right
            [ ConstraintDecl (ConstraintDeclBody "fib" 2 Nothing Nothing),
              ConstraintDecl (ConstraintDeclBody "upto" 1 Nothing Nothing)
            ],
      testCase "chr_constraint zero arity" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint fire/0."
          @?= Right [ConstraintDecl (ConstraintDeclBody "fire" 0 Nothing Nothing)],
      testCase "type export in export list" $
        fmap (.node) . (.exports) <$> p ":- module(m, [type(tree/0), leq/2])."
          @?= Right
            ( Just
                [ TypeExportDecl (TypeExportDeclBody "tree" 0 Nothing),
                  ConstraintDecl (ConstraintDeclBody "leq" 2 Nothing Nothing)
                ]
            ),
      testCase "type export with constructor allowlist" $
        fmap (.node) . (.exports)
          <$> p ":- module(m, [type(foo/0, [bar, baz])])."
          @?= Right
            (Just [TypeExportDecl (TypeExportDeclBody "foo" 0 (Just ["bar", "baz"]))]),
      testCase "type export with empty constructor list" $
        fmap (.node) . (.exports)
          <$> p ":- module(m, [type(foo/0, [])])."
          @?= Right (Just [TypeExportDecl (TypeExportDeclBody "foo" 0 (Just []))]),
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
      -- The low-level converter has no macro visibility; the compile
      -- pipeline reports an unknown directive (see "YCHR.DeclMacroTest").
      testCase "unknown directive is skipped by the converter" $
        (map (.node) . (.decls))
          <$> p ":- mystery_directive(foo).\n:- chr_constraint leq/2."
          @?= Right [ConstraintDecl (ConstraintDeclBody "leq" 2 Nothing Nothing)],
      testCase "chr_constraint typed" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint leq(int, int)."
          @?= Right
            [ ConstraintDecl
                ( ConstraintDeclBody
                    "leq"
                    2
                    ( Just
                        [ TypeCon (Unqualified "int") [],
                          TypeCon (Unqualified "int") []
                        ]
                    )
                    Nothing
                )
            ],
      testCase "chr_constraint typed with type variables" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint foo(list(T), T)."
          @?= Right
            [ ConstraintDecl
                ( ConstraintDeclBody
                    "foo"
                    2
                    (Just [TypeCon (Unqualified "list") [TypeVar "T"], TypeVar "T"])
                    Nothing
                )
            ],
      testCase "chr_constraint typed zero arity" $
        (map (.node) . (.decls)) <$> p ":- chr_constraint fire()."
          @?= Right [ConstraintDecl (ConstraintDeclBody "fire" 0 (Just []) Nothing)],
      testCase "function typed" $
        (map (.node) . (.decls)) <$> p ":- function factorial(int) -> int."
          @?= Right
            [ FunctionDecl
                ( FunctionDeclBody
                    "factorial"
                    1
                    (Just [TypeCon (Unqualified "int") []])
                    (Just (TypeCon (Unqualified "int") []))
                    False
                    DKFunction
                    Nothing
                    Nothing
                )
            ],
      testCase "function typed with refining" $
        (map (.node) . (.decls))
          <$> p ":- function integer(any) -> bool refining int."
          @?= Right
            [ FunctionDecl
                ( FunctionDeclBody
                    "integer"
                    1
                    (Just [TypeCon (Unqualified "any") []])
                    (Just (TypeCon (Unqualified "bool") []))
                    False
                    DKFunction
                    Nothing
                    (Just (TypeCon (Unqualified "int") []))
                )
            ],
      testCase "function typed multiple args" $
        (map (.node) . (.decls)) <$> p ":- function add(int, int) -> int."
          @?= Right
            [ FunctionDecl
                ( FunctionDeclBody
                    "add"
                    2
                    ( Just
                        [ TypeCon (Unqualified "int") [],
                          TypeCon (Unqualified "int") []
                        ]
                    )
                    (Just (TypeCon (Unqualified "int") []))
                    False
                    DKFunction
                    Nothing
                    Nothing
                )
            ],
      testCase "function untyped" $
        (map (.node) . (.decls)) <$> p ":- function foo/2."
          @?= Right
            [ FunctionDecl
                ( FunctionDeclBody
                    "foo"
                    2
                    Nothing
                    Nothing
                    False
                    DKFunction
                    Nothing
                    Nothing
                )
            ],
      testCase "requiring bound with a qualified name" $
        firstRequiring
          ":- function pick(T, T) -> T requiring lib:gt(T, T) -> bool."
          @?= Right
            ( Just
                [ BoundSig
                    (Qualified "lib" "gt")
                    2
                    [TypeVar "T", TypeVar "T"]
                    (TypeCon (Unqualified "bool") [])
                    dummyLoc
                ]
            ),
      testCase "requiring bound with a qualified, zero-arity name" $
        firstRequiring ":- function pick(T) -> T requiring lib:k -> int."
          @?= Right
            ( Just
                [ BoundSig
                    (Qualified "lib" "k")
                    0
                    []
                    (TypeCon (Unqualified "int") [])
                    dummyLoc
                ]
            ),
      testCase "requiring bound with a variable qualifier is malformed" $ do
        -- A variable module part isn't a qualified name.
        (map (.node) . (.decls))
          <$> p ":- function pick(T, T) -> T requiring X:gt(T, T) -> bool."
          @?= Right []
        pErrs ":- function pick(T, T) -> T requiring X:gt(T, T) -> bool."
          @?= Right [MalformedBoundSig],
      testCase "macro nullary head, single goal body" $
        macroShapes <$> p ":- macro foo ---> [bar]."
          @?= Right [("foo", 0, [([], [atom "bar"])])],
      testCase "macro with parameters, single-compound body" $
        macroShapes
          <$> p ":- macro in_degree(N, C) ---> [count(edge(_, N), C)]."
          @?= Right
            [ ( "in_degree",
                2,
                [ ( [VarTerm "N", VarTerm "C"],
                    [ CompoundTerm
                        (Unqualified "count")
                        [ CompoundTerm (Unqualified "edge") [Wildcard, VarTerm "N"],
                          VarTerm "C"
                        ]
                    ]
                  )
                ]
              )
            ],
      testCase "macro with a two-goal body" $
        macroShapes <$> p ":- macro both(X) ---> [a(X), b(X)]."
          @?= Right
            [ ( "both",
                1,
                [ ( [VarTerm "X"],
                    [ CompoundTerm (Unqualified "a") [VarTerm "X"],
                      CompoundTerm (Unqualified "b") [VarTerm "X"]
                    ]
                  )
                ]
              )
            ],
      testCase "macro with an empty body" $
        macroShapes <$> p ":- macro nothing(_) ---> []."
          @?= Right [("nothing", 1, [([Wildcard], [])])],
      testCase "macro body that is not a list is rejected" $
        pErrs ":- macro foo(X) ---> a(X)." @?= Right [MalformedMacroBody],
      testCase "macro body with a tail variable is rejected" $
        pErrs ":- macro foo(X, T) ---> [a(X) | T]." @?= Right [MalformedMacroBody],
      testCase "macro head patterns: '_', repeated, constant, list" $
        macroShapes <$> p ":- macro foo(_, X, X, 1, [H|T]) ---> [a(H, T)]."
          @?= Right
            [ ( "foo",
                5,
                [ ( [ Wildcard,
                      VarTerm "X",
                      VarTerm "X",
                      IntTerm 1,
                      CompoundTerm (Unqualified ".") [VarTerm "H", VarTerm "T"]
                    ],
                    [CompoundTerm (Unqualified "a") [VarTerm "H", VarTerm "T"]]
                  )
                ]
              )
            ],
      testCase "multi-clause macro: clauses grouped in order, declaration after them" $
        macroShapes
          <$> p
            "all_of([]) ---> [].\nall_of([G|Gs]) ---> [G, all_of(Gs)].\n:- macro all_of/1.\n"
          @?= Right
            [ ( "all_of",
                1,
                [ ([atom "[]"], []),
                  ( [CompoundTerm (Unqualified ".") [VarTerm "G", VarTerm "Gs"]],
                    [VarTerm "G", CompoundTerm (Unqualified "all_of") [VarTerm "Gs"]]
                  )
                ]
              )
            ],
      testCase "multi-clause macro: clauses are well-formed with no errors" $
        pErrs ":- macro all_of/1.\nall_of([]) ---> [].\nall_of([G|Gs]) ---> [G, all_of(Gs)].\n"
          @?= Right [],
      testCase "a declaration inside the clause block splits it" $
        pErrs "all_of([]) ---> [].\n:- macro all_of/1.\nall_of([G|Gs]) ---> [G, all_of(Gs)].\n"
          @?= Right [DiscontiguousMacroClauses "all_of" 1],
      testCase "declaration list declares several macros" $
        (map (\(n, a, _) -> (n, a)) . macroShapes) <$> p ":- macro foo/1, bar/2."
          @?= Right [("foo", 1), ("bar", 2)],
      testCase "declared macro with no clauses" $
        macroShapes <$> p ":- macro foo/2." @?= Right [("foo", 2, [])],
      testCase "undeclared macro clause is rejected" $
        pErrs "foo(X) ---> [a(X)]." @?= Right [UndeclaredMacroClause "foo" 1],
      testCase "macro clause of another arity is undeclared" $
        pErrs ":- macro foo/1.\nfoo(X, Y) ---> [a(X, Y)]."
          @?= Right [UndeclaredMacroClause "foo" 2],
      testCase "discontiguous macro clauses are rejected" $
        pErrs ":- macro foo/1.\nfoo(a) ---> [].\n:- chr_constraint c/0.\nfoo(b) ---> []."
          @?= Right [DiscontiguousMacroClauses "foo" 1],
      testCase "extra clauses of a one-line macro form a second definition" $
        (map (\(n, a, cs) -> (n, a, length cs)) . macroShapes)
          <$> p ":- macro foo(a) ---> [].\nfoo(b) ---> [].\nfoo(c) ---> []."
          @?= Right [("foo", 1, 1), ("foo", 1, 2)],
      testCase "extra clauses before a one-line macro come second" $
        (map (\(_, _, cs) -> map fst cs) . macroShapes)
          <$> p "foo(b) ---> [].\n:- macro foo(a) ---> []."
          @?= Right [[[atom "a"]], [[atom "b"]]],
      testCase "macro(n/a) in export list" $
        fmap (.node) . (.exports) <$> p ":- module(m, [macro(foo/2)])."
          @?= Right (Just [MacroExportDecl (MacroExportDeclBody "foo" 2)]),
      testCase "macro(n/a) in use_module import list" $
        case p ":- use_module(agg, [macro(count/2)])." of
          Right m -> case m.imports of
            [AnnP (ModuleImport "agg" (Just decls)) _ _] ->
              decls @?= [MacroExportDecl (MacroExportDeclBody "count" 2)]
            other -> assertFailure ("unexpected imports: " ++ show other)
          Left err -> assertFailure ("parse failed: " ++ show err),
      testCase "macro head qualified name is rejected" $
        pErrs ":- macro m:foo(X) ---> []." @?= Right [MalformedMacroHead],
      testCase "macro head reserved name is rejected" $
        pErrs ":- macro is(X, Y) ---> []." @?= Right [MalformedMacroHead],
      testCase "macro head primitive name is rejected" $
        pErrs ":- macro '$compound'(X, Y) ---> []." @?= Right [MalformedMacroHead],
      testCase "macro declaration with a reserved name is rejected" $
        pErrs ":- macro is/2." @?= Right [MalformedMacroHead],
      testCase "macro directive of another shape is rejected" $
        pErrs ":- macro foo(X)." @?= Right [MalformedMacroHead],
      testCase "macro_decls one-line definition is a declaration macro" $
        map (\d -> (d.node.kind, d.node.name, d.node.arity))
          . (.macros)
          <$> p ":- macro_decls flag(N) ---> [(:- chr_constraint N/0)]."
          @?= Right [(DeclMacro, "flag", 1)],
      testCase "macro_decls declaration gives its clauses its kind" $
        map (\d -> (d.node.kind, length d.node.clauses))
          . (.macros)
          <$> p ":- macro_decls f/1.\nf([]) ---> [].\nf([_|T]) ---> [(:- f(T))]."
          @?= Right [(DeclMacro, 2)],
      testCase "macro and macro_decls in one module keep their kinds" $
        map (\d -> (d.node.kind, d.node.name))
          . (.macros)
          <$> p ":- macro g/0.\n:- macro_decls d/0.\ng ---> [].\nd ---> []."
          @?= Right [(GoalMacro, "g"), (DeclMacro, "d")],
      testCase "macro_decls with a built-in directive's name and arity is rejected" $
        pErrs ":- macro_decls use_module(X) ---> []."
          @?= Right [DeclMacroBuiltinDirective "use_module" 1],
      testCase "macro_decls declaration with a built-in directive's key is rejected" $
        pErrs ":- macro_decls module/1." @?= Right [DeclMacroBuiltinDirective "module" 1],
      testCase "macro_decls may use another arity of a built-in directive" $
        pErrs ":- macro_decls module(A, B, C) ---> [(:- module(A, B)), C]."
          @?= Right [],
      testCase "a goal macro may use a built-in directive's name" $
        pErrs ":- macro inline(X) ---> [X]." @?= Right [],
      testCase "constraint_use with every tag" $
        (map (.node) . (.constraintUses))
          <$> p ":- constraint_use any(a/0), fact(b/1), event(c/2), tell_only(d/3)."
          @?= Right
            [ ConstraintUseDecl UseAny "a" 0,
              ConstraintUseDecl UseFact "b" 1,
              ConstraintUseDecl UseEvent "c" 2,
              ConstraintUseDecl UseTellOnly "d" 3
            ],
      testCase "constraint_use with an unknown tag is rejected" $
        pErrs ":- constraint_use positive(c/1)." @?= Right [MalformedDeclaration],
      testCase "constraint_use tag with two entries is rejected" $
        pErrs ":- constraint_use fact(a/1, b/1)." @?= Right [MalformedDeclaration],
      testCase "constraint_use bare name/arity is rejected" $
        pErrs ":- constraint_use c/1." @?= Right [MalformedDeclaration]
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
          >>= (@?= Simplification [Constraint (Unqualified "c") [Wildcard]] []),
      testCase "underscore-prefixed variable in body" $
        bodyOf "c(X) <=> _X." >>= (@?= [VarTerm "_X"]),
      testCase "underscore-prefixed variable in head" $
        headOf "c(_X) <=> true."
          >>= (@?= Simplification [Constraint (Unqualified "c") [VarTerm "_X"]] []),
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
          >>= ( @?=
                  Simplification
                    [Constraint (Unqualified "c") [IntTerm (-3), VarTerm "X"]]
                    []
              ),
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
                    []
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
              ),
      -- `\` is a symbol character, so a multi-character operator may use
      -- it (both `\` as simpagation and `\==` as disequality).
      testCase "backslash disequality operator" $
        bodyOfWithBackslashEq "c <=> X \\== Y."
          >>= ( @?=
                  [ CompoundTerm
                      (Unqualified "\\==")
                      [VarTerm "X", VarTerm "Y"]
                  ]
              ),
      testCase "backslash disequality operator via quoted functor" $
        bodyOfWithBackslashEq "c <=> '\\\\=='(X, Y)."
          >>= ( @?=
                  [ CompoundTerm
                      (Unqualified "\\==")
                      [VarTerm "X", VarTerm "Y"]
                  ]
              ),
      testCase "backslash disequality rejects when undeclared" $
        -- Without the `\==` operator in the table the greedy symbol
        -- tokenizer consumes it whole and rejects it.
        assertBool "expected parse failure" (isLeft (p "c <=> X \\== Y."))
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
                        []
                    )
                )
                (noAnnP [])
                (noAnnP [CompoundTerm (Unqualified "true") []])
                []
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
                        []
                    )
                )
                (noAnnP [])
                (noAnnP [CompoundTerm (Unqualified "true") []])
                []
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
                        []
                    )
                )
                (noAnnP [])
                (noAnnP [CompoundTerm (Unqualified "leq") [VarTerm "X", VarTerm "Z"]])
                []
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
                        []
                    )
                )
                (noAnnP [])
                (noAnnP [CompoundTerm (Unqualified "body") []])
                []
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
                        []
                    )
                )
                (noAnnP [CompoundTerm (Unqualified "g") [VarTerm "X"]])
                (noAnnP [CompoundTerm (Unqualified "b") [VarTerm "Y"]])
                []
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
          >>= (@?= Simplification [Constraint (Unqualified "fire") []] [])
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
                        DataConstructor
                          (Unqualified "leaf")
                          [TypeCon (Unqualified "int") []],
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
                              [ TypeCon (Unqualified "int") [],
                                TypeCon (Unqualified "int") []
                              ]
                          ]
                      ]
                      dummyLoc
                  ]
              ),
      testCase "type decl doesn't affect constraint decls" $
        case p ":- chr_type t ---> a.\n:- chr_constraint c/1." of
          Left err -> assertFailure (show err)
          Right m -> do
            map (.node) m.decls
              @?= [ConstraintDecl (ConstraintDeclBody "c" 1 Nothing Nothing)]
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
          @?= Right (Just [TypeExportDecl (TypeExportDeclBody "set" 1 Nothing)])
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
                  decls =
                    [noAnn (ConstraintDecl (ConstraintDeclBody "leq" 2 Nothing Nothing))],
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
                                []
                            )
                        )
                        (noAnnP [])
                        (noAnnP [CompoundTerm (Unqualified "true") []])
                        [],
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
                                []
                            )
                        )
                        (noAnnP [])
                        ( noAnnP
                            [ CompoundTerm
                                (Unqualified "leq")
                                [VarTerm "X", VarTerm "Y"]
                            ]
                        )
                        [],
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
                                []
                            )
                        )
                        (noAnnP [])
                        ( noAnnP
                            [ CompoundTerm
                                (Unqualified "leq")
                                [VarTerm "X", VarTerm "Z"]
                            ]
                        )
                        []
                    ],
                  equations = [],
                  extensions = [],
                  classExtensions = [],
                  inlines = [],
                  constraintUses = [],
                  macros = [],
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

-- | The classic @leq@ handler, as a parser fixture.
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
                        []
                    )
                )
                (noAnnP [])
                (noAnnP [CompoundTerm (Unqualified "bar") []])
                []
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
                        []
                    )
                )
                (noAnnP [])
                (noAnnP [CompoundTerm (Unqualified "bar") []])
                []
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
ops :: Text -> Either ParseError [OpDecl]
ops src = (.exportOps) <$> collectModuleHeader "" src

-- | Helper: collect imports from a module header.
hdrImports :: Text -> Either ParseError [Import]
hdrImports src = map (.node) . (.headerImports) <$> collectModuleHeader "" src

firstPassTests :: TestTree
firstPassTests =
  testGroup
    "first-pass module-header collector"
    [ testCase "extracts operators from export list" $
        ops ":- module(m, [op(500, yfx, '+')])." @?= Right [OpDecl 500 Yfx "+"],
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

-- | Parse @src@ with @parseSrc@, failing the test on a parse error, and pass
-- the resulting module to @extract@.
parseAndExtract ::
  (Text -> Either ParseError Module) ->
  (Module -> IO a) ->
  Text ->
  IO a
parseAndExtract parseSrc extract src = case parseSrc src of
  Left err -> assertFailure (show err)
  Right m -> extract m

-- | Apply @extract@ to the first rule of a parsed module, failing the test
-- when the module has no rules.
withFirstRule :: (Rule -> a) -> Module -> IO a
withFirstRule extract m = case m.rules of
  [] -> assertFailure "expected at least one rule, got none"
  (r : _) -> pure (extract r)

-- | The type definitions of a parsed module, locations stripped.
typeDefsOf :: Text -> IO [TypeDefinition]
typeDefsOf src = parseAndExtract p extract src
  where
    extract m = pure (map (normalizeTypeDefLoc . (.node)) m.typeDecls)

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

-- | The body of the module's first rule.
bodyOf :: Text -> IO [Term]
bodyOf src = parseAndExtract p (withFirstRule (.body.node)) src

-- | Like 'bodyOf', but parses with @<@ added as a 700 xfx operator so
-- precedence interactions between @is@\/@=@ and a comparison can be tested
-- without pulling in the whole prelude.
bodyOfWithLt :: Text -> IO [Term]
bodyOfWithLt src = case mergeOps builtinOps [OpDecl 700 Xfx "<"] of
  Left e -> assertFailure ("mergeOps failed: " <> Text.unpack e)
  Right table ->
    parseAndExtract
      (fmap (.value) . parseModuleWith table "")
      (withFirstRule (.body.node))
      src

-- | Like 'bodyOf', but parses with @\\==@ added as a 700 xfx operator, the
-- fixity the prelude declares, so a body can use the disequality operator
-- without pulling in the whole prelude.
bodyOfWithBackslashEq :: Text -> IO [Term]
bodyOfWithBackslashEq src = case mergeOps builtinOps [OpDecl 700 Xfx "\\=="] of
  Left e -> assertFailure ("mergeOps failed: " <> Text.unpack e)
  Right table ->
    parseAndExtract
      (fmap (.value) . parseModuleWith table "")
      (withFirstRule (.body.node))
      src

-- | The head of the module's first rule.
headOf :: Text -> IO Head
headOf src = parseAndExtract p (withFirstRule (.head.node)) src

-- | The guard of the module's first rule.
guardOf :: Text -> IO [Term]
guardOf src = parseAndExtract p (withFirstRule (.guard.node)) src
