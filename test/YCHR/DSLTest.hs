{-# LANGUAGE OverloadedStrings #-}

module YCHR.DSLTest (tests) where

import Data.Map.Strict qualified as Map
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import YCHR.DSL
import YCHR.Parsed

tests :: TestTree
tests =
  testGroup
    "DSL"
    [ moduleTests,
      declarationTests,
      functionDeclarationTests,
      typeDeclarationTests,
      operatorDeclarationTests,
      ruleTests,
      guardTests,
      termTests,
      lambdaTests,
      numericInstanceTests,
      integrationTests,
      endToEndTests
    ]

--------------------------------------------------------------------------------
-- Fixtures
--------------------------------------------------------------------------------

orderModule :: Module
orderModule =
  module' "Order"
    `declaring` ["leq" // 2]
    `defining` [ "refl" @: ([term "leq" [var "X", var "X"]] <=> [atom "true"])
               ]

logicModule :: Module
logicModule =
  module' "Logic"
    `importing` ["Order"]
    `defining` [ "trans"
                   @: ( [term "leq" [var "X", var "Y"], term "leq" [var "Y", var "Z"]]
                          ==> [term "leq" [var "X", var "Z"]]
                      )
               ]

--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------

moduleTests :: TestTree
moduleTests =
  testGroup
    "module"
    [ testCase "module' produces empty module" $
        module' "Foo" @?= emptyModule "Foo",
      testCase "importing sets modImports" $
        module' "Foo" `importing` ["Bar", "Baz"]
          @?= (emptyModule "Foo")
            { imports =
                [ noAnnP (ModuleImport "Bar" Nothing),
                  noAnnP (ModuleImport "Baz" Nothing)
                ]
            },
      testCase "declaring sets modDecls" $
        module' "Foo" `declaring` ["leq" // 2]
          @?= (emptyModule "Foo")
            { decls = [noAnn (ConstraintDecl "leq" 2 Nothing Nothing)]
            },
      testCase "defining sets modRules" $
        let r = [term "leq" [var "X"]] <=> [atom "true"]
         in module' "Foo" `defining` [r]
              @?= (emptyModule "Foo") {rules = [r]},
      testCase "chaining importing, declaring, defining" $
        let r = [term "c" []] <=> [atom "true"]
         in module' "M"
              `importing` ["A"]
              `declaring` ["c" // 0]
              `defining` [r]
              @?= (emptyModule "M")
                { imports = [noAnnP (ModuleImport "A" Nothing)],
                  decls = [noAnn (ConstraintDecl "c" 0 Nothing Nothing)],
                  rules = [r]
                },
      testCase "exporting sets modExports" $
        module' "Foo" `exporting` ["leq" // 2]
          @?= (emptyModule "Foo")
            { exports = Just (noAnnP [ConstraintDecl "leq" 2 Nothing Nothing])
            },
      testCase "library appends a LibraryImport" $
        module' "Foo" `library` "lists" `library` "math"
          @?= (emptyModule "Foo")
            { imports =
                [ noAnnP (LibraryImport "lists" Nothing),
                  noAnnP (LibraryImport "math" Nothing)
                ]
            },
      testCase "exporting appends to an existing export list" $
        -- Two calls should accumulate, not replace — pinning the
        -- documented append-semantics in DSL.hs.
        module' "Foo" `exporting` ["a" // 1] `exporting` ["b" // 2]
          @?= (emptyModule "Foo")
            { exports =
                Just
                  ( noAnnP
                      [ ConstraintDecl "a" 1 Nothing Nothing,
                        ConstraintDecl "b" 2 Nothing Nothing
                      ]
                  )
            },
      testCase "withEquations appends to module.equations" $
        let eq = equation "f" [int 0] [] (int 1)
            m = module' "M" `withEquations` [eq]
         in m.equations @?= [noAnnP eq]
    ]
  where
    emptyModule n =
      Module
        { name = n,
          nameLoc = dummyLoc,
          imports = [],
          decls = [],
          extensionTypes = [],
          typeDecls = [],
          rules = [],
          equations = [],
          extensions = [],
          classExtensions = [],
          exports = Nothing
        }

declarationTests :: TestTree
declarationTests =
  testGroup
    "declaration"
    [ testCase "\"leq\" // 2 produces ConstraintDecl" $
        "leq" // 2 @?= ConstraintDecl "leq" 2 Nothing Nothing,
      testCase "\"foo\" // 0 produces ConstraintDecl with arity 0" $
        "foo" // 0 @?= ConstraintDecl "foo" 0 Nothing Nothing,
      testCase "extendClassType produces ExtendClassTypeDecl" $
        extendClassType
          "classify"
          [TypeCon (Unqualified "int") []]
          (TypeCon (Unqualified "int") [])
          @?= ExtendClassTypeDecl
            { name = "classify",
              arity = 1,
              argTypes = Just [TypeCon (Unqualified "int") []],
              returnType = Just (TypeCon (Unqualified "int") []),
              target = Nothing
            },
      testCase "withExtensions appends to module.extensions" $
        let eq = equation "classify" [atom "dog"] [] (atom "animal")
            m = module' "ext" `withExtensions` [eq]
         in m.extensions @?= [noAnnP eq],
      testCase "withClassExtensions appends to module.classExtensions" $
        let eq = equation "classify" [atom "dog"] [] (atom "animal")
            m = module' "ext" `withClassExtensions` [eq]
         in m.classExtensions @?= [noAnnP eq]
    ]

functionDeclarationTests :: TestTree
functionDeclarationTests =
  testGroup
    "function declaration"
    [ testCase "function produces FunctionDecl with isOpen = False" $
        function "factorial" 1
          @?= FunctionDecl
            { name = "factorial",
              arity = 1,
              argTypes = Nothing,
              returnType = Nothing,
              isOpen = False,
              kind = DKFunction,
              requiring = Nothing
            },
      testCase "openFunction produces FunctionDecl with isOpen = True" $
        openFunction "show" 1
          @?= FunctionDecl
            { name = "show",
              arity = 1,
              argTypes = Nothing,
              returnType = Nothing,
              isOpen = True,
              kind = DKFunction,
              requiring = Nothing
            },
      testCase "class_ produces FunctionDecl with kind = DKClass" $
        class_ "size" 1
          @?= FunctionDecl
            { name = "size",
              arity = 1,
              argTypes = Nothing,
              returnType = Nothing,
              isOpen = False,
              kind = DKClass,
              requiring = Nothing
            },
      testCase "openClass produces FunctionDecl with kind = DKClass and isOpen = True" $
        openClass "show" 1
          @?= FunctionDecl
            { name = "show",
              arity = 1,
              argTypes = Nothing,
              returnType = Nothing,
              isOpen = True,
              kind = DKClass,
              requiring = Nothing
            },
      testCase "extendClassType arity matches argTypes length" $
        let intCon = TypeCon (Unqualified "int") []
         in extendClassType "add" [intCon, intCon] intCon
              @?= ExtendClassTypeDecl
                { name = "add",
                  arity = 2,
                  argTypes = Just [intCon, intCon],
                  returnType = Just intCon,
                  target = Nothing
                },
      testCase "extendClassType with zero args is allowed" $
        let intCon = TypeCon (Unqualified "int") []
         in extendClassType "zero" [] intCon
              @?= ExtendClassTypeDecl
                { name = "zero",
                  arity = 0,
                  argTypes = Just [],
                  returnType = Just intCon,
                  target = Nothing
                }
    ]

typeDeclarationTests :: TestTree
typeDeclarationTests =
  testGroup
    "type declaration"
    [ testCase "typeExport with no allowlist" $
        typeExport "color" 0 @?= TypeExportDecl "color" 0 Nothing,
      testCase "typeExportWith carries the allowlist" $
        typeExportWith "color" 0 ["red", "green", "blue"]
          @?= TypeExportDecl "color" 0 (Just ["red", "green", "blue"]),
      testCase "typeExportWith with empty allowlist exports type only" $
        -- Empty list is distinct from Nothing: exports the type tag
        -- without any of its constructors.
        typeExportWith "opaque" 0 []
          @?= TypeExportDecl "opaque" 0 (Just []),
      testCase "tyDef with no type variables (mono-type)" $
        tyDef "color" [] [dataCtor "red" [], dataCtor "green" []]
          @?= TypeDefinition
            { name = Unqualified "color",
              typeVars = [],
              constructors =
                [ DataConstructor (Unqualified "red") [],
                  DataConstructor (Unqualified "green") []
                ],
              loc = dummyLoc
            },
      testCase "tyDef with type variables (parametric)" $
        -- The recursive 'list(a)' shape exercises both TypeVar (in cons
        -- field 0) and TypeCon-with-args (in cons field 1: list(a)).
        let listCon = TypeCon (Unqualified "list") [TypeVar "a"]
         in tyDef
              "list"
              ["a"]
              [ dataCtor "nil" [],
                dataCtor "cons" [TypeVar "a", listCon]
              ]
              @?= TypeDefinition
                { name = Unqualified "list",
                  typeVars = ["a"],
                  constructors =
                    [ DataConstructor (Unqualified "nil") [],
                      DataConstructor (Unqualified "cons") [TypeVar "a", listCon]
                    ],
                  loc = dummyLoc
                }
    ]

operatorDeclarationTests :: TestTree
operatorDeclarationTests =
  testGroup
    "operator declaration"
    [ testCase "op produces OperatorDecl with the given fixity and type" $
        op 700 Xfx "is"
          @?= OperatorDecl
            OpDecl {fixity = 700, opType = Xfx, opName = "is"},
      testCase "op accepts each fixity variant we expose" $
        -- Spot-check the four OpType variants that don't appear in
        -- existing tests; if one of them were ever removed, this would
        -- catch it.
        [ op 200 Fy "-",
          op 500 Yfx "+",
          op 400 Xfy ":-",
          op 700 Xfx "<"
        ]
          @?= [ OperatorDecl (OpDecl 200 Fy "-"),
                OperatorDecl (OpDecl 500 Yfx "+"),
                OperatorDecl (OpDecl 400 Xfy ":-"),
                OperatorDecl (OpDecl 700 Xfx "<")
              ]
    ]

ruleTests :: TestTree
ruleTests =
  testGroup
    "rule"
    [ testCase "(<=>): simplification rule" $
        [term "a" []] <=> [atom "true"]
          @?= Rule
            Nothing
            (noAnnP (Simplification [a0]))
            (noAnnP [])
            (noAnnP [atom "true"]),
      testCase "(==>): propagation rule" $
        [term "a" []] ==> [term "b" []]
          @?= Rule
            Nothing
            (noAnnP (Propagation [a0]))
            (noAnnP [])
            (noAnnP [term "b" []]),
      testCase "(\\): simpagation rule" $
        [term "k" []] \\ [term "r" []] <=> [atom "true"]
          @?= Rule
            Nothing
            ( noAnnP
                ( Simpagation
                    [Constraint (Unqualified "k") []]
                    [Constraint (Unqualified "r") []]
                )
            )
            (noAnnP [])
            (noAnnP [atom "true"]),
      testCase "(@:): sets rule name" $
        ("my_rule" @: ([term "a" []] <=> [atom "true"]))
          @?= Rule
            (Just (noAnn "my_rule"))
            (noAnnP (Simplification [a0]))
            (noAnnP [])
            (noAnnP [atom "true"]),
      testCase "(|-): sets rule guard" $
        (([term "a" [var "X"]] <=> [atom "true"]) |- [var "X" .=. atom "zero"])
          @?= Rule
            Nothing
            (noAnnP (Simplification [Constraint (Unqualified "a") [var "X"]]))
            (noAnnP [var "X" .=. atom "zero"])
            (noAnnP [atom "true"])
    ]
  where
    a0 = Constraint (Unqualified "a") []

guardTests :: TestTree
guardTests =
  testGroup
    "rule guard"
    [ testCase "(|-) attaches a single-conjunct guard" $
        (([term "p" [var "X"]] <=> [bool True]) |- [var "X" .> int 0])
          @?= Rule
            Nothing
            (noAnnP (Simplification [Constraint (Unqualified "p") [var "X"]]))
            (noAnnP [var "X" .> int 0])
            (noAnnP [bool True]),
      testCase "(|-) attaches a multi-conjunct guard" $
        -- The guard slot in 'Rule' is a list, so a list with multiple
        -- conjuncts is the surface form for @g1, g2, g3@. Pin that
        -- shape directly.
        ( ([term "p" [var "X"]] <=> [bool True])
            |- [var "X" .> int 0, var "X" .< int 100, var "X" .=. var "Y"]
        )
          @?= Rule
            Nothing
            (noAnnP (Simplification [Constraint (Unqualified "p") [var "X"]]))
            ( noAnnP
                [ var "X" .> int 0,
                  var "X" .< int 100,
                  var "X" .=. var "Y"
                ]
            )
            (noAnnP [bool True]),
      testCase "(|-) attaches a guard to a propagation rule" $
        ( ([term "p" [var "X"]] ==> [term "q" [var "X"]])
            |- [var "X" .> int 0]
        )
          @?= Rule
            Nothing
            (noAnnP (Propagation [Constraint (Unqualified "p") [var "X"]]))
            (noAnnP [var "X" .> int 0])
            (noAnnP [term "q" [var "X"]])
    ]

termTests :: TestTree
termTests =
  testGroup
    "term"
    [ testCase "var produces VarTerm" $
        var "X" @?= VarTerm "X",
      testCase "atom produces AtomTerm" $
        atom "true" @?= AtomTerm "true",
      testCase "term produces unqualified CompoundTerm" $
        term "f" [var "X"] @?= CompoundTerm (Unqualified "f") [var "X"],
      testCase "qterm produces qualified CompoundTerm" $
        qterm "Order" "leq" [var "X", var "Y"]
          @?= CompoundTerm (Qualified "Order" "leq") [VarTerm "X", VarTerm "Y"],
      testCase "qterm with zero arguments" $
        qterm "M" "marker" []
          @?= CompoundTerm (Qualified "M" "marker") [],
      testCase "(.=.) produces unification term" $
        var "X" .=. var "Y"
          @?= CompoundTerm (Unqualified "=") [VarTerm "X", VarTerm "Y"],
      testCase "hostCall produces host wrapper" $
        hostCall "print" [var "X"]
          @?= CompoundTerm (Qualified "host" "print") [VarTerm "X"],
      testCase "wildcard produces Wildcard" $
        wildcard @?= Wildcard,
      testCase "`is` produces is term" $
        var "X" `is` term "+" [int 1, int 2]
          @?= CompoundTerm
            (Unqualified "is")
            [VarTerm "X", CompoundTerm (Unqualified "+") [IntTerm 1, IntTerm 2]],
      -- Literal builders not yet exercised in their own test.
      testCase "int produces IntTerm" $
        int 42 @?= IntTerm 42,
      testCase "float produces FloatTerm" $
        float 1.5 @?= FloatTerm 1.5,
      testCase "text produces TextTerm" $
        text "hello" @?= TextTerm "hello",
      testCase "bool True maps to AtomTerm \"true\"" $
        bool True @?= AtomTerm "true",
      testCase "bool False maps to AtomTerm \"false\"" $
        bool False @?= AtomTerm "false"
    ]

lambdaTests :: TestTree
lambdaTests =
  testGroup
    "lambda and funRef"
    [ testCase "lambda builds the '->' compound shape" $
        -- A lambda is sugar for ->(fun(args), body); the AST shows
        -- both the params block and the body as siblings of '->'.
        lambda [var "X"] (var "X" .+ int 1)
          @?= CompoundTerm
            (Unqualified "->")
            [ CompoundTerm (Unqualified "fun") [VarTerm "X"],
              CompoundTerm (Unqualified "+") [VarTerm "X", IntTerm 1]
            ],
      testCase "lambda with multiple params" $
        lambda [var "X", var "Y"] (var "X" .+ var "Y")
          @?= CompoundTerm
            (Unqualified "->")
            [ CompoundTerm
                (Unqualified "fun")
                [VarTerm "X", VarTerm "Y"],
              CompoundTerm (Unqualified "+") [VarTerm "X", VarTerm "Y"]
            ],
      testCase "higher-order lambda: returning a lambda" $
        -- 'fun(X) -> fun(Y) -> X + Y end end' — a curried add. The
        -- outer body is itself a '->' compound.
        lambda [var "X"] (lambda [var "Y"] (var "X" .+ var "Y"))
          @?= CompoundTerm
            (Unqualified "->")
            [ CompoundTerm (Unqualified "fun") [VarTerm "X"],
              CompoundTerm
                (Unqualified "->")
                [ CompoundTerm (Unqualified "fun") [VarTerm "Y"],
                  CompoundTerm (Unqualified "+") [VarTerm "X", VarTerm "Y"]
                ]
            ],
      testCase "lambda with zero params" $
        lambda [] (int 42)
          @?= CompoundTerm
            (Unqualified "->")
            [ CompoundTerm (Unqualified "fun") [],
              IntTerm 42
            ],
      testCase "funRef builds fun(name/arity)" $
        funRef "factorial" 1
          @?= CompoundTerm
            (Unqualified "fun")
            [ CompoundTerm
                (Unqualified "/")
                [AtomTerm "factorial", IntTerm 1]
            ],
      testCase "call_ wraps args after the callable" $
        call_ (funRef "f" 2) [int 1, int 2]
          @?= CompoundTerm
            (Unqualified "$call")
            [ funRef "f" 2,
              IntTerm 1,
              IntTerm 2
            ],
      testCase "call_ on a lambda value" $
        call_ (lambda [var "X"] (var "X" .+ int 1)) [int 5]
          @?= CompoundTerm
            (Unqualified "$call")
            [ lambda [var "X"] (var "X" .+ int 1),
              IntTerm 5
            ]
    ]

numericInstanceTests :: TestTree
numericInstanceTests =
  testGroup
    "Num instance and comparison sugar"
    [ -- The 'Num' instance for 'Term' lets users write @1 + 2@ instead
      -- of @int 1 .+ int 2@; fromInteger and +/-/* must compile to the
      -- corresponding compound terms.
      testCase "fromInteger: literal 7 produces IntTerm 7" $
        (7 :: Term) @?= IntTerm 7,
      testCase "Num (+) builds '+' compound" $
        ((var "X" + int 1) :: Term)
          @?= CompoundTerm (Unqualified "+") [VarTerm "X", IntTerm 1],
      testCase "Num (-) builds '-' compound" $
        ((var "X" - int 1) :: Term)
          @?= CompoundTerm (Unqualified "-") [VarTerm "X", IntTerm 1],
      testCase "Num (*) builds '*' compound" $
        ((var "X" * int 2) :: Term)
          @?= CompoundTerm (Unqualified "*") [VarTerm "X", IntTerm 2],
      testCase "negate builds unary '-' compound" $
        negate (var "X") @?= CompoundTerm (Unqualified "-") [VarTerm "X"],
      testCase "abs builds 'abs' compound" $
        abs (var "X") @?= CompoundTerm (Unqualified "abs") [VarTerm "X"],
      testCase "signum builds 'sign' compound" $
        signum (var "X") @?= CompoundTerm (Unqualified "sign") [VarTerm "X"],
      -- Prefixed operators that bypass the Num machinery.
      testCase "(.+) (.-) (.*) (./) build the expected compounds" $
        [var "X" .+ int 1, var "X" .- int 1, var "X" .* int 2, var "X" ./ int 2]
          @?= [ CompoundTerm (Unqualified "+") [VarTerm "X", IntTerm 1],
                CompoundTerm (Unqualified "-") [VarTerm "X", IntTerm 1],
                CompoundTerm (Unqualified "*") [VarTerm "X", IntTerm 2],
                CompoundTerm (Unqualified "/") [VarTerm "X", IntTerm 2]
              ],
      -- Comparison sugar: each produces the surface operator name
      -- (note '.<=' renders as '=<', matching Prolog convention).
      testCase "comparison sugar builds correct compound names" $
        [ var "X" .< var "Y",
          var "X" .<= var "Y",
          var "X" .> var "Y",
          var "X" .>= var "Y",
          var "X" .== var "Y"
        ]
          @?= [ CompoundTerm (Unqualified "<") [VarTerm "X", VarTerm "Y"],
                CompoundTerm (Unqualified "=<") [VarTerm "X", VarTerm "Y"],
                CompoundTerm (Unqualified ">") [VarTerm "X", VarTerm "Y"],
                CompoundTerm (Unqualified ">=") [VarTerm "X", VarTerm "Y"],
                CompoundTerm (Unqualified "==") [VarTerm "X", VarTerm "Y"]
              ]
    ]

integrationTests :: TestTree
integrationTests =
  testGroup
    "integration"
    [ testCase "orderModule structure" $
        orderModule
          @?= Module
            { name = "Order",
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
                    (noAnnP [AtomTerm "true"])
                ],
              equations = [],
              extensions = [],
              classExtensions = [],
              exports = Nothing
            },
      testCase "logicModule structure" $
        logicModule
          @?= Module
            { name = "Logic",
              nameLoc = dummyLoc,
              imports = [noAnnP (ModuleImport "Order" Nothing)],
              decls = [],
              extensionTypes = [],
              typeDecls = [],
              rules =
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
                    ( noAnnP
                        [CompoundTerm (Unqualified "leq") [VarTerm "X", VarTerm "Z"]]
                    )
                ],
              equations = [],
              extensions = [],
              classExtensions = [],
              exports = Nothing
            }
    ]

--------------------------------------------------------------------------------
-- End-to-end: build with the DSL, compile, and run
--------------------------------------------------------------------------------

endToEndTests :: TestTree
endToEndTests =
  testGroup
    "endToEnd"
    [ leqEndToEnd,
      crossModuleEndToEnd,
      factorialEndToEnd,
      chrTypeEndToEnd,
      guardEndToEnd
    ]

-- | A full @leq@ handler exercising simplification, simpagation, and
-- propagation. Querying the reflexive case @leq(X, X)@ leaves @X@ unbound
-- (matches @test/golden/leq@).
leqEndToEnd :: TestTree
leqEndToEnd =
  testCase "leq: reflexivity collapses leq(X, X)" $ do
    let m =
          module' "order"
            `exporting` ["leq" // 2]
            `declaring` ["leq" // 2]
            `defining` [ "refl" @: [term "leq" [var "X", var "X"]] <=> [bool True],
                         "antisymm"
                           @: [term "leq" [var "X", var "Y"], term "leq" [var "Y", var "X"]]
                           <=> [var "X" .=. var "Y"],
                         "idemp"
                           @: [term "leq" [var "X", var "Y"]]
                           \\ [term "leq" [var "X", var "Y"]]
                           <=> [bool True],
                         "trans"
                           @: [term "leq" [var "X", var "Y"], term "leq" [var "Y", var "Z"]]
                           ==> [term "leq" [var "X", var "Z"]]
                       ]
    bindings <- runDSL [m] (term "leq" [var "X", var "X"])
    Map.keys bindings @?= ["X"]

-- | Two-module program. The library module @cross_lib@ exports a @double@
-- constraint; the main module @cross_main@ uses it to define @quadruple@.
-- Mirrors the @cross_module_import@ golden test.
crossModuleEndToEnd :: TestTree
crossModuleEndToEnd =
  testCase "cross-module: quadruple via cross_lib:double" $ do
    let lib =
          module' "cross_lib"
            `exporting` ["double" // 2]
            `declaring` ["double" // 2]
            `defining` [ [term "double" [var "X", var "R"]]
                           <=> [var "R" `is` (var "X" .* int 2)]
                       ]
        main_ =
          module' "cross_main"
            `importing` ["cross_lib"]
            `exporting` ["quadruple" // 2]
            `declaring` ["quadruple" // 2]
            `defining` [ [term "quadruple" [var "X", var "R"]]
                           <=> [ term "double" [var "X", var "Y"],
                                 term "double" [var "Y", var "R"]
                               ]
                       ]
    bindings <- runDSL [lib, main_] (term "quadruple" [int 7, var "R"])
    Map.lookup "R" bindings @?= Just (IntTerm 28)

-- | Function definition with multiple equations and recursion. Driven via a
-- @compute(R)@ constraint that calls @factorial(5)@ in its body.
factorialEndToEnd :: TestTree
factorialEndToEnd =
  testCase "factorial: function equations and recursion" $ do
    let m =
          module' "fact"
            `exporting` ["compute" // 1]
            `declaring` [ "compute" // 1,
                          function "factorial" 1
                        ]
            `withEquations` [ equation "factorial" [int 0] [] (int 1),
                              equation
                                "factorial"
                                [var "N"]
                                [var "N" .> int 0]
                                (var "N" .* call_ (funRef "factorial" 1) [var "N" .- int 1])
                            ]
            `defining` [ [term "compute" [var "R"]]
                           <=> [var "R" `is` call_ (funRef "factorial" 1) [int 5]]
                       ]
    bindings <- runDSL [m] (term "compute" [var "R"])
    Map.lookup "R" bindings @?= Just (IntTerm 120)

-- | Algebraic-type definition (@:- chr_type color ---> red ; green ; blue@).
-- The constraint @paint/1@ is declared with a typed argument; the rule simply
-- removes any @paint@ to verify the typed program compiles and runs.
chrTypeEndToEnd :: TestTree
chrTypeEndToEnd =
  testCase "chr_type color: typed constraint compiles and runs" $ do
    let m =
          module' "tc"
            `exporting` ["paint" // 1]
            `declaring` ["paint" // 1]
            `chrType` tyDef
              "color"
              []
              [ dataCtor "red" [],
                dataCtor "green" [],
                dataCtor "blue" []
              ]
            `defining` [[term "paint" [var "C"]] <=> [bool True]]
    bindings <- runDSL [m] (term "paint" [atom "red"])
    Map.keys bindings @?= []

-- | Simplification with a guard built from @is@ and @(.<)@. Mirrors the
-- @clamp@ shape of @test/golden/guard@: the low branch fires when @X < Lo@,
-- so @clamp(3, 5, R)@ binds @R = 5@.
guardEndToEnd :: TestTree
guardEndToEnd =
  testCase "guard: clamp(3, 5, R) → R = 5" $ do
    let m =
          module' "g"
            `exporting` ["clamp" // 3]
            `declaring` ["clamp" // 3]
            `defining` [ "low"
                           @: [term "clamp" [var "X", var "Lo", var "R"]]
                           <=> [var "R" .=. var "Lo"]
                           |- [var "X" .< var "Lo"],
                         "high"
                           @: [term "clamp" [var "X", var "Lo", var "R"]]
                           <=> [var "R" .=. var "X"]
                           |- [var "X" .>= var "Lo"]
                       ]
    bindings <- runDSL [m] (term "clamp" [int 3, int 5, var "R"])
    Map.lookup "R" bindings @?= Just (IntTerm 5)
