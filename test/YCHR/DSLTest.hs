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
      ruleTests,
      termTests,
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
        module' "Foo" @?= Module "Foo" [] [] [] [] [] [] [] Nothing,
      testCase "importing sets modImports" $
        module' "Foo" `importing` ["Bar", "Baz"]
          @?= Module
            "Foo"
            [ noAnnP (ModuleImport "Bar" Nothing),
              noAnnP (ModuleImport "Baz" Nothing)
            ]
            []
            []
            []
            []
            []
            []
            Nothing,
      testCase "declaring sets modDecls" $
        module' "Foo" `declaring` ["leq" // 2]
          @?= Module "Foo" [] [noAnn (ConstraintDecl "leq" 2 Nothing)] [] [] [] [] [] Nothing,
      testCase "defining sets modRules" $
        let r = [term "leq" [var "X"]] <=> [atom "true"]
         in module' "Foo" `defining` [r]
              @?= Module "Foo" [] [] [] [] [r] [] [] Nothing,
      testCase "chaining importing, declaring, defining" $
        let r = [term "c" []] <=> [atom "true"]
         in module' "M"
              `importing` ["A"]
              `declaring` ["c" // 0]
              `defining` [r]
              @?= Module
                "M"
                [noAnnP (ModuleImport "A" Nothing)]
                [ noAnn
                    ( ConstraintDecl
                        "c"
                        0
                        Nothing
                    )
                ]
                []
                []
                [r]
                []
                []
                Nothing,
      testCase "exporting sets modExports" $
        module' "Foo" `exporting` ["leq" // 2]
          @?= Module
            "Foo"
            []
            []
            []
            []
            []
            []
            []
            (Just (noAnnP [ConstraintDecl "leq" 2 Nothing]))
    ]

declarationTests :: TestTree
declarationTests =
  testGroup
    "declaration"
    [ testCase "\"leq\" // 2 produces ConstraintDecl" $
        "leq" // 2 @?= ConstraintDecl "leq" 2 Nothing,
      testCase "\"foo\" // 0 produces ConstraintDecl with arity 0" $
        "foo" // 0 @?= ConstraintDecl "foo" 0 Nothing
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

termTests :: TestTree
termTests =
  testGroup
    "term"
    [ testCase "var produces VarTerm" $
        var "X" @?= VarTerm "X",
      testCase "atom produces AtomTerm" $
        atom "true" @?= AtomTerm "true",
      testCase "term produces CompoundTerm" $
        term "f" [var "X"] @?= CompoundTerm (Unqualified "f") [var "X"],
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
            [VarTerm "X", CompoundTerm (Unqualified "+") [IntTerm 1, IntTerm 2]]
    ]

integrationTests :: TestTree
integrationTests =
  testGroup
    "integration"
    [ testCase "orderModule structure" $
        orderModule
          @?= Module
            "Order"
            []
            [noAnn (ConstraintDecl "leq" 2 Nothing)]
            []
            []
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
                (noAnnP [AtomTerm "true"])
            ]
            []
            []
            Nothing,
      testCase "logicModule structure" $
        logicModule
          @?= Module
            "Logic"
            [noAnnP (ModuleImport "Order" Nothing)]
            []
            []
            []
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
            ]
            []
            []
            Nothing
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
