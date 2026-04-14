{-# LANGUAGE OverloadedStrings #-}

module YCHR.DSLTest (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import YCHR.DSL
import YCHR.Parsed
import YCHR.Types

tests :: TestTree
tests =
  testGroup
    "DSL"
    [ moduleTests,
      declarationTests,
      ruleTests,
      constraintTests,
      termTests,
      integrationTests
    ]

--------------------------------------------------------------------------------
-- Fixtures
--------------------------------------------------------------------------------

orderModule :: Module
orderModule =
  module' "Order"
    `declaring` ["leq" // 2]
    `defining` [ "refl" @: ([con "leq" [var "X", var "X"]] <=> [atom "true"])
               ]

logicModule :: Module
logicModule =
  module' "Logic"
    `importing` ["Order"]
    `defining` [ "trans"
                   @: ( [con "leq" [var "X", var "Y"], con "leq" [var "Y", var "Z"]]
                          ==> [func "leq" [var "X", var "Z"]]
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
        module' "Foo" @?= Module "Foo" [] [] [] [] [] Nothing,
      testCase "importing sets modImports" $
        module' "Foo" `importing` ["Bar", "Baz"]
          @?= Module "Foo" [noAnnP (ModuleImport "Bar"), noAnnP (ModuleImport "Baz")] [] [] [] [] Nothing,
      testCase "declaring sets modDecls" $
        module' "Foo" `declaring` ["leq" // 2]
          @?= Module "Foo" [] [noAnn (ConstraintDecl "leq" 2 Nothing)] [] [] [] Nothing,
      testCase "defining sets modRules" $
        let r = [con "leq" [var "X"]] <=> [atom "true"]
         in module' "Foo" `defining` [r]
              @?= Module "Foo" [] [] [] [r] [] Nothing,
      testCase "chaining importing, declaring, defining" $
        let r = [con "c" []] <=> [atom "true"]
         in module' "M"
              `importing` ["A"]
              `declaring` ["c" // 0]
              `defining` [r]
              @?= Module "M" [noAnnP (ModuleImport "A")] [noAnn (ConstraintDecl "c" 0 Nothing)] [] [r] [] Nothing,
      testCase "exporting sets modExports" $
        module' "Foo" `exporting` ["leq" // 2]
          @?= Module "Foo" [] [] [] [] [] (Just (noAnnP [ConstraintDecl "leq" 2 Nothing]))
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
        [con "a" []] <=> [atom "true"]
          @?= Rule Nothing (noAnnP (Simplification [con "a" []])) (noAnnP []) (noAnnP [atom "true"]),
      testCase "(==>): propagation rule" $
        [con "a" []] ==> [func "b" []]
          @?= Rule Nothing (noAnnP (Propagation [con "a" []])) (noAnnP []) (noAnnP [func "b" []]),
      testCase "(\\): simpagation rule" $
        ([con "k" []] \\ [con "r" []]) [atom "true"]
          @?= Rule Nothing (noAnnP (Simpagation [con "k" []] [con "r" []])) (noAnnP []) (noAnnP [atom "true"]),
      testCase "(@:): sets rule name" $
        "my_rule" @: ([con "a" []] <=> [atom "true"])
          @?= Rule (Just (noAnn "my_rule")) (noAnnP (Simplification [con "a" []])) (noAnnP []) (noAnnP [atom "true"]),
      testCase "(|-): sets rule guard" $
        ([con "a" [var "X"]] <=> [atom "true"]) |- [var "X" .=. atom "zero"]
          @?= Rule
            Nothing
            (noAnnP (Simplification [con "a" [var "X"]]))
            (noAnnP [var "X" .=. atom "zero"])
            (noAnnP [atom "true"])
    ]

constraintTests :: TestTree
constraintTests =
  testGroup
    "constraint"
    [ testCase "con produces Unqualified constraint" $
        con "leq" [var "X"] @?= Constraint (Unqualified "leq") [var "X"],
      testCase "(.:) qualifies an unqualified constraint" $
        "Mod" .: con "leq" [var "X"]
          @?= Constraint (Qualified "Mod" "leq") [var "X"],
      testCase "(.:) on already-qualified constraint is a no-op" $
        "Other" .: Constraint (Qualified "Mod" "leq") [var "X"]
          @?= Constraint (Qualified "Mod" "leq") [var "X"]
    ]

termTests :: TestTree
termTests =
  testGroup
    "term"
    [ testCase "var produces VarTerm" $
        var "X" @?= VarTerm "X",
      testCase "atom produces AtomTerm" $
        atom "true" @?= AtomTerm "true",
      testCase "func produces CompoundTerm" $
        func "f" [var "X"] @?= CompoundTerm (Unqualified "f") [var "X"],
      testCase "(.=.) produces unification term" $
        var "X" .=. var "Y"
          @?= CompoundTerm (Unqualified "=") [VarTerm "X", VarTerm "Y"],
      testCase "hostCall produces host wrapper" $
        hostCall "print" [var "X"]
          @?= CompoundTerm (Qualified "host" "print") [VarTerm "X"],
      testCase "wildcard produces Wildcard" $
        wildcard @?= Wildcard,
      testCase "`is` produces is term" $
        var "X" `is` func "+" [int 1, int 2]
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
            [ Rule
                (Just (noAnn "refl"))
                (noAnnP (Simplification [Constraint (Unqualified "leq") [VarTerm "X", VarTerm "X"]]))
                (noAnnP [])
                (noAnnP [AtomTerm "true"])
            ]
            []
            Nothing,
      testCase "logicModule structure" $
        logicModule
          @?= Module
            "Logic"
            [noAnnP (ModuleImport "Order")]
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
            Nothing
    ]
