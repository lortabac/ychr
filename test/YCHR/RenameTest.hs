module YCHR.RenameTest (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import YCHR.DSL
import YCHR.Parsed
import YCHR.Rename (RenameError (..), renameProgram)
import YCHR.Types

tests :: TestTree
tests =
  testGroup
    "Rename"
    [ sameModuleTests,
      importedTests,
      ambiguousTests,
      unknownTests,
      alreadyQualifiedTests,
      goalClassificationTests,
      headTypeTests,
      multiModuleTests,
      reservedSymbolTests
    ]

-- | Rename a single-module program and return the single renamed rule.
singleRule :: Module -> IO Rule
singleRule m = do
  renamed <- case renameProgram [m] of
    Right [r] -> return r
    Right mods -> assertFailure $ "expected 1 renamed module, got " ++ show (length mods)
    Left errs -> assertFailure $ "unexpected errors: " ++ show errs
  case modRules renamed of
    [rule] -> return rule
    rules -> assertFailure $ "expected 1 rule, got " ++ show (length rules)

--------------------------------------------------------------------------------
-- same-module: constraints declared in the current module get its qualifier
--------------------------------------------------------------------------------

sameModuleTests :: TestTree
sameModuleTests =
  testGroup
    "same-module"
    [ testCase "head constraint qualified with own module" $ do
        let m =
              module' "M"
                `declaring` ["leq" // 2]
                `defining` [[con "leq" [var "X", var "Y"]] <=> [atom "true"]]
        rule <- singleRule m
        ruleHead rule
          @?= Simplification [Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "Y"]],
      testCase "zero-arity constraint" $ do
        let m =
              module' "M"
                `declaring` ["done" // 0]
                `defining` [[con "done" []] <=> [atom "true"]]
        rule <- singleRule m
        ruleHead rule
          @?= Simplification [Constraint (Qualified "M" "done") []],
      testCase "body goal in own module" $ do
        let m =
              module' "M"
                `declaring` ["leq" // 2]
                `defining` [[con "leq" [var "X", var "Y"]] ==> [func "leq" [var "X", var "Z"]]]
        rule <- singleRule m
        ruleBody rule
          @?= [CompoundTerm (Qualified "M" "leq") [VarTerm "X", VarTerm "Z"]]
    ]

--------------------------------------------------------------------------------
-- imported: constraints from imported modules get the declaring module's qualifier
--------------------------------------------------------------------------------

importedTests :: TestTree
importedTests =
  testGroup
    "imported"
    [ testCase "head and body via import" $ do
        let modOrder = module' "Order" `declaring` ["leq" // 2]
            modLogic =
              module' "Logic"
                `importing` ["Order"]
                `defining` [ [con "leq" [var "X", var "Y"], con "leq" [var "Y", var "Z"]]
                               ==> [func "leq" [var "X", var "Z"]]
                           ]
        (_, renamedLogic) <- case renameProgram [modOrder, modLogic] of
          Right [a, b] -> return (a, b)
          Right mods -> assertFailure $ "expected 2 modules, got " ++ show (length mods)
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs
        rule <- case modRules renamedLogic of
          [r] -> return r
          rules -> assertFailure $ "expected 1 rule, got " ++ show (length rules)
        (ruleHead rule, ruleBody rule)
          @?= ( Propagation
                  [ Constraint (Qualified "Order" "leq") [VarTerm "X", VarTerm "Y"],
                    Constraint (Qualified "Order" "leq") [VarTerm "Y", VarTerm "Z"]
                  ],
                [CompoundTerm (Qualified "Order" "leq") [VarTerm "X", VarTerm "Z"]]
              ),
      testCase "imports are not transitive" $ do
        -- A declares leq/2; B imports A; C imports B (not A)
        -- C cannot see leq/2 because A is not in C's visible set
        let modA = module' "A" `declaring` ["leq" // 2]
            modB = module' "B" `importing` ["A"]
            modC =
              module' "C"
                `importing` ["B"]
                `defining` [[con "leq" [var "X", var "Y"]] <=> [atom "true"]]
        renameProgram [modA, modB, modC]
          @?= Left [UnknownName "leq" 2]
    ]

--------------------------------------------------------------------------------
-- ambiguous: multiple visible providers -> AmbiguousName error
--------------------------------------------------------------------------------

ambiguousTests :: TestTree
ambiguousTests =
  testGroup
    "ambiguous"
    [ testCase "own + imported both declare same name" $ do
        let modA = module' "A" `declaring` ["leq" // 2]
            modB =
              module' "B"
                `importing` ["A"]
                `declaring` ["leq" // 2]
                `defining` [[con "leq" [var "X", var "Y"]] <=> [atom "true"]]
        renameProgram [modA, modB]
          @?= Left [AmbiguousName "leq" 2 ["B", "A"]],
      testCase "two imports declare same name" $ do
        let modA = module' "A" `declaring` ["leq" // 2]
            modB = module' "B" `declaring` ["leq" // 2]
            modC =
              module' "C"
                `importing` ["A", "B"]
                `defining` [[con "leq" [var "X", var "Y"]] <=> [atom "true"]]
        case renameProgram [modA, modB, modC] of
          Left [AmbiguousName "leq" 2 _] -> pure ()
          other -> assertFailure $ "expected AmbiguousName error, got " ++ show other
    ]

--------------------------------------------------------------------------------
-- unknown: no visible provider -> UnknownName error
--------------------------------------------------------------------------------

unknownTests :: TestTree
unknownTests =
  testGroup
    "unknown"
    [ testCase "undeclared constraint" $ do
        let m =
              module' "M"
                `defining` [[con "foo" [var "X"]] <=> [atom "true"]]
        renameProgram [m]
          @?= Left [UnknownName "foo" 1],
      testCase "wrong arity" $ do
        -- leq/3 is declared but leq/2 is used: key ("leq",2) absent in env
        let m =
              module' "M"
                `declaring` ["leq" // 3]
                `defining` [[con "leq" [var "X", var "Y"]] <=> [atom "true"]]
        renameProgram [m]
          @?= Left [UnknownName "leq" 2],
      testCase "host call in body" $ do
        let m =
              module' "M"
                `declaring` ["c" // 0]
                `defining` [[con "c" []] <=> [hostStmt "some_host_func" [var "X"]]]
        rule <- singleRule m
        ruleBody rule
          @?= [CompoundTerm (Unqualified "$") [CompoundTerm (Unqualified "some_host_func") [VarTerm "X"]]]
    ]

--------------------------------------------------------------------------------
-- already-qualified: Qualified names pass through resolveName unchanged
--------------------------------------------------------------------------------

alreadyQualifiedTests :: TestTree
alreadyQualifiedTests =
  testGroup
    "already-qualified"
    [ testCase "pre-qualified head constraint passes through unchanged" $ do
        -- No declarations at all, but the constraint is pre-qualified
        let m =
              module' "M"
                `defining` [["Order" .: con "leq" [var "X", var "Y"]] <=> [atom "true"]]
        rule <- singleRule m
        ruleHead rule
          @?= Simplification [Constraint (Qualified "Order" "leq") [VarTerm "X", VarTerm "Y"]],
      testCase "pre-qualified survives ambiguity" $ do
        -- Two visible providers, but the constraint is already Qualified
        let modA = module' "A" `declaring` ["leq" // 2]
            modB = module' "B" `declaring` ["leq" // 2]
            modC =
              module' "C"
                `importing` ["A", "B"]
                `defining` [["A" .: con "leq" [var "X", var "Y"]] <=> [atom "true"]]
        renamedC <- case renameProgram [modA, modB, modC] of
          Right [_, _, c] -> return c
          Right mods -> assertFailure $ "expected 3 modules, got " ++ show (length mods)
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs
        rule <- case modRules renamedC of
          [r] -> return r
          rules -> assertFailure $ "expected 1 rule, got " ++ show (length rules)
        ruleHead rule
          @?= Simplification [Constraint (Qualified "A" "leq") [VarTerm "X", VarTerm "Y"]]
    ]

--------------------------------------------------------------------------------
-- goal-classification: isGoal controls whether compound terms are resolved
--------------------------------------------------------------------------------

goalClassificationTests :: TestTree
goalClassificationTests =
  testGroup
    "goal-classification"
    [ testCase "guard functor NOT resolved" $ do
        -- Guards use isGoal = False, so compound terms are not looked up
        let m =
              module' "M"
                `declaring` ["leq" // 2]
                `defining` [ ([con "leq" [var "X", var "Y"]] <=> [atom "true"])
                               |- [func "leq" [var "X", var "Y"]]
                           ]
        rule <- singleRule m
        ruleGuard rule
          @?= [CompoundTerm (Unqualified "leq") [VarTerm "X", VarTerm "Y"]],
      testCase "body functor IS resolved" $ do
        -- Body uses isGoal = True, so compound terms are looked up
        let m =
              module' "M"
                `declaring` ["leq" // 2]
                `defining` [[con "leq" [var "X", var "Y"]] ==> [func "leq" [var "X", var "Z"]]]
        rule <- singleRule m
        ruleBody rule
          @?= [CompoundTerm (Qualified "M" "leq") [VarTerm "X", VarTerm "Z"]],
      testCase "nested arg of head NOT resolved" $ do
        -- Head args use isGoal = False: inner functor stays Unqualified
        let m =
              module' "M"
                `declaring` ["wrap" // 1, "inner" // 1]
                `defining` [[con "wrap" [func "inner" [var "X"]]] <=> [atom "true"]]
        rule <- singleRule m
        ruleHead rule
          @?= Simplification
            [ Constraint
                (Qualified "M" "wrap")
                [CompoundTerm (Unqualified "inner") [VarTerm "X"]]
            ],
      testCase "nested arg of body goal NOT resolved" $ do
        -- Outer functor is resolved (isGoal = True), inner is not (args use isGoal = False)
        let m =
              module' "M"
                `declaring` ["c" // 0, "leq" // 1, "pair" // 1]
                `defining` [[con "c" []] ==> [func "leq" [func "pair" [var "X"]]]]
        rule <- singleRule m
        ruleBody rule
          @?= [CompoundTerm (Qualified "M" "leq") [CompoundTerm (Unqualified "pair") [VarTerm "X"]]],
      testCase "non-compound terms in guard untouched" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [ ([con "c" [var "X"]] <=> [atom "true"])
                               |- [var "X", atom "zero", IntTerm 42]
                           ]
        rule <- singleRule m
        ruleGuard rule
          @?= [VarTerm "X", AtomTerm "zero", IntTerm 42],
      testCase "non-compound terms in body untouched" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [[con "c" [var "X"]] <=> [var "X", atom "zero", IntTerm 42]]
        rule <- singleRule m
        ruleBody rule
          @?= [VarTerm "X", AtomTerm "zero", IntTerm 42]
    ]

--------------------------------------------------------------------------------
-- head-types: all three Head constructors are renamed
--------------------------------------------------------------------------------

headTypeTests :: TestTree
headTypeTests =
  testGroup
    "head-types"
    [ testCase "Propagation" $ do
        let m =
              module' "M"
                `declaring` ["leq" // 2]
                `defining` [[con "leq" [var "X", var "Y"]] ==> [atom "true"]]
        rule <- singleRule m
        ruleHead rule
          @?= Propagation [Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "Y"]],
      testCase "Simpagation kept and removed both renamed" $ do
        let m =
              module' "M"
                `declaring` ["leq" // 2, "gt" // 2]
                `defining` [ ([con "leq" [var "X", var "Y"]] \\ [con "gt" [var "X", var "Y"]])
                               [atom "true"]
                           ]
        rule <- singleRule m
        ruleHead rule
          @?= Simpagation
            [Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "Y"]]
            [Constraint (Qualified "M" "gt") [VarTerm "X", VarTerm "Y"]]
    ]

--------------------------------------------------------------------------------
-- multi-module: whole-program behavior and edge cases
--------------------------------------------------------------------------------

multiModuleTests :: TestTree
multiModuleTests =
  testGroup
    "multi-module"
    [ testCase "full two-module program" $ do
        let modOrder =
              module' "Order"
                `declaring` ["leq" // 2]
                `defining` ["refl" @: ([con "leq" [var "X", var "X"]] <=> [atom "true"])]
            modLogic =
              module' "Logic"
                `importing` ["Order"]
                `defining` [ "trans"
                               @: ( [con "leq" [var "X", var "Y"], con "leq" [var "Y", var "Z"]]
                                      ==> [func "leq" [var "X", var "Z"]]
                                  )
                           ]
        (renamedOrder, renamedLogic) <- case renameProgram [modOrder, modLogic] of
          Right [a, b] -> return (a, b)
          Right mods -> assertFailure $ "expected 2 modules, got " ++ show (length mods)
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs
        (modRules renamedOrder, modRules renamedLogic)
          @?= ( [ Rule
                    (Just "refl")
                    (Simplification [Constraint (Qualified "Order" "leq") [VarTerm "X", VarTerm "X"]])
                    []
                    [AtomTerm "true"]
                ],
                [ Rule
                    (Just "trans")
                    ( Propagation
                        [ Constraint (Qualified "Order" "leq") [VarTerm "X", VarTerm "Y"],
                          Constraint (Qualified "Order" "leq") [VarTerm "Y", VarTerm "Z"]
                        ]
                    )
                    []
                    [CompoundTerm (Qualified "Order" "leq") [VarTerm "X", VarTerm "Z"]]
                ]
              ),
      testCase "empty program" $
        renameProgram [] @?= Right [],
      testCase "module with no rules" $
        let m = module' "M" `declaring` ["leq" // 2]
         in renameProgram [m] @?= Right [Module "M" [] [ConstraintDecl "leq" 2] []],
      testCase "rule name preserved" $ do
        let m =
              module' "M"
                `declaring` ["c" // 0]
                `defining` ["my_rule" @: ([con "c" []] <=> [atom "true"])]
        rule <- singleRule m
        ruleName rule @?= Just "my_rule"
    ]

--------------------------------------------------------------------------------
-- reserved-symbols: =, ==, <- in body position remain Unqualified without error
--------------------------------------------------------------------------------

reservedSymbolTests :: TestTree
reservedSymbolTests =
  testGroup
    "reserved-symbols"
    [ testCase "= in body stays Unqualified" $ do
        let m =
              module' "M"
                `declaring` ["c" // 0]
                `defining` [[con "c" []] <=> [func "=" [var "X", var "Y"]]]
        rule <- singleRule m
        ruleBody rule
          @?= [CompoundTerm (Unqualified "=") [VarTerm "X", VarTerm "Y"]],
      testCase "== in body stays Unqualified" $ do
        let m =
              module' "M"
                `declaring` ["c" // 0]
                `defining` [[con "c" []] <=> [func "==" [var "X", var "Y"]]]
        rule <- singleRule m
        ruleBody rule
          @?= [CompoundTerm (Unqualified "==") [VarTerm "X", VarTerm "Y"]],
      testCase "<- in body stays Unqualified" $ do
        let m =
              module' "M"
                `declaring` ["c" // 0]
                `defining` [[con "c" []] <=> [func "<-" [var "X", var "Y"]]]
        rule <- singleRule m
        ruleBody rule
          @?= [CompoundTerm (Unqualified "<-") [VarTerm "X", VarTerm "Y"]],
      testCase "$ in body stays Unqualified" $ do
        let m =
              module' "M"
                `declaring` ["c" // 0]
                `defining` [[con "c" []] <=> [hostStmt "print" [var "X"]]]
        rule <- singleRule m
        ruleBody rule
          @?= [CompoundTerm (Unqualified "$") [CompoundTerm (Unqualified "print") [VarTerm "X"]]]
    ]
