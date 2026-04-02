{-# LANGUAGE OverloadedStrings #-}

module YCHR.RenameTest (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import YCHR.DSL
import YCHR.Parsed
import YCHR.Rename (RenameError (..), RenameWarning (..), renameProgram)
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
      reservedSymbolTests,
      exportTests,
      warningTests
    ]

-- | Rename a single-module program and return the single renamed rule.
singleRule :: Module -> IO Rule
singleRule m = do
  renamed <- case renameProgram [m] of
    Right ([r], _) -> return r
    Right (mods, _) -> assertFailure $ "expected 1 renamed module, got " ++ show (length mods)
    Left errs -> assertFailure $ "unexpected errors: " ++ show errs
  case renamed.rules of
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
        rule.head.node
          @?= Simplification [Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "Y"]],
      testCase "zero-arity constraint" $ do
        let m =
              module' "M"
                `declaring` ["done" // 0]
                `defining` [[con "done" []] <=> [atom "true"]]
        rule <- singleRule m
        rule.head.node
          @?= Simplification [Constraint (Qualified "M" "done") []],
      testCase "body goal in own module" $ do
        let m =
              module' "M"
                `declaring` ["leq" // 2]
                `defining` [[con "leq" [var "X", var "Y"]] ==> [func "leq" [var "X", var "Z"]]]
        rule <- singleRule m
        rule.body.node
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
          Right ([a, b], _) -> return (a, b)
          Right (mods, _) -> assertFailure $ "expected 2 modules, got " ++ show (length mods)
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs
        rule <- case renamedLogic.rules of
          [r] -> return r
          rules -> assertFailure $ "expected 1 rule, got " ++ show (length rules)
        (rule.head.node, rule.body.node)
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
          @?= Left [UnknownName dummyLoc "leq" 2]
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
          @?= Left [AmbiguousName dummyLoc "leq" 2 ["B", "A"]],
      testCase "two imports declare same name" $ do
        let modA = module' "A" `declaring` ["leq" // 2]
            modB = module' "B" `declaring` ["leq" // 2]
            modC =
              module' "C"
                `importing` ["A", "B"]
                `defining` [[con "leq" [var "X", var "Y"]] <=> [atom "true"]]
        case renameProgram [modA, modB, modC] of
          Left [AmbiguousName _ "leq" 2 _] -> pure ()
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
          @?= Left [UnknownName dummyLoc "foo" 1],
      testCase "wrong arity" $ do
        -- leq/3 is declared but leq/2 is used: key ("leq",2) absent in env
        let m =
              module' "M"
                `declaring` ["leq" // 3]
                `defining` [[con "leq" [var "X", var "Y"]] <=> [atom "true"]]
        renameProgram [m]
          @?= Left [UnknownName dummyLoc "leq" 2],
      testCase "host call in body" $ do
        let m =
              module' "M"
                `declaring` ["c" // 0]
                `defining` [[con "c" []] <=> [hostCall "some_host_func" [var "X"]]]
        rule <- singleRule m
        rule.body.node
          @?= [CompoundTerm (Qualified "host" "some_host_func") [VarTerm "X"]]
    ]

--------------------------------------------------------------------------------
-- already-qualified: Qualified names pass through resolveName unchanged
--------------------------------------------------------------------------------

alreadyQualifiedTests :: TestTree
alreadyQualifiedTests =
  testGroup
    "already-qualified"
    [ testCase "pre-qualified head constraint passes through unchanged" $ do
        let modOrder = module' "Order" `declaring` ["leq" // 2]
            modM =
              module' "M"
                `importing` ["Order"]
                `defining` [["Order" .: con "leq" [var "X", var "Y"]] <=> [atom "true"]]
        (_, renamedM) <- case renameProgram [modOrder, modM] of
          Right ([a, b], _) -> return (a, b)
          Right (mods, _) -> assertFailure $ "expected 2 modules, got " ++ show (length mods)
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs
        rule <- case renamedM.rules of
          [r] -> return r
          rules -> assertFailure $ "expected 1 rule, got " ++ show (length rules)
        rule.head.node
          @?= Simplification [Constraint (Qualified "Order" "leq") [VarTerm "X", VarTerm "Y"]],
      testCase "pre-qualified undeclared constraint produces error" $ do
        let m =
              module' "M"
                `defining` [["Order" .: con "leq" [var "X", var "Y"]] <=> [atom "true"]]
        renameProgram [m]
          @?= Left [UnknownName dummyLoc "leq" 2],
      testCase "pre-qualified survives ambiguity" $ do
        -- Two visible providers, but the constraint is already Qualified
        let modA = module' "A" `declaring` ["leq" // 2]
            modB = module' "B" `declaring` ["leq" // 2]
            modC =
              module' "C"
                `importing` ["A", "B"]
                `defining` [["A" .: con "leq" [var "X", var "Y"]] <=> [atom "true"]]
        renamedC <- case renameProgram [modA, modB, modC] of
          Right ([_, _, c], _) -> return c
          Right (mods, _) -> assertFailure $ "expected 3 modules, got " ++ show (length mods)
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs
        rule <- case renamedC.rules of
          [r] -> return r
          rules -> assertFailure $ "expected 1 rule, got " ++ show (length rules)
        rule.head.node
          @?= Simplification [Constraint (Qualified "A" "leq") [VarTerm "X", VarTerm "Y"]]
    ]

--------------------------------------------------------------------------------
-- goal-classification: isGoal controls whether compound terms are resolved
--------------------------------------------------------------------------------

goalClassificationTests :: TestTree
goalClassificationTests =
  testGroup
    "goal-classification"
    [ testCase "guard functor IS resolved" $ do
        -- Guards use ResolveAll, so compound terms are looked up
        let m =
              module' "M"
                `declaring` ["leq" // 2]
                `defining` [ ([con "leq" [var "X", var "Y"]] <=> [atom "true"])
                               |- [func "leq" [var "X", var "Y"]]
                           ]
        rule <- singleRule m
        rule.guard.node
          @?= [CompoundTerm (Qualified "M" "leq") [VarTerm "X", VarTerm "Y"]],
      testCase "body functor IS resolved" $ do
        -- Body uses isGoal = True, so compound terms are looked up
        let m =
              module' "M"
                `declaring` ["leq" // 2]
                `defining` [[con "leq" [var "X", var "Y"]] ==> [func "leq" [var "X", var "Z"]]]
        rule <- singleRule m
        rule.body.node
          @?= [CompoundTerm (Qualified "M" "leq") [VarTerm "X", VarTerm "Z"]],
      testCase "nested arg of head NOT resolved" $ do
        -- Head args use isGoal = False: inner functor stays Unqualified
        let m =
              module' "M"
                `declaring` ["wrap" // 1, "inner" // 1]
                `defining` [[con "wrap" [func "inner" [var "X"]]] <=> [atom "true"]]
        rule <- singleRule m
        rule.head.node
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
        rule.body.node
          @?= [CompoundTerm (Qualified "M" "leq") [CompoundTerm (Unqualified "pair") [VarTerm "X"]]],
      testCase "unknown functor in guard stays Unqualified (data constructor)" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [ ([con "c" [var "X"]] <=> [atom "true"])
                               |- [func "." [var "H", var "T"]]
                           ]
        rule <- singleRule m
        rule.guard.node
          @?= [CompoundTerm (Unqualified ".") [VarTerm "H", VarTerm "T"]],
      testCase "unknown functor in is RHS stays Unqualified (data constructor)" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [ [con "c" [var "X"]]
                               <=> [var "R" `is` func "pair" [var "X", int 1]]
                           ]
        rule <- singleRule m
        rule.body.node
          @?= [ CompoundTerm
                  (Unqualified "is")
                  [VarTerm "R", CompoundTerm (Unqualified "pair") [VarTerm "X", IntTerm 1]]
              ],
      testCase "non-compound terms in guard untouched" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [ ([con "c" [var "X"]] <=> [atom "true"])
                               |- [var "X", atom "zero", IntTerm 42]
                           ]
        rule <- singleRule m
        rule.guard.node
          @?= [VarTerm "X", AtomTerm "zero", IntTerm 42],
      testCase "non-compound terms in body untouched" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [[con "c" [var "X"]] <=> [var "X", atom "zero", IntTerm 42]]
        rule <- singleRule m
        rule.body.node
          @?= [VarTerm "X", AtomTerm "zero", IntTerm 42],
      testCase "zero-arity atom in body promoted to constraint" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1, "done" // 0]
                `defining` [[con "c" [var "X"]] <=> [atom "done"]]
        rule <- singleRule m
        rule.body.node
          @?= [CompoundTerm (Qualified "M" "done") []],
      testCase "zero-arity atom in guard promoted to constraint" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1, "ready" // 0]
                `defining` [ ([con "c" [var "X"]] <=> [atom "true"])
                               |- [atom "ready"]
                           ]
        rule <- singleRule m
        rule.guard.node
          @?= [CompoundTerm (Qualified "M" "ready") []],
      testCase "undeclared atom in body stays as AtomTerm" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [[con "c" [var "X"]] <=> [atom "hello"]]
        rule <- singleRule m
        rule.body.node
          @?= [AtomTerm "hello"],
      testCase "undeclared atom in guard stays as AtomTerm" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [ ([con "c" [var "X"]] <=> [atom "true"])
                               |- [atom "hello"]
                           ]
        rule <- singleRule m
        rule.guard.node
          @?= [AtomTerm "hello"],
      testCase "zero-arity atom in head arg stays as AtomTerm (NoResolve)" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1, "done" // 0]
                `defining` [[con "c" [atom "done"]] <=> [atom "true"]]
        rule <- singleRule m
        rule.head.node
          @?= Simplification [Constraint (Qualified "M" "c") [AtomTerm "done"]]
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
        rule.head.node
          @?= Propagation [Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "Y"]],
      testCase "Simpagation kept and removed both renamed" $ do
        let m =
              module' "M"
                `declaring` ["leq" // 2, "gt" // 2]
                `defining` [ ([con "leq" [var "X", var "Y"]] \\ [con "gt" [var "X", var "Y"]])
                               [atom "true"]
                           ]
        rule <- singleRule m
        rule.head.node
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
          Right ([a, b], _) -> return (a, b)
          Right (mods, _) -> assertFailure $ "expected 2 modules, got " ++ show (length mods)
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs
        (renamedOrder.rules, renamedLogic.rules)
          @?= ( [ Rule
                    (Just (noAnn "refl"))
                    (noAnn (Simplification [Constraint (Qualified "Order" "leq") [VarTerm "X", VarTerm "X"]]))
                    (noAnn [])
                    (noAnn [AtomTerm "true"])
                ],
                [ Rule
                    (Just (noAnn "trans"))
                    ( noAnn
                        ( Propagation
                            [ Constraint (Qualified "Order" "leq") [VarTerm "X", VarTerm "Y"],
                              Constraint (Qualified "Order" "leq") [VarTerm "Y", VarTerm "Z"]
                            ]
                        )
                    )
                    (noAnn [])
                    (noAnn [CompoundTerm (Qualified "Order" "leq") [VarTerm "X", VarTerm "Z"]])
                ]
              ),
      testCase "empty program" $
        renameProgram [] @?= Right ([], []),
      testCase "module with no rules" $
        let m = module' "M" `declaring` ["leq" // 2]
         in renameProgram [m] @?= Right ([Module "M" [] [noAnn (ConstraintDecl "leq" 2 Nothing)] [] [] [] Nothing], []),
      testCase "rule name preserved" $ do
        let m =
              module' "M"
                `declaring` ["c" // 0]
                `defining` ["my_rule" @: ([con "c" []] <=> [atom "true"])]
        rule <- singleRule m
        fmap (.node) rule.name @?= Just "my_rule"
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
        rule.body.node
          @?= [CompoundTerm (Unqualified "=") [VarTerm "X", VarTerm "Y"]],
      testCase "host:f in body stays Qualified host" $ do
        let m =
              module' "M"
                `declaring` ["c" // 0]
                `defining` [[con "c" []] <=> [hostCall "print" [var "X"]]]
        rule <- singleRule m
        rule.body.node
          @?= [CompoundTerm (Qualified "host" "print") [VarTerm "X"]]
    ]

--------------------------------------------------------------------------------
-- exports: export list controls visibility to importers
--------------------------------------------------------------------------------

exportTests :: TestTree
exportTests =
  testGroup
    "exports"
    [ testCase "exported constraint is visible to importer" $ do
        -- A exports leq/2; B imports A and uses leq in head
        let modA =
              module' "A"
                `declaring` ["leq" // 2]
                `exporting` ["leq" // 2]
            modB =
              module' "B"
                `importing` ["A"]
                `defining` [[con "leq" [var "X", var "Y"]] <=> [atom "true"]]
        (_, renamedB) <- case renameProgram [modA, modB] of
          Right ([a, b], _) -> return (a, b)
          Right (mods, _) -> assertFailure $ "expected 2 modules, got " ++ show (length mods)
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs
        rule <- case renamedB.rules of
          [r] -> return r
          rules -> assertFailure $ "expected 1 rule, got " ++ show (length rules)
        rule.head.node
          @?= Simplification [Constraint (Qualified "A" "leq") [VarTerm "X", VarTerm "Y"]],
      testCase "non-exported constraint is hidden from importer" $ do
        -- A declares leq/2 and gt/2 but only exports leq/2; B can't see gt/2
        let modA =
              module' "A"
                `declaring` ["leq" // 2, "gt" // 2]
                `exporting` ["leq" // 2]
            modB =
              module' "B"
                `importing` ["A"]
                `defining` [[con "gt" [var "X", var "Y"]] <=> [atom "true"]]
        renameProgram [modA, modB]
          @?= Left [UnknownName dummyLoc "gt" 2],
      testCase "empty export list hides all constraints from importer" $ do
        -- A exports nothing; B cannot see leq/2
        let modA =
              module' "A"
                `declaring` ["leq" // 2]
                `exporting` []
            modB =
              module' "B"
                `importing` ["A"]
                `defining` [[con "leq" [var "X", var "Y"]] <=> [atom "true"]]
        renameProgram [modA, modB]
          @?= Left [UnknownName dummyLoc "leq" 2],
      testCase "export restriction does not affect own-module use" $ do
        -- A exports only leq/2, but still uses gt/2 in its own rules
        let modA =
              module' "A"
                `declaring` ["leq" // 2, "gt" // 2]
                `exporting` ["leq" // 2]
                `defining` [[con "gt" [var "X", var "Y"]] <=> [atom "true"]]
        rule <- singleRule modA
        rule.head.node
          @?= Simplification [Constraint (Qualified "A" "gt") [VarTerm "X", VarTerm "Y"]],
      testCase "no module directive exports all constraints" $ do
        -- A has modExports = Nothing (no directive); B can see all of A's constraints
        let modA = module' "A" `declaring` ["leq" // 2]
            modB =
              module' "B"
                `importing` ["A"]
                `defining` [[con "leq" [var "X", var "Y"]] <=> [atom "true"]]
        (_, renamedB) <- case renameProgram [modA, modB] of
          Right ([a, b], _) -> return (a, b)
          Right (mods, _) -> assertFailure $ "expected 2 modules, got " ++ show (length mods)
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs
        rule <- case renamedB.rules of
          [r] -> return r
          rules -> assertFailure $ "expected 1 rule, got " ++ show (length rules)
        rule.head.node
          @?= Simplification [Constraint (Qualified "A" "leq") [VarTerm "X", VarTerm "Y"]],
      testCase "exporting undeclared name produces error" $ do
        let m = module' "M" `exporting` ["foo" // 1]
        renameProgram [m] @?= Left [UnknownExport "M" "foo" 1],
      testCase "exporting declared constraint is fine" $ do
        let m =
              module' "M"
                `declaring` ["foo" // 1]
                `exporting` ["foo" // 1]
        case renameProgram [m] of
          Right _ -> pure ()
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs
    ]

-- ---------------------------------------------------------------------------
-- Warnings
-- ---------------------------------------------------------------------------

-- | Rename a program and return the warnings (failing on errors).
warningsOf :: [Module] -> IO [RenameWarning]
warningsOf mods = case renameProgram mods of
  Right (_, ws) -> pure ws
  Left errs -> assertFailure $ "unexpected errors: " ++ show errs

warningTests :: TestTree
warningTests =
  testGroup
    "warnings"
    [ testCase "undeclared data constructor in guard" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [[con "c" [var "X"]] <=> [atom "true"] |- [func "foo" [var "X"]]]
        ws <- warningsOf [m]
        ws @?= [UndeclaredDataConstructor dummyLoc "foo"],
      testCase "declared data constructor produces no warning" $ do
        let m =
              (module' "M" `declaring` ["c" // 1] `defining` [[con "c" [var "X"]] <=> [atom "true"] |- [func "foo" [var "X"]]])
                { typeDecls = [noAnn (TypeDefinition (Unqualified "t") [] [DataConstructor (Unqualified "foo") [TypeCon (Unqualified "int") []]])]
                }
        ws <- warningsOf [m]
        ws @?= [],
      testCase "data constructor arity mismatch" $ do
        let m =
              (module' "M" `declaring` ["c" // 1] `defining` [[con "c" [var "X"]] <=> [atom "true"] |- [func "foo" [var "X", var "X"]]])
                { typeDecls = [noAnn (TypeDefinition (Unqualified "t") [] [DataConstructor (Unqualified "foo") [TypeCon (Unqualified "int") []]])]
                }
        ws <- warningsOf [m]
        ws @?= [DataConstructorArityMismatch dummyLoc "foo" 2],
      testCase "no warning for reserved symbols" $ do
        let m =
              module' "M"
                `declaring` ["c" // 2]
                `defining` [[con "c" [var "X", var "Y"]] <=> [var "X" .=. var "Y"]]
        ws <- warningsOf [m]
        ws @?= [],
      testCase "no warning in NoResolve mode (head arguments)" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [[con "c" [func "unknown" [var "X"]]] <=> [atom "true"]]
        ws <- warningsOf [m]
        ws @?= [],
      testCase "exporting undeclared type produces error" $ do
        let m = (module' "M") {exports = Just [TypeExportDecl "tree" 0]}
        renameProgram [m] @?= Left [UnknownExport "M" "tree" 0],
      testCase "exporting declared type is fine" $ do
        let m =
              (module' "M")
                { typeDecls = [noAnn (TypeDefinition (Unqualified "tree") [] [DataConstructor (Unqualified "empty") []])],
                  exports = Just [TypeExportDecl "tree" 0]
                }
        case renameProgram [m] of
          Right _ -> pure ()
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs,
      testCase "type definition names are qualified after renaming" $ do
        let m =
              (module' "M")
                { typeDecls = [noAnn (TypeDefinition (Unqualified "tree") [] [DataConstructor (Unqualified "leaf") [TypeCon (Unqualified "int") []]])]
                }
        case renameProgram [m] of
          Right ([renamed], _) -> case renamed.typeDecls of
            [Ann td _] -> do
              td.name @?= Qualified "M" "tree"
              case td.constructors of
                [dc] -> dc.conName @?= Qualified "M" "leaf"
                dcs -> assertFailure $ "expected 1 constructor, got " ++ show (length dcs)
            tds -> assertFailure $ "expected 1 type decl, got " ++ show (length tds)
          Right (mods, _) -> assertFailure $ "expected 1 module, got " ++ show (length mods)
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs,
      testCase "type references resolved across modules" $ do
        let modA =
              (module' "A")
                { typeDecls = [noAnn (TypeDefinition (Unqualified "color") [] [DataConstructor (Unqualified "red") []])]
                }
            modB =
              (module' "B" `importing` ["A"])
                { typeDecls = [noAnn (TypeDefinition (Unqualified "widget") [] [DataConstructor (Unqualified "w") [TypeCon (Unqualified "color") []]])]
                }
        case renameProgram [modA, modB] of
          Right ([_, renamedB], _) -> case renamedB.typeDecls of
            [Ann td _] -> case td.constructors of
              [dc] -> case dc.conArgs of
                [TypeCon colorName []] -> colorName @?= Qualified "A" "color"
                args -> assertFailure $ "unexpected constructor args: " ++ show args
              dcs -> assertFailure $ "expected 1 constructor, got " ++ show (length dcs)
            tds -> assertFailure $ "expected 1 type decl, got " ++ show (length tds)
          Right (mods, _) -> assertFailure $ "expected 2 modules, got " ++ show (length mods)
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs
    ]
