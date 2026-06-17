{-# LANGUAGE OverloadedStrings #-}

module YCHR.RenameTest (tests) where

import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import YCHR.DSL
import YCHR.Diagnostic (Diagnostic (..), noDiag)
import YCHR.PExpr (PExpr (Atom))
import YCHR.Parsed
import YCHR.Rename
  ( RenameError (..),
    RenameInputs (..),
    RenameWarning (..),
    defaultRenameInputs,
  )
import YCHR.Rename qualified as Rn

-- | Test-local wrapper that forwards to 'Rn.renameProgram' with empty
-- rename inputs (no operator-export map and no trailing-loc map). The
-- module-list-only signature keeps existing tests concise.
renameProgram ::
  [Module] ->
  Either
    [Diagnostic RenameError]
    ( [Module],
      [Diagnostic RenameWarning]
    )
renameProgram = Rn.renameProgram defaultRenameInputs

-- | Build an algebraic type definition positionally (the constructors
-- are wrapped in the 'Algebraic' 'TypeKind').
algebraicTD :: Name -> [Text] -> [DataConstructor] -> SourceLoc -> TypeDefinition
algebraicTD n vs cs loc = TypeDefinition n vs (Algebraic cs) loc

tests :: TestTree
tests =
  testGroup
    "Rename"
    [ sameModuleTests,
      importedTests,
      ambiguousTests,
      ambiguousDataConTests,
      unknownTests,
      alreadyQualifiedTests,
      goalClassificationTests,
      headTypeTests,
      multiModuleTests,
      reservedSymbolTests,
      exportTests,
      warningTests,
      importListTests
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
                `defining` [[term "leq" [var "X", var "Y"]] <=> [atom "true"]]
        rule <- singleRule m
        rule.head.node
          @?= Simplification [Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "Y"]],
      testCase "zero-arity constraint" $ do
        let m =
              module' "M"
                `declaring` ["done" // 0]
                `defining` [[term "done" []] <=> [atom "true"]]
        rule <- singleRule m
        rule.head.node
          @?= Simplification [Constraint (Qualified "M" "done") []],
      testCase "body goal in own module" $ do
        let m =
              module' "M"
                `declaring` ["leq" // 2]
                `defining` [ [term "leq" [var "X", var "Y"]]
                               ==> [term "leq" [var "X", var "Z"]]
                           ]
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
                `defining` [ [term "leq" [var "X", var "Y"], term "leq" [var "Y", var "Z"]]
                               ==> [term "leq" [var "X", var "Z"]]
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
                `defining` [[term "leq" [var "X", var "Y"]] <=> [atom "true"]]
        renameProgram [modA, modB, modC]
          @?= Left [noDiag (AnnP (UnknownName "leq" 2) dummyLoc (Atom ""))]
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
                `defining` [[term "leq" [var "X", var "Y"]] <=> [atom "true"]]
        renameProgram [modA, modB]
          @?= Left [noDiag (AnnP (AmbiguousName "leq" 2 ["B", "A"]) dummyLoc (Atom ""))],
      testCase "two imports declare same name" $ do
        let modA = module' "A" `declaring` ["leq" // 2]
            modB = module' "B" `declaring` ["leq" // 2]
            modC =
              module' "C"
                `importing` ["A", "B"]
                `defining` [[term "leq" [var "X", var "Y"]] <=> [atom "true"]]
        case renameProgram [modA, modB, modC] of
          Left [Diagnostic _ (AnnP (AmbiguousName "leq" 2 _) _ _)] -> pure ()
          other -> assertFailure $ "expected AmbiguousName error, got " ++ show other,
      testCase "ambiguous function used as a body-tell constraint argument" $ do
        -- The bare 'f(1)' lands in 'NoResolve' (demoted from the
        -- 'ResolveTop' parent 'c(...)'). Previously this was the silent
        -- 'otherwise -> pure ()' branch — 'Resolve.termToExpr' would
        -- fall through to 'CtorExpr' with no diagnostic at any stage.
        -- The renamer now mirrors 'resolveName''s multi-provider arm
        -- so the user gets the same YCHR-20001 diagnostic they would
        -- in a guard or 'is'-RHS position.
        let modA = module' "A" `declaring` [function "f" 1]
            modB = module' "B" `declaring` [function "f" 1]
            modC =
              module' "C"
                `importing` ["A", "B"]
                `declaring` ["c" // 1]
                `defining` [ [term "c" [var "X"]]
                               <=> [term "c" [term "f" [int 1]]]
                           ]
        case renameProgram [modA, modB, modC] of
          Left [Diagnostic _ (AnnP (AmbiguousName "f" 1 _) _ _)] -> pure ()
          other -> assertFailure $ "expected AmbiguousName error, got " ++ show other,
      testCase "ambiguous function on '=' operand" $ do
        -- '=' no longer has a special arm that routed operands to
        -- 'ResolveAll' (the lambda workaround). Operands inherit
        -- 'NoResolve' from the 'ResolveTop' body, so the multi-provider
        -- check has to live in 'NoResolve' itself; this case locks in
        -- that the diagnostic that the workaround used to surface still
        -- fires under the uniform path.
        let modA = module' "A" `declaring` [function "f" 1]
            modB = module' "B" `declaring` [function "f" 1]
            modC =
              module' "C"
                `importing` ["A", "B"]
                `declaring` ["c" // 1]
                `defining` [ [term "c" [var "X"]]
                               <=> [var "R" .=. term "f" [int 1]]
                           ]
        case renameProgram [modA, modB, modC] of
          Left [Diagnostic _ (AnnP (AmbiguousName "f" 1 _) _ _)] -> pure ()
          other -> assertFailure $ "expected AmbiguousName error, got " ++ show other,
      testCase "ambiguous compound nested inside a head-pattern argument" $ do
        -- The constraint functor itself (the outer 'c') resolves via
        -- 'renameCon' → 'resolveName ResolveTop', which has always
        -- diagnosed multi-provider. The compound /inside/ the head arg
        -- ('f(X)' below) is renamed in 'NoResolve' via 'renameTerm';
        -- previously that arm silently accepted multi-provider names.
        -- The 'NoResolve' multi-provider arm now diagnoses it.
        let modA = module' "A" `declaring` [function "f" 1]
            modB = module' "B" `declaring` [function "f" 1]
            modC =
              module' "C"
                `importing` ["A", "B"]
                `declaring` ["c" // 1]
                `defining` [ [term "c" [term "f" [var "X"]]]
                               <=> [atom "true"]
                           ]
        case renameProgram [modA, modB, modC] of
          Left [Diagnostic _ (AnnP (AmbiguousName "f" 1 _) _ _)] -> pure ()
          other -> assertFailure $ "expected AmbiguousName error, got " ++ show other,
      testCase "ambiguous compound in a function-equation pattern" $ do
        -- 'renameEquation' renames the equation's argument patterns in
        -- 'NoResolve'. A multi-provider name used as a pattern functor
        -- there has the same downstream gap (silent 'CtorExpr' fall-
        -- through) as in body-tell args; lock the diagnostic in.
        let modA = module' "A" `declaring` [function "f" 1]
            modB = module' "B" `declaring` [function "f" 1]
            modC =
              ( module' "C"
                  `importing` ["A", "B"]
                  `declaring` [function "g" 1]
              )
                `withEquations` [equation "g" [term "f" [var "X"]] [] (var "X")]
        case renameProgram [modA, modB, modC] of
          Left [Diagnostic _ (AnnP (AmbiguousName "f" 1 _) _ _)] -> pure ()
          other -> assertFailure $ "expected AmbiguousName error, got " ++ show other,
      testCase "ambiguous zero-arity atom in 'NoResolve' position" $ do
        -- Companion to the compound cases for the 'AtomTerm' arm.
        -- A bare 'f' inside a tell-side constraint argument lands in
        -- 'NoResolve'; if two modules export 'f/0' as a function, the
        -- atom arm now emits 'AmbiguousName' instead of silently
        -- producing an 'AtomTerm' that 'Resolve.termToExpr' can't
        -- disambiguate.
        let modA = module' "A" `declaring` [function "f" 0]
            modB = module' "B" `declaring` [function "f" 0]
            modC =
              module' "C"
                `importing` ["A", "B"]
                `declaring` ["c" // 1]
                `defining` [ [term "c" [var "X"]]
                               <=> [term "c" [atom "f"]]
                           ]
        case renameProgram [modA, modB, modC] of
          Left [Diagnostic _ (AnnP (AmbiguousName "f" 0 _) _ _)] -> pure ()
          other -> assertFailure $ "expected AmbiguousName error, got " ++ show other
    ]

--------------------------------------------------------------------------------
-- ambiguous data constructors: multiple visible providers ->
-- AmbiguousDataConstructor (YCHR-20012). Parallel to 'ambiguousTests'
-- but for the constructor namespace, which carries no arity (data
-- constructors are not arity-overloadable).
--------------------------------------------------------------------------------

ambiguousDataConTests :: TestTree
ambiguousDataConTests =
  testGroup
    "ambiguous data constructor"
    [ testCase "two imports both export a nullary constructor 'foo'" $ do
        let modA = modWithCtor "A" "foo" []
            modB = modWithCtor "B" "foo" []
            modC =
              ( module' "C"
                  `importing` ["A", "B"]
                  `declaring` ["r" // 1]
                  `defining` [[term "r" [var "R"]] <=> [var "R" .=. atom "foo"]]
              )
        case renameProgram [modA, modB, modC] of
          Left [Diagnostic _ (AnnP (AmbiguousDataConstructor "foo" _) _ _)] ->
            pure ()
          other ->
            assertFailure $
              "expected AmbiguousDataConstructor error, got " ++ show other,
      testCase "two imports both export a unary constructor 'foo'" $ do
        let modA = modWithCtor "A" "foo" [TypeCon (Unqualified "int") []]
            modB = modWithCtor "B" "foo" [TypeCon (Unqualified "int") []]
            modC =
              ( module' "C"
                  `importing` ["A", "B"]
                  `declaring` ["r" // 1]
                  `defining` [ [term "r" [var "R"]]
                                 <=> [var "R" .=. term "foo" [IntTerm 42]]
                             ]
              )
        case renameProgram [modA, modB, modC] of
          Left [Diagnostic _ (AnnP (AmbiguousDataConstructor "foo" _) _ _)] ->
            pure ()
          other ->
            assertFailure $
              "expected AmbiguousDataConstructor error, got " ++ show other
    ]
  where
    -- Empty module that declares a single type @t/0@ with one
    -- constructor @ctor@ at the given argument shape.
    modWithCtor modName ctor argTypes =
      (module' modName)
        { typeDecls =
            [ noAnn
                ( algebraicTD
                    (Unqualified "t")
                    []
                    [DataConstructor (Unqualified ctor) argTypes]
                    dummyLoc
                )
            ]
        }

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
                `defining` [[term "foo" [var "X"]] <=> [atom "true"]]
        renameProgram [m]
          @?= Left [noDiag (AnnP (UnknownName "foo" 1) dummyLoc (Atom ""))],
      testCase "wrong arity" $ do
        -- leq/3 is declared but leq/2 is used: key ("leq",2) absent in env
        let m =
              module' "M"
                `declaring` ["leq" // 3]
                `defining` [[term "leq" [var "X", var "Y"]] <=> [atom "true"]]
        renameProgram [m]
          @?= Left [noDiag (AnnP (UnknownName "leq" 2) dummyLoc (Atom ""))],
      testCase "host call in body" $ do
        let m =
              module' "M"
                `declaring` ["c" // 0]
                `defining` [[term "c" []] <=> [hostCall "some_host_func" [var "X"]]]
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
                `defining` [[qterm "Order" "leq" [var "X", var "Y"]] <=> [atom "true"]]
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
                `defining` [[qterm "Order" "leq" [var "X", var "Y"]] <=> [atom "true"]]
        renameProgram [m]
          @?= Left [noDiag (AnnP (NotExportedByModule "Order" "leq" 2) dummyLoc (Atom ""))],
      testCase "pre-qualified survives ambiguity" $ do
        -- Two visible providers, but the constraint is already Qualified
        let modA = module' "A" `declaring` ["leq" // 2]
            modB = module' "B" `declaring` ["leq" // 2]
            modC =
              module' "C"
                `importing` ["A", "B"]
                `defining` [[qterm "A" "leq" [var "X", var "Y"]] <=> [atom "true"]]
        renamedC <- case renameProgram [modA, modB, modC] of
          Right ([_, _, c], _) -> return c
          Right (mods, _) -> assertFailure $ "expected 3 modules, got " ++ show (length mods)
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs
        rule <- case renamedC.rules of
          [r] -> return r
          rules -> assertFailure $ "expected 1 rule, got " ++ show (length rules)
        rule.head.node
          @?= Simplification [Constraint (Qualified "A" "leq") [VarTerm "X", VarTerm "Y"]],
      testCase "pre-qualified reference to non-imported module is rejected" $ do
        -- A declares leq/2 but B does not import A; the qualification
        -- must not silently bypass the visibility rules.
        let modA = module' "A" `declaring` ["leq" // 2]
            modB =
              module' "B"
                `defining` [[qterm "A" "leq" [var "X", var "Y"]] <=> [atom "true"]]
        renameProgram [modA, modB]
          @?= Left [noDiag (AnnP (NotExportedByModule "A" "leq" 2) dummyLoc (Atom ""))],
      testCase "pre-qualified reference to non-exported name is rejected" $ do
        -- A declares leq/2 and gt/2 but only exports leq/2. B imports A
        -- and tries to reach gt/2 via qualification; still hidden.
        let modA =
              module' "A"
                `declaring` ["leq" // 2, "gt" // 2]
                `exporting` ["leq" // 2]
            modB =
              module' "B"
                `importing` ["A"]
                `defining` [[qterm "A" "gt" [var "X", var "Y"]] <=> [atom "true"]]
        renameProgram [modA, modB]
          @?= Left [noDiag (AnnP (NotExportedByModule "A" "gt" 2) dummyLoc (Atom ""))]
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
                `defining` [ ([term "leq" [var "X", var "Y"]] <=> [atom "true"])
                               |- [term "leq" [var "X", var "Y"]]
                           ]
        rule <- singleRule m
        rule.guard.node
          @?= [CompoundTerm (Qualified "M" "leq") [VarTerm "X", VarTerm "Y"]],
      testCase "body functor IS resolved" $ do
        -- Body uses isGoal = True, so compound terms are looked up
        let m =
              module' "M"
                `declaring` ["leq" // 2]
                `defining` [ [term "leq" [var "X", var "Y"]]
                               ==> [term "leq" [var "X", var "Z"]]
                           ]
        rule <- singleRule m
        rule.body.node
          @?= [CompoundTerm (Qualified "M" "leq") [VarTerm "X", VarTerm "Z"]],
      testCase "nested arg of head NOT resolved" $ do
        -- Head args use isGoal = False: inner functor stays Unqualified
        let m =
              module' "M"
                `declaring` ["wrap" // 1, "inner" // 1]
                `defining` [[term "wrap" [term "inner" [var "X"]]] <=> [atom "true"]]
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
                `defining` [[term "c" []] ==> [term "leq" [term "pair" [var "X"]]]]
        rule <- singleRule m
        rule.body.node
          @?= [ CompoundTerm
                  (Qualified "M" "leq")
                  [ CompoundTerm
                      (Unqualified "pair")
                      [ VarTerm
                          "X"
                      ]
                  ]
              ],
      testCase "unknown functor in guard stays Unqualified (data constructor)" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [ ([term "c" [var "X"]] <=> [atom "true"])
                               |- [term "." [var "H", var "T"]]
                           ]
        rule <- singleRule m
        rule.guard.node
          @?= [CompoundTerm (Unqualified ".") [VarTerm "H", VarTerm "T"]],
      testCase "unknown functor in is RHS stays Unqualified (data constructor)" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [ [term "c" [var "X"]]
                               <=> [var "R" `is` term "pair" [var "X", int 1]]
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
                `defining` [ ([term "c" [var "X"]] <=> [atom "true"])
                               |- [var "X", atom "zero", IntTerm 42]
                           ]
        rule <- singleRule m
        rule.guard.node
          @?= [VarTerm "X", CompoundTerm (Unqualified "zero") [], IntTerm 42],
      testCase "non-compound terms in body untouched" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [[term "c" [var "X"]] <=> [var "X", atom "zero", IntTerm 42]]
        rule <- singleRule m
        rule.body.node
          @?= [VarTerm "X", CompoundTerm (Unqualified "zero") [], IntTerm 42],
      testCase "zero-arity atom in body promoted to constraint" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1, "done" // 0]
                `defining` [[term "c" [var "X"]] <=> [atom "done"]]
        rule <- singleRule m
        rule.body.node
          @?= [CompoundTerm (Qualified "M" "done") []],
      testCase "zero-arity atom in guard promoted to constraint" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1, "ready" // 0]
                `defining` [ ([term "c" [var "X"]] <=> [atom "true"])
                               |- [atom "ready"]
                           ]
        rule <- singleRule m
        rule.guard.node
          @?= [CompoundTerm (Qualified "M" "ready") []],
      testCase "undeclared atom in body stays as AtomTerm" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [[term "c" [var "X"]] <=> [atom "hello"]]
        rule <- singleRule m
        rule.body.node
          @?= [CompoundTerm (Unqualified "hello") []],
      testCase "undeclared atom in guard stays as AtomTerm" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [ ([term "c" [var "X"]] <=> [atom "true"])
                               |- [atom "hello"]
                           ]
        rule <- singleRule m
        rule.guard.node
          @?= [CompoundTerm (Unqualified "hello") []],
      testCase "zero-arity atom in head arg stays as AtomTerm (NoResolve)" $ do
        let m =
              module' "M"
                `declaring` ["c" // 1, "done" // 0]
                `defining` [[term "c" [atom "done"]] <=> [atom "true"]]
        rule <- singleRule m
        rule.head.node
          @?= Simplification
            [ Constraint
                (Qualified "M" "c")
                [CompoundTerm (Unqualified "done") []]
            ]
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
                `defining` [[term "leq" [var "X", var "Y"]] ==> [atom "true"]]
        rule <- singleRule m
        rule.head.node
          @?= Propagation [Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "Y"]],
      testCase "Simpagation kept and removed both renamed" $ do
        let m =
              module' "M"
                `declaring` ["leq" // 2, "gt" // 2]
                `defining` [ [term "leq" [var "X", var "Y"]]
                               \\ [term "gt" [var "X", var "Y"]]
                               <=> [atom "true"]
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
                `defining` ["refl" @: ([term "leq" [var "X", var "X"]] <=> [atom "true"])]
            modLogic =
              module' "Logic"
                `importing` ["Order"]
                `defining` [ "trans"
                               @: ( [ term "leq" [var "X", var "Y"],
                                      term "leq" [var "Y", var "Z"]
                                    ]
                                      ==> [term "leq" [var "X", var "Z"]]
                                  )
                           ]
        (renamedOrder, renamedLogic) <- case renameProgram [modOrder, modLogic] of
          Right ([a, b], _) -> return (a, b)
          Right (mods, _) -> assertFailure $ "expected 2 modules, got " ++ show (length mods)
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs
        (renamedOrder.rules, renamedLogic.rules)
          @?= ( [ Rule
                    (Just (noAnn "refl"))
                    ( noAnnP
                        ( Simplification
                            [ Constraint
                                (Qualified "Order" "leq")
                                [ VarTerm "X",
                                  VarTerm "X"
                                ]
                            ]
                        )
                    )
                    (noAnnP [])
                    (noAnnP [CompoundTerm (Unqualified "true") []])
                ],
                [ Rule
                    (Just (noAnn "trans"))
                    ( noAnnP
                        ( Propagation
                            [ Constraint (Qualified "Order" "leq") [VarTerm "X", VarTerm "Y"],
                              Constraint (Qualified "Order" "leq") [VarTerm "Y", VarTerm "Z"]
                            ]
                        )
                    )
                    (noAnnP [])
                    ( noAnnP
                        [ CompoundTerm
                            (Qualified "Order" "leq")
                            [ VarTerm "X",
                              VarTerm "Z"
                            ]
                        ]
                    )
                ]
              ),
      testCase "empty program" $
        renameProgram [] @?= Right ([], []),
      testCase "module with no rules" $
        let m = module' "M" `declaring` ["leq" // 2]
         in renameProgram [m]
              @?= Right
                ( [ Module
                      { name = "M",
                        nameLoc = dummyLoc,
                        imports = [],
                        decls = [noAnn (ConstraintDecl "leq" 2 Nothing Nothing)],
                        extensionTypes = [],
                        typeDecls = [],
                        rules = [],
                        equations = [],
                        extensions = [],
                        classExtensions = [],
                        exports = Nothing
                      }
                  ],
                  []
                ),
      testCase "rule name preserved" $ do
        let m =
              module' "M"
                `declaring` ["c" // 0]
                `defining` ["my_rule" @: ([term "c" []] <=> [atom "true"])]
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
                `defining` [[term "c" []] <=> [term "=" [var "X", var "Y"]]]
        rule <- singleRule m
        rule.body.node
          @?= [CompoundTerm (Unqualified "=") [VarTerm "X", VarTerm "Y"]],
      testCase "host:f in body stays Qualified host" $ do
        let m =
              module' "M"
                `declaring` ["c" // 0]
                `defining` [[term "c" []] <=> [hostCall "print" [var "X"]]]
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
                `defining` [[term "leq" [var "X", var "Y"]] <=> [atom "true"]]
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
                `defining` [[term "gt" [var "X", var "Y"]] <=> [atom "true"]]
        renameProgram [modA, modB]
          @?= Left [noDiag (AnnP (UnknownName "gt" 2) dummyLoc (Atom ""))],
      testCase "empty export list hides all constraints from importer" $ do
        -- A exports nothing; B cannot see leq/2
        let modA =
              module' "A"
                `declaring` ["leq" // 2]
                `exporting` []
            modB =
              module' "B"
                `importing` ["A"]
                `defining` [[term "leq" [var "X", var "Y"]] <=> [atom "true"]]
        renameProgram [modA, modB]
          @?= Left [noDiag (AnnP (UnknownName "leq" 2) dummyLoc (Atom ""))],
      testCase "export restriction does not affect own-module use" $ do
        -- A exports only leq/2, but still uses gt/2 in its own rules
        let modA =
              module' "A"
                `declaring` ["leq" // 2, "gt" // 2]
                `exporting` ["leq" // 2]
                `defining` [[term "gt" [var "X", var "Y"]] <=> [atom "true"]]
        rule <- singleRule modA
        rule.head.node
          @?= Simplification [Constraint (Qualified "A" "gt") [VarTerm "X", VarTerm "Y"]],
      testCase "no module directive exports all constraints" $ do
        -- A has modExports = Nothing (no directive); B can see all of A's constraints
        let modA = module' "A" `declaring` ["leq" // 2]
            modB =
              module' "B"
                `importing` ["A"]
                `defining` [[term "leq" [var "X", var "Y"]] <=> [atom "true"]]
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
        renameProgram [m]
          @?= Left
            [ noDiag
                ( AnnP
                    (UnknownExport "M" "foo" 1)
                    dummyLoc
                    ( Atom
                        ""
                    )
                )
            ],
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
warningsOf :: [Module] -> IO [Diagnostic RenameWarning]
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
                `defining` [[term "c" [var "X"]] <=> [atom "true"] |- [term "foo" [var "X"]]]
        ws <- warningsOf [m]
        ws @?= [noDiag (AnnP (UndeclaredDataConstructor "foo") dummyLoc (Atom ""))],
      testCase "declared data constructor produces no warning" $ do
        let m =
              ( module' "M"
                  `declaring` ["c" // 1]
                  `defining` [ [term "c" [var "X"]]
                                 <=> [ atom
                                         "true"
                                     ]
                                 |- [term "foo" [var "X"]]
                             ]
              )
                { typeDecls =
                    [ noAnn
                        ( algebraicTD
                            (Unqualified "t")
                            []
                            [ DataConstructor
                                (Unqualified "foo")
                                [TypeCon (Unqualified "int") []]
                            ]
                            dummyLoc
                        )
                    ]
                }
        ws <- warningsOf [m]
        ws @?= [],
      testCase "declared function in tell-side argument position produces no warning" $ do
        -- Regression: a bare compound like 'f(X)' appearing as an argument
        -- to a tell-side constraint is renamed in 'NoResolve' mode but
        -- must not be warned as a data constructor when 'f' is a visible
        -- function -- 'Resolve.termToExpr' will later canonicalize it to
        -- a 'CallExpr' for tell-time evaluation.
        let m =
              module' "M"
                `declaring` ["c" // 1, function "f" 1]
                `defining` [ [term "c" [var "X"]]
                               <=> [atom "true"]
                               |- [term "c" [term "f" [var "X"]]]
                           ]
        ws <- warningsOf [m]
        ws @?= [],
      testCase "data constructor arity mismatch" $ do
        let m =
              ( module' "M"
                  `declaring` ["c" // 1]
                  `defining` [ [term "c" [var "X"]]
                                 <=> [ atom
                                         "true"
                                     ]
                                 |- [term "foo" [var "X", var "X"]]
                             ]
              )
                { typeDecls =
                    [ noAnn
                        ( algebraicTD
                            (Unqualified "t")
                            []
                            [ DataConstructor
                                (Unqualified "foo")
                                [TypeCon (Unqualified "int") []]
                            ]
                            dummyLoc
                        )
                    ]
                }
        ws <- warningsOf [m]
        ws @?= [noDiag (AnnP (DataConstructorArityMismatch "foo" 2) dummyLoc (Atom ""))],
      testCase "no warning for reserved symbols" $ do
        let m =
              module' "M"
                `declaring` ["c" // 2]
                `defining` [[term "c" [var "X", var "Y"]] <=> [var "X" .=. var "Y"]]
        ws <- warningsOf [m]
        ws @?= [],
      testCase "warns on unknown data constructor in NoResolve mode (head arguments)" $ do
        -- Per the user's "warn everywhere" choice, the renamer now emits
        -- 'UndeclaredDataConstructor' for unknown atoms/compounds in head
        -- pattern position too (previously only resolving contexts warned).
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [[term "c" [term "unknown" [var "X"]]] <=> [atom "true"]]
        ws <- warningsOf [m]
        ws @?= [noDiag (AnnP (UndeclaredDataConstructor "unknown") dummyLoc (Atom ""))],
      testCase "no warning inside term(...) quoting in body position" $ do
        -- Regression for the BUGS.md case 'store(term(plus(X, 3)))': the
        -- term/1 quoting form should keep its argument opaque, so neither
        -- 'term' itself nor any undeclared functor inside should produce
        -- an 'UndeclaredDataConstructor' warning.
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [ [term "c" [var "X"]]
                               <=> [term "c" [term "term" [term "plus" [var "X", int 3]]]]
                           ]
        ws <- warningsOf [m]
        ws @?= [],
      testCase "no warning inside term(...) quoting in guard position" $ do
        -- The quoting form must also stay opaque in expression-position
        -- contexts (guards, is-RHS), where the surrounding mode is
        -- 'ResolveAll' rather than 'NoResolve'.
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [ [term "c" [var "X"]]
                               <=> [atom "true"]
                               |- [term "term" [term "plus" [var "X", int 3]]]
                           ]
        ws <- warningsOf [m]
        ws @?= [],
      testCase "no warning inside nested term(term(...)) quoting" $ do
        -- Quoting nests: the inner 'term(...)' must also fire the
        -- special case (childMode propagates 'NoResolveQuoted'), so no
        -- warning is emitted for the inner functor either.
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [ [term "c" [var "X"]]
                               <=> [ term
                                       "c"
                                       [ term
                                           "term"
                                           [term "term" [term "plus" [var "X", int 3]]]
                                       ]
                                   ]
                           ]
        ws <- warningsOf [m]
        ws @?= [],
      testCase "syntactic forms stay literal inside term(...) quoting" $ do
        -- 'is', lambdas, and 'fun name/arity' references are interpreted
        -- only outside @term/1@. Inside a quoted body they must remain
        -- literal compound terms — no warning for their undeclared inner
        -- functors either.
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [ [term "c" [var "X"]]
                               <=> [ term
                                       "c"
                                       [ term
                                           "term"
                                           [term "is" [var "X", term "foo" [int 1]]]
                                       ]
                                   ]
                           ]
        ws <- warningsOf [m]
        ws @?= [],
      testCase "lambda passed directly as a tell-side constraint argument is not warned" $ do
        -- Regression for BUGS.md "Spurious 'Undeclared data constructor'
        -- warnings for 'fun' and '->'". A lambda is a first-class value;
        -- its synthetic '->' and 'fun' functors are surface syntax, not
        -- data constructors. Previously the renamer demoted the
        -- constraint's argument to 'NoResolve', the lambda arm's
        -- 'isResolving' guard failed, and the synthetic functors leaked
        -- through to 'warnUnknownDataCon'. The lambda body is a bare
        -- variable so the test isolates the surface-syntax bug without
        -- pulling in prelude functions that this minimal DSL module
        -- doesn't import.
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [ [term "c" [var "X"]]
                               <=> [term "c" [lambda [var "Y"] (var "Y")]]
                           ]
        ws <- warningsOf [m]
        ws @?= [],
      testCase "lambda bound via '=' then passed is not warned" $ do
        -- The bind-then-pass form ('F = fun(...) -> ... end, c(F)') was
        -- the documented workaround for the lambda bug. Now that the
        -- lambda arm fires in every non-quoted mode, the workaround on
        -- '=' itself was removed; this case verifies the bind-then-pass
        -- form still produces no spurious warnings under the simplified
        -- pipeline.
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [ [term "c" [var "X"]]
                               <=> [ var "F" .=. lambda [var "Y"] (var "Y"),
                                     term "c" [var "F"]
                                   ]
                           ]
        ws <- warningsOf [m]
        ws @?= [],
      testCase "function reference passed directly as constraint argument is not warned" $ do
        -- Same structural bug as the lambda case, on the @fun name/arity@
        -- arm: a funref is a first-class value, not data. Previously
        -- 'c(fun f/1)' would emit a spurious 'UndeclaredDataConstructor
        -- "fun"' under 'NoResolve'.
        let m =
              module' "M"
                `declaring` ["c" // 1, function "f" 1]
                `defining` [ [term "c" [var "X"]]
                               <=> [term "c" [funRef "f" 1]]
                           ]
        ws <- warningsOf [m]
        ws @?= [],
      testCase "lambda inside term(...) stays opaque" $ do
        -- Negative companion to the lambda fix: 'term(fun(X) -> X end)'
        -- must NOT be recognized as a lambda (the user has explicitly
        -- opted into raw compound shape). The relaxed lambda guard
        -- skips 'NoResolveQuoted' for exactly this reason; this case
        -- locks that contract in.
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [ [term "c" [var "X"]]
                               <=> [term "c" [term "term" [lambda [var "Y"] (var "Y")]]]
                           ]
        ws <- warningsOf [m]
        ws @?= [],
      testCase "funref inside term(...) stays opaque" $ do
        -- Funref counterpart to the lambda-inside-term/1 case. The
        -- relaxed funref guard ('mode /= NoResolveQuoted') means a
        -- funref outside 'term/1' resolves; inside 'term/1' it must
        -- remain a literal compound. 'f' is *not* declared as a
        -- function in this module, so if the funref arm fired
        -- 'resolveName' would emit an UnknownName error and the
        -- compile would fail — the program rename-succeeds only
        -- because the funref arm correctly skips 'NoResolveQuoted'.
        let m =
              module' "M"
                `declaring` ["c" // 1]
                `defining` [ [term "c" [var "X"]]
                               <=> [term "c" [term "term" [funRef "f" 1]]]
                           ]
        ws <- warningsOf [m]
        ws @?= [],
      testCase "exporting undeclared type produces error" $ do
        let m = (module' "M") {exports = Just (noAnnP [TypeExportDecl "tree" 0 Nothing])}
        renameProgram [m]
          @?= Left
            [ noDiag
                ( AnnP
                    (UnknownExport "M" "tree" 0)
                    dummyLoc
                    ( Atom
                        ""
                    )
                )
            ],
      testCase "exporting declared type is fine" $ do
        let m =
              (module' "M")
                { typeDecls =
                    [ noAnn
                        ( algebraicTD
                            (Unqualified "tree")
                            []
                            [ DataConstructor
                                (Unqualified "empty")
                                []
                            ]
                            dummyLoc
                        )
                    ],
                  exports = Just (noAnnP [TypeExportDecl "tree" 0 Nothing])
                }
        case renameProgram [m] of
          Right _ -> pure ()
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs,
      testCase "type definition names are qualified after renaming" $ do
        let m =
              (module' "M")
                { typeDecls =
                    [ noAnn
                        ( algebraicTD
                            (Unqualified "tree")
                            []
                            [ DataConstructor
                                (Unqualified "leaf")
                                [TypeCon (Unqualified "int") []]
                            ]
                            dummyLoc
                        )
                    ]
                }
        case renameProgram [m] of
          Right ([renamed], _) -> case renamed.typeDecls of
            [Ann td _] -> do
              td.name @?= Qualified "M" "tree"
              case typeConstructors td of
                [dc] -> dc.conName @?= Qualified "M" "leaf"
                dcs -> assertFailure $ "expected 1 constructor, got " ++ show (length dcs)
            tds -> assertFailure $ "expected 1 type decl, got " ++ show (length tds)
          Right (mods, _) -> assertFailure $ "expected 1 module, got " ++ show (length mods)
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs,
      testCase "type references resolved across modules" $ do
        let modA =
              (module' "A")
                { typeDecls =
                    [ noAnn
                        ( algebraicTD
                            (Unqualified "color")
                            []
                            [ DataConstructor
                                (Unqualified "red")
                                []
                            ]
                            dummyLoc
                        )
                    ]
                }
            modB =
              (module' "B" `importing` ["A"])
                { typeDecls =
                    [ noAnn
                        ( algebraicTD
                            (Unqualified "widget")
                            []
                            [ DataConstructor
                                (Unqualified "w")
                                [ TypeCon
                                    (Unqualified "color")
                                    []
                                ]
                            ]
                            dummyLoc
                        )
                    ]
                }
        case renameProgram [modA, modB] of
          Right ([_, renamedB], _) -> case renamedB.typeDecls of
            [Ann td _] -> case typeConstructors td of
              [dc] -> case dc.conArgs of
                [TypeCon colorName []] -> colorName @?= Qualified "A" "color"
                args -> assertFailure $ "unexpected constructor args: " ++ show args
              dcs -> assertFailure $ "expected 1 constructor, got " ++ show (length dcs)
            tds -> assertFailure $ "expected 1 type decl, got " ++ show (length tds)
          Right (mods, _) -> assertFailure $ "expected 2 modules, got " ++ show (length mods)
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs
    ]

--------------------------------------------------------------------------------
-- import lists: use_module/2 restricts visibility
--------------------------------------------------------------------------------

importListTests :: TestTree
importListTests =
  testGroup
    "import lists"
    [ testCase "name in import list is visible" $ do
        let modOrder =
              module' "Order"
                `declaring` ["leq" // 2, "geq" // 2]
                `exporting` ["leq" // 2, "geq" // 2]
            modLogic =
              (module' "Logic")
                { imports =
                    [ noAnnP
                        ( ModuleImport
                            "Order"
                            ( Just
                                [ ConstraintDecl
                                    "leq"
                                    2
                                    Nothing
                                    Nothing
                                ]
                            )
                        )
                    ]
                }
                `defining` [[term "leq" [var "X", var "Y"]] <=> [atom "true"]]
        case renameProgram [modOrder, modLogic] of
          Right ([_, renamedLogic], _) -> case renamedLogic.rules of
            [rule] ->
              rule.head.node
                @?= Simplification
                  [ Constraint
                      (Qualified "Order" "leq")
                      [ VarTerm "X",
                        VarTerm "Y"
                      ]
                  ]
            rules -> assertFailure $ "expected 1 rule, got " ++ show (length rules)
          Right (mods, _) -> assertFailure $ "expected 2 modules, got " ++ show (length mods)
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs,
      testCase "name NOT in import list is not resolved" $ do
        let modOrder =
              module' "Order"
                `declaring` ["leq" // 2, "geq" // 2]
                `exporting` ["leq" // 2, "geq" // 2]
            modLogic =
              (module' "Logic")
                { imports =
                    [ noAnnP
                        ( ModuleImport
                            "Order"
                            ( Just
                                [ ConstraintDecl
                                    "geq"
                                    2
                                    Nothing
                                    Nothing
                                ]
                            )
                        )
                    ]
                }
                `defining` [[term "leq" [var "X", var "Y"]] <=> [atom "true"]]
        renameProgram [modOrder, modLogic]
          @?= Left [noDiag (AnnP (UnknownName "leq" 2) dummyLoc (Atom ""))],
      testCase "error for import list item not exported" $ do
        let modOrder =
              module' "Order"
                `declaring` ["leq" // 2]
                `exporting` ["leq" // 2]
            modLogic =
              (module' "Logic")
                { imports =
                    [ noAnnP
                        ( ModuleImport
                            "Order"
                            ( Just
                                [ ConstraintDecl
                                    "nonexistent"
                                    1
                                    Nothing
                                    Nothing
                                ]
                            )
                        )
                    ]
                }
        renameProgram [modOrder, modLogic]
          @?= Left [noDiag (AnnP (UnknownImport "Order" "nonexistent" 1) dummyLoc (Atom ""))],
      testCase "operator in import list is accepted when source module exports it" $ do
        let modOrder =
              module' "Order"
                `declaring` ["leq" // 2]
                `exporting` ["leq" // 2]
            modLogic =
              (module' "Logic")
                { imports =
                    [ noAnnP
                        ( ModuleImport
                            "Order"
                            ( Just
                                [ OperatorDecl
                                    ( OpDecl
                                        700
                                        Xfx
                                        "==="
                                    )
                                ]
                            )
                        )
                    ]
                }
            inputs =
              defaultRenameInputs
                { operatorExports = Map.fromList [("Order", [OpDecl 700 Xfx "==="])]
                }
        case Rn.renameProgram inputs [modOrder, modLogic] of
          Right _ -> pure ()
          Left errs -> assertFailure $ "unexpected errors: " ++ show errs,
      testCase "operator in import list is rejected when source module does not export it" $ do
        let modOrder =
              module' "Order"
                `declaring` ["leq" // 2]
                `exporting` ["leq" // 2]
            modLogic =
              (module' "Logic")
                { imports =
                    [ noAnnP
                        ( ModuleImport
                            "Order"
                            ( Just
                                [ OperatorDecl
                                    ( OpDecl
                                        700
                                        Xfx
                                        "==="
                                    )
                                ]
                            )
                        )
                    ]
                }
        renameProgram [modOrder, modLogic]
          @?= Left [noDiag (AnnP (UnknownOperatorImport "Order" "===") dummyLoc (Atom ""))],
      testCase "use_module after non-import directive is reported as out-of-order" $ do
        let modOrder =
              module' "Order"
                `declaring` ["leq" // 2]
                `exporting` ["leq" // 2]
            -- Synthesise an import located after the recorded trailingLoc.
            misplacedLoc = SourceLoc "test.chr" 10 1
            modLogic =
              (module' "Logic")
                { imports = [AnnP (ModuleImport "Order" Nothing) misplacedLoc (Atom "")]
                }
            inputs =
              defaultRenameInputs
                { trailingLoc = Map.fromList [("Logic", Just (SourceLoc "test.chr" 5 1))]
                }
        case Rn.renameProgram inputs [modOrder, modLogic] of
          Left errs ->
            any
              ( \(Diagnostic _ (AnnP e _ _)) -> case e of
                  UseModuleOutOfOrder "Order" -> True
                  _ -> False
              )
              errs
              @?= True
          Right _ -> assertFailure "expected UseModuleOutOfOrder error",
      testCase "import of unknown type with constructor list reports one UnknownImport" $ do
        -- Regression: `type(missing/0, [c1, c2])` against a module that
        -- doesn't declare `missing` used to fire one UnknownImport plus
        -- one UnknownExportedConstructor per listed constructor.
        let modLib =
              module' "Lib"
                `declaring` ["leq" // 2]
                `exporting` ["leq" // 2]
            modUser =
              (module' "User")
                { imports =
                    [ noAnnP
                        ( ModuleImport
                            "Lib"
                            (Just [TypeExportDecl "missing" 0 (Just ["c1", "c2"])])
                        )
                    ]
                }
        renameProgram [modLib, modUser]
          @?= Left
            [noDiag (AnnP (UnknownImport "Lib" "missing" 0) dummyLoc (Atom ""))]
    ]
