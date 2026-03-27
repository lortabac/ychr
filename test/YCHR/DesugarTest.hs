{-# LANGUAGE OverloadedStrings #-}

module YCHR.DesugarTest (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import YCHR.DSL
import YCHR.Desugar (DesugarError (..), desugarProgram, extractSymbolTable)
import YCHR.Desugared qualified as D
import YCHR.Parsed
import YCHR.Types (ConstraintType (..), Name (..), lookupSymbol, mkSymbolTable, symbolTableSize)

tests :: TestTree
tests =
  testGroup
    "Desugar"
    [ headTests,
      hnfTests,
      guardTests,
      bodyTests,
      errorTests,
      flatteningTests,
      ruleNameTests,
      symbolTableTests
    ]

desugar :: [Module] -> IO D.Program
desugar mods = case desugarProgram mods of
  Right p -> return p
  Left errs -> assertFailure $ "unexpected errors: " ++ show errs

singleRule :: [Module] -> IO D.Rule
singleRule mods = do
  D.Program rules <- desugar mods
  case rules of
    [r] -> return r
    rs -> assertFailure $ "expected 1 rule, got " ++ show (length rs)

leqQual :: Constraint
leqQual = "M" .: con "leq" [var "X", var "Y"]

leqQual2 :: Constraint
leqQual2 = "M" .: con "leq" [var "A", var "B"]

mod1rule :: Head -> Rule
mod1rule h = Rule Nothing (noAnn h) (noAnn []) (noAnn [atom "true"])

simpleModule :: Head -> Module
simpleModule h = module' "M" `defining` [mod1rule h]

--------------------------------------------------------------------------------
-- Head normalization
--------------------------------------------------------------------------------

headTests :: TestTree
headTests =
  testGroup
    "head-normalization"
    [ testCase "Simplification maps to kept=[], removed=constraints" $ do
        rule <- singleRule [simpleModule (Simplification [leqQual])]
        D.ruleHead rule @?= D.Head {D.headKept = [], D.headRemoved = [leqQual]},
      testCase "Propagation maps to kept=constraints, removed=[]" $ do
        rule <- singleRule [simpleModule (Propagation [leqQual])]
        D.ruleHead rule @?= D.Head {D.headKept = [leqQual], D.headRemoved = []},
      testCase "Simpagation maps kept and removed correctly" $ do
        rule <- singleRule [simpleModule (Simpagation [leqQual] [leqQual2])]
        D.ruleHead rule @?= D.Head {D.headKept = [leqQual], D.headRemoved = [leqQual2]}
    ]

--------------------------------------------------------------------------------
-- Head Normal Form
--------------------------------------------------------------------------------

hnfTests :: TestTree
hnfTests =
  testGroup
    "hnf"
    [ testCase "distinct variables: no change" $ do
        let m = simpleModule (Simplification ["M" .: con "leq" [var "X", var "Y"]])
        rule <- singleRule [m]
        D.ruleHead rule @?= D.Head [] [Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "Y"]]
        D.ruleGuard rule @?= [],
      testCase "duplicate variable generates equality guard" $ do
        let m = simpleModule (Simplification ["M" .: con "leq" [var "X", var "X"]])
        rule <- singleRule [m]
        D.ruleHead rule @?= D.Head [] [Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "_hnf_0"]]
        D.ruleGuard rule @?= [D.GuardEqual (VarTerm "X") (VarTerm "_hnf_0")],
      testCase "non-variable argument (integer) generates equality guard" $ do
        let m = simpleModule (Simplification ["M" .: con "leq" [var "X", IntTerm 5]])
        rule <- singleRule [m]
        D.ruleHead rule @?= D.Head [] [Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "_hnf_0"]]
        D.ruleGuard rule @?= [D.GuardEqual (VarTerm "_hnf_0") (IntTerm 5)],
      testCase "non-variable argument (atom) generates equality guard" $ do
        let m = simpleModule (Simplification ["M" .: con "leq" [var "X", atom "foo"]])
        rule <- singleRule [m]
        D.ruleHead rule @?= D.Head [] [Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "_hnf_0"]]
        D.ruleGuard rule @?= [D.GuardEqual (VarTerm "_hnf_0") (AtomTerm "foo")],
      testCase "cross-constraint duplicate variable" $ do
        let m =
              simpleModule
                ( Simplification
                    [ "M" .: con "leq" [var "X", var "Y"],
                      "M" .: con "leq" [var "Y", var "Z"]
                    ]
                )
        rule <- singleRule [m]
        D.ruleHead rule
          @?= D.Head
            []
            [ Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "Y"],
              Constraint (Qualified "M" "leq") [VarTerm "_hnf_0", VarTerm "Z"]
            ]
        D.ruleGuard rule @?= [D.GuardEqual (VarTerm "Y") (VarTerm "_hnf_0")],
      testCase "simpagation: kept processed before removed" $ do
        let m =
              simpleModule
                ( Simpagation
                    ["M" .: con "leq" [var "X", var "Y"]]
                    ["M" .: con "leq" [var "Y", var "Z"]]
                )
        rule <- singleRule [m]
        D.ruleHead rule
          @?= D.Head
            [Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "Y"]]
            [Constraint (Qualified "M" "leq") [VarTerm "_hnf_0", VarTerm "Z"]]
        D.ruleGuard rule @?= [D.GuardEqual (VarTerm "Y") (VarTerm "_hnf_0")],
      testCase "hnf guards prepended before user guards" $ do
        let m =
              module' "M"
                `defining` [ Rule
                               Nothing
                               (noAnn (Simplification ["M" .: con "leq" [var "X", var "X"]]))
                               (noAnn [func "gt" [var "X", IntTerm 0]])
                               (noAnn [atom "true"])
                           ]
        rule <- singleRule [m]
        D.ruleGuard rule
          @?= [ D.GuardEqual (VarTerm "X") (VarTerm "_hnf_0"),
                D.GuardExpr (CompoundTerm (Unqualified "gt") [VarTerm "X", IntTerm 0])
              ],
      testCase "wildcard passes through HNF unchanged" $ do
        let m = simpleModule (Simplification ["M" .: con "foo" [wildcard]])
        rule <- singleRule [m]
        D.ruleHead rule @?= D.Head [] [Constraint (Qualified "M" "foo") [Wildcard]]
        D.ruleGuard rule @?= [],
      testCase "two wildcards stay as wildcards without guards" $ do
        let m = simpleModule (Simplification ["M" .: con "foo" [wildcard, wildcard]])
        rule <- singleRule [m]
        D.ruleHead rule @?= D.Head [] [Constraint (Qualified "M" "foo") [Wildcard, Wildcard]]
        D.ruleGuard rule @?= [],
      testCase "wildcard and non-variable: only non-variable gets guard" $ do
        let m = simpleModule (Simplification ["M" .: con "foo" [wildcard, IntTerm 1]])
        rule <- singleRule [m]
        D.ruleHead rule @?= D.Head [] [Constraint (Qualified "M" "foo") [Wildcard, VarTerm "_hnf_0"]]
        D.ruleGuard rule @?= [D.GuardEqual (VarTerm "_hnf_0") (IntTerm 1)]
    ]

--------------------------------------------------------------------------------
-- Guard classification
--------------------------------------------------------------------------------

guardTests :: TestTree
guardTests =
  testGroup
    "guard-classification"
    [ testCase "== becomes GuardExpr" $ do
        let m =
              module' "M"
                `defining` [ Rule Nothing (noAnn (Simplification [leqQual])) (noAnn [func "==" [var "X", var "Y"]]) (noAnn [atom "true"])
                           ]
        rule <- singleRule [m]
        D.ruleGuard rule @?= [D.GuardExpr (CompoundTerm (Unqualified "==") [VarTerm "X", VarTerm "Y"])],
      testCase "host call becomes GuardExpr" $ do
        let m =
              module' "M"
                `defining` [ Rule Nothing (noAnn (Simplification [leqQual])) (noAnn [func "gt" [var "X", IntTerm 0]]) (noAnn [atom "true"])
                           ]
        rule <- singleRule [m]
        D.ruleGuard rule @?= [D.GuardExpr (CompoundTerm (Unqualified "gt") [VarTerm "X", IntTerm 0])],
      testCase "atom true becomes GuardCommon GoalTrue" $ do
        let m =
              module' "M"
                `defining` [ Rule Nothing (noAnn (Simplification [leqQual])) (noAnn [atom "true"]) (noAnn [atom "true"])
                           ]
        rule <- singleRule [m]
        D.ruleGuard rule @?= [D.GuardCommon D.GoalTrue]
    ]

--------------------------------------------------------------------------------
-- Body goal classification
--------------------------------------------------------------------------------

bodyTests :: TestTree
bodyTests =
  testGroup
    "body-classification"
    [ testCase "= becomes BodyUnify" $ do
        rule <- singleRule [simpleModule' (Simplification [leqQual]) [var "X" .=. var "Y"]]
        D.ruleBody rule @?= [D.BodyUnify (VarTerm "X") (VarTerm "Y")],
      testCase ":= becomes BodyHostCall" $ do
        rule <- singleRule [simpleModule' (Simplification [leqQual]) [var "X" .:=. func "readInt" []]]
        D.ruleBody rule @?= [D.BodyHostCall "X" "readInt" []],
      testCase "is becomes BodyIs" $ do
        rule <- singleRule [simpleModule' (Simplification [leqQual]) [var "X" `is` func "+" [int 1, int 2]]]
        D.ruleBody rule @?= [D.BodyIs "X" (CompoundTerm (Unqualified "+") [IntTerm 1, IntTerm 2])],
      testCase "Qualified compound becomes BodyConstraint" $ do
        let body = [CompoundTerm (Qualified "M" "leq") [var "X"]]
        rule <- singleRule [simpleModule' (Simplification [leqQual]) body]
        D.ruleBody rule @?= [D.BodyConstraint (Constraint (Qualified "M" "leq") [VarTerm "X"])],
      testCase "hostStmt becomes BodyHostStmt" $ do
        rule <- singleRule [simpleModule' (Simplification [leqQual]) [hostStmt "print" [var "X"]]]
        D.ruleBody rule @?= [D.BodyHostStmt "print" [VarTerm "X"]],
      testCase "atom true becomes BodyCommon GoalTrue" $ do
        rule <- singleRule [simpleModule' (Simplification [leqQual]) [atom "true"]]
        D.ruleBody rule @?= [D.BodyCommon D.GoalTrue]
    ]
  where
    simpleModule' h body = module' "M" `defining` [Rule Nothing (noAnn h) (noAnn []) (noAnn body)]

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

errorTests :: TestTree
errorTests =
  testGroup
    "error-handling"
    [ testCase "unqualified compound in body produces UnexpectedBodyTerm" $ do
        let badTerm = func "foo" [var "X"]
            m = module' "M" `defining` [Rule Nothing (noAnn (Simplification [leqQual])) (noAnn []) (noAnn [badTerm])]
        desugarProgram [m] @?= Left [UnexpectedBodyTerm badTerm],
      testCase "two unqualified compounds collect both errors" $ do
        let bad1 = func "foo" [var "X"]
            bad2 = func "bar" [var "Y"]
            m = module' "M" `defining` [Rule Nothing (noAnn (Simplification [leqQual])) (noAnn []) (noAnn [bad1, bad2])]
        desugarProgram [m] @?= Left [UnexpectedBodyTerm bad1, UnexpectedBodyTerm bad2]
    ]

--------------------------------------------------------------------------------
-- Multi-module flattening
--------------------------------------------------------------------------------

flatteningTests :: TestTree
flatteningTests =
  testGroup
    "flattening"
    [ testCase "two modules with one rule each yield two rules" $ do
        let m1 = module' "A" `defining` [[("A" .: con "c" [])] <=> [atom "true"]]
            m2 = module' "B" `defining` [[("B" .: con "d" [])] <=> [atom "true"]]
        D.Program rules <- desugar [m1, m2]
        length rules @?= 2,
      testCase "empty module list yields empty program" $
        desugarProgram [] @?= Right (D.Program []),
      testCase "module with no rules contributes no rules" $ do
        let empty = module' "Empty"
            m = module' "M" `defining` [[("M" .: con "c" [])] <=> [atom "true"]]
        D.Program rules <- desugar [empty, m]
        length rules @?= 1
    ]

--------------------------------------------------------------------------------
-- Rule name preservation
--------------------------------------------------------------------------------

ruleNameTests :: TestTree
ruleNameTests =
  testGroup
    "rule-name"
    [ testCase "named rule preserves name" $ do
        let m = module' "M" `defining` ["my_rule" @: ([leqQual] <=> [atom "true"])]
        rule <- singleRule [m]
        D.ruleName rule @?= Just "my_rule",
      testCase "anonymous rule has Nothing name" $ do
        rule <- singleRule [simpleModule (Simplification [leqQual])]
        D.ruleName rule @?= Nothing
    ]

--------------------------------------------------------------------------------
-- Symbol table
--------------------------------------------------------------------------------

symbolTableTests :: TestTree
symbolTableTests =
  testGroup
    "symbol-table"
    [ testCase "empty program yields empty table" $
        extractSymbolTable (D.Program []) @?= mkSymbolTable [],
      testCase "one qualified constraint in head gets id 0" $ do
        let prog =
              D.Program
                [ D.Rule
                    Nothing
                    (D.Head [] [Constraint (Qualified "M" "leq") []])
                    []
                    []
                ]
        extractSymbolTable prog @?= mkSymbolTable [(Qualified "M" "leq", ConstraintType 0)],
      testCase "two distinct qualified constraints get sequential ids" $ do
        let prog =
              D.Program
                [ D.Rule
                    Nothing
                    (D.Head [] [Constraint (Qualified "A" "c") [], Constraint (Qualified "B" "d") []])
                    []
                    []
                ]
        let table = extractSymbolTable prog
        symbolTableSize table @?= 2,
      testCase "same constraint in head and body appears only once" $ do
        let prog =
              D.Program
                [ D.Rule
                    Nothing
                    (D.Head [] [Constraint (Qualified "M" "leq") []])
                    []
                    [D.BodyConstraint (Constraint (Qualified "M" "leq") [])]
                ]
        extractSymbolTable prog @?= mkSymbolTable [(Qualified "M" "leq", ConstraintType 0)],
      testCase "unqualified name in body not in table" $ do
        let prog =
              D.Program
                [ D.Rule
                    Nothing
                    (D.Head [] [Constraint (Qualified "M" "leq") []])
                    []
                    [D.BodyHostStmt "print" []]
                ]
        let table = extractSymbolTable prog
        lookupSymbol (Unqualified "print") table @?= Nothing,
      testCase "ids assigned in Set.toList order (module-first then name)" $ do
        -- Qualified "A" "z" < Qualified "B" "a" by derived Ord
        let prog =
              D.Program
                [ D.Rule
                    Nothing
                    ( D.Head
                        []
                        [ Constraint (Qualified "A" "z") [],
                          Constraint (Qualified "B" "a") []
                        ]
                    )
                    []
                    []
                ]
        let table = extractSymbolTable prog
        (lookupSymbol (Qualified "A" "z") table, lookupSymbol (Qualified "B" "a") table)
          @?= (Just (ConstraintType 0), Just (ConstraintType 1))
    ]
