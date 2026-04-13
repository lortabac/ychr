{-# LANGUAGE OverloadedStrings #-}

module YCHR.DesugarTest (tests) where

import Data.Map.Strict qualified as Map
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import YCHR.DSL
import YCHR.Desugar (DesugarError (..), desugarProgram, extractSymbolTable, liftAllLambdas)
import YCHR.Desugared qualified as D
import YCHR.Parsed
import YCHR.Pretty (AnnP (..), noAnnP)
import YCHR.Types (ConstraintType (..), Identifier (..), Name (..), lookupSymbol, mkSymbolTable, symbolTableSize)

getNode :: AnnP a -> a
getNode (AnnP n _ _) = n

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
      symbolTableTests,
      lambdaLiftTests
    ]

desugar :: [Module] -> IO D.Program
desugar mods = case desugarProgram mods of
  Right p -> return p
  Left errs -> assertFailure $ "unexpected errors: " ++ show errs

singleRule :: [Module] -> IO D.Rule
singleRule mods = do
  prog <- desugar mods
  let rules = prog.rules
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
        getNode rule.head @?= D.Head {kept = [], removed = [leqQual]},
      testCase "Propagation maps to kept=constraints, removed=[]" $ do
        rule <- singleRule [simpleModule (Propagation [leqQual])]
        getNode rule.head @?= D.Head {kept = [leqQual], removed = []},
      testCase "Simpagation maps kept and removed correctly" $ do
        rule <- singleRule [simpleModule (Simpagation [leqQual] [leqQual2])]
        getNode rule.head @?= D.Head {kept = [leqQual], removed = [leqQual2]}
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
        getNode rule.head @?= D.Head [] [Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "Y"]]
        getNode rule.guard @?= [],
      testCase "duplicate variable generates equality guard" $ do
        let m = simpleModule (Simplification ["M" .: con "leq" [var "X", var "X"]])
        rule <- singleRule [m]
        getNode rule.head @?= D.Head [] [Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "_hnf_0"]]
        getNode rule.guard @?= [D.GuardEqual (VarTerm "X") (VarTerm "_hnf_0")],
      testCase "non-variable argument (integer) generates equality guard" $ do
        let m = simpleModule (Simplification ["M" .: con "leq" [var "X", IntTerm 5]])
        rule <- singleRule [m]
        getNode rule.head @?= D.Head [] [Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "_hnf_0"]]
        getNode rule.guard @?= [D.GuardEqual (VarTerm "_hnf_0") (IntTerm 5)],
      testCase "non-variable argument (atom) generates equality guard" $ do
        let m = simpleModule (Simplification ["M" .: con "leq" [var "X", atom "foo"]])
        rule <- singleRule [m]
        getNode rule.head @?= D.Head [] [Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "_hnf_0"]]
        getNode rule.guard @?= [D.GuardEqual (VarTerm "_hnf_0") (AtomTerm "foo")],
      testCase "cross-constraint duplicate variable" $ do
        let m =
              simpleModule
                ( Simplification
                    [ "M" .: con "leq" [var "X", var "Y"],
                      "M" .: con "leq" [var "Y", var "Z"]
                    ]
                )
        rule <- singleRule [m]
        getNode rule.head
          @?= D.Head
            []
            [ Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "Y"],
              Constraint (Qualified "M" "leq") [VarTerm "_hnf_0", VarTerm "Z"]
            ]
        getNode rule.guard @?= [D.GuardEqual (VarTerm "Y") (VarTerm "_hnf_0")],
      testCase "simpagation: kept processed before removed" $ do
        let m =
              simpleModule
                ( Simpagation
                    ["M" .: con "leq" [var "X", var "Y"]]
                    ["M" .: con "leq" [var "Y", var "Z"]]
                )
        rule <- singleRule [m]
        getNode rule.head
          @?= D.Head
            [Constraint (Qualified "M" "leq") [VarTerm "X", VarTerm "Y"]]
            [Constraint (Qualified "M" "leq") [VarTerm "_hnf_0", VarTerm "Z"]]
        getNode rule.guard @?= [D.GuardEqual (VarTerm "Y") (VarTerm "_hnf_0")],
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
        getNode rule.guard
          @?= [ D.GuardEqual (VarTerm "X") (VarTerm "_hnf_0"),
                D.GuardExpr (CompoundTerm (Unqualified "gt") [VarTerm "X", IntTerm 0])
              ],
      testCase "wildcard passes through HNF unchanged" $ do
        let m = simpleModule (Simplification ["M" .: con "foo" [wildcard]])
        rule <- singleRule [m]
        getNode rule.head @?= D.Head [] [Constraint (Qualified "M" "foo") [Wildcard]]
        getNode rule.guard @?= [],
      testCase "two wildcards stay as wildcards without guards" $ do
        let m = simpleModule (Simplification ["M" .: con "foo" [wildcard, wildcard]])
        rule <- singleRule [m]
        getNode rule.head @?= D.Head [] [Constraint (Qualified "M" "foo") [Wildcard, Wildcard]]
        getNode rule.guard @?= [],
      testCase "wildcard and non-variable: only non-variable gets guard" $ do
        let m = simpleModule (Simplification ["M" .: con "foo" [wildcard, IntTerm 1]])
        rule <- singleRule [m]
        getNode rule.head @?= D.Head [] [Constraint (Qualified "M" "foo") [Wildcard, VarTerm "_hnf_0"]]
        getNode rule.guard @?= [D.GuardEqual (VarTerm "_hnf_0") (IntTerm 1)]
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
        getNode rule.guard @?= [D.GuardExpr (CompoundTerm (Unqualified "==") [VarTerm "X", VarTerm "Y"])],
      testCase "host call becomes GuardExpr" $ do
        let m =
              module' "M"
                `defining` [ Rule Nothing (noAnn (Simplification [leqQual])) (noAnn [func "gt" [var "X", IntTerm 0]]) (noAnn [atom "true"])
                           ]
        rule <- singleRule [m]
        getNode rule.guard @?= [D.GuardExpr (CompoundTerm (Unqualified "gt") [VarTerm "X", IntTerm 0])],
      testCase "atom true becomes GuardExpr" $ do
        let m =
              module' "M"
                `defining` [ Rule Nothing (noAnn (Simplification [leqQual])) (noAnn [atom "true"]) (noAnn [atom "true"])
                           ]
        rule <- singleRule [m]
        getNode rule.guard @?= [D.GuardExpr (AtomTerm "true")]
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
        getNode rule.body @?= [D.BodyUnify (VarTerm "X") (VarTerm "Y")],
      testCase "is becomes BodyIs" $ do
        rule <- singleRule [simpleModule' (Simplification [leqQual]) [var "X" `is` func "+" [int 1, int 2]]]
        getNode rule.body @?= [D.BodyIs "X" (CompoundTerm (Unqualified "+") [IntTerm 1, IntTerm 2])],
      testCase "Qualified compound becomes BodyConstraint" $ do
        let body = [CompoundTerm (Qualified "M" "leq") [var "X"]]
        rule <- singleRule [simpleModule' (Simplification [leqQual]) body]
        getNode rule.body @?= [D.BodyConstraint (Constraint (Qualified "M" "leq") [VarTerm "X"])],
      testCase "hostCall becomes BodyHostStmt" $ do
        rule <- singleRule [simpleModule' (Simplification [leqQual]) [hostCall "print" [var "X"]]]
        getNode rule.body @?= [D.BodyHostStmt "print" [VarTerm "X"]],
      testCase "atom true becomes BodyCommon GoalTrue" $ do
        rule <- singleRule [simpleModule' (Simplification [leqQual]) [atom "true"]]
        getNode rule.body @?= [D.BodyCommon D.GoalTrue]
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
        case desugarProgram [m] of
          Left errs -> errs @?= [UnexpectedBodyTerm dummyLoc badTerm]
          Right _ -> assertFailure "expected Left",
      testCase "two unqualified compounds collect both errors" $ do
        let bad1 = func "foo" [var "X"]
            bad2 = func "bar" [var "Y"]
            m = module' "M" `defining` [Rule Nothing (noAnn (Simplification [leqQual])) (noAnn []) (noAnn [bad1, bad2])]
        case desugarProgram [m] of
          Left errs -> errs @?= [UnexpectedBodyTerm dummyLoc bad1, UnexpectedBodyTerm dummyLoc bad2]
          Right _ -> assertFailure "expected Left",
      testCase "bare variable in body produces UnexpectedBodyTerm" $ do
        let badTerm = var "X"
            m = module' "M" `defining` [Rule Nothing (noAnn (Simplification [leqQual])) (noAnn []) (noAnn [badTerm])]
        case desugarProgram [m] of
          Left errs -> errs @?= [UnexpectedBodyTerm dummyLoc badTerm]
          Right _ -> assertFailure "expected Left",
      testCase "bare integer in body produces UnexpectedBodyTerm" $ do
        let badTerm = int 42
            m = module' "M" `defining` [Rule Nothing (noAnn (Simplification [leqQual])) (noAnn []) (noAnn [badTerm])]
        case desugarProgram [m] of
          Left errs -> errs @?= [UnexpectedBodyTerm dummyLoc badTerm]
          Right _ -> assertFailure "expected Left",
      testCase "non-true atom in body produces UnexpectedBodyTerm" $ do
        let badTerm = atom "foo"
            m = module' "M" `defining` [Rule Nothing (noAnn (Simplification [leqQual])) (noAnn []) (noAnn [badTerm])]
        case desugarProgram [m] of
          Left errs -> errs @?= [UnexpectedBodyTerm dummyLoc badTerm]
          Right _ -> assertFailure "expected Left",
      testCase "bare variable in guard becomes GuardExpr" $ do
        let term = var "X"
            m = module' "M" `defining` [Rule Nothing (noAnn (Simplification [leqQual])) (noAnn [term]) (noAnn [atom "true"])]
        case desugarProgram [m] of
          Left errs -> assertFailure ("unexpected errors: " ++ show errs)
          Right prog -> do
            let rule = head prog.rules
            getNode rule.guard @?= [D.GuardExpr (VarTerm "X")],
      testCase "bare integer in guard becomes GuardExpr" $ do
        let term = int 42
            m = module' "M" `defining` [Rule Nothing (noAnn (Simplification [leqQual])) (noAnn [term]) (noAnn [atom "true"])]
        case desugarProgram [m] of
          Left errs -> assertFailure ("unexpected errors: " ++ show errs)
          Right prog -> do
            let rule = head prog.rules
            getNode rule.guard @?= [D.GuardExpr (IntTerm 42)],
      testCase "non-true atom in guard becomes GuardExpr" $ do
        let term = atom "foo"
            m = module' "M" `defining` [Rule Nothing (noAnn (Simplification [leqQual])) (noAnn [term]) (noAnn [atom "true"])]
        case desugarProgram [m] of
          Left errs -> assertFailure ("unexpected errors: " ++ show errs)
          Right prog -> do
            let rule = head prog.rules
            getNode rule.guard @?= [D.GuardExpr (AtomTerm "foo")]
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
        prog <- desugar [m1, m2]
        length prog.rules @?= 2,
      testCase "empty module list yields empty program" $ do
        prog <- desugar []
        length prog.rules @?= 0,
      testCase "module with no rules contributes no rules" $ do
        let empty = module' "Empty"
            m = module' "M" `defining` [[("M" .: con "c" [])] <=> [atom "true"]]
        prog <- desugar [empty, m]
        length prog.rules @?= 1
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
        rule.name @?= Just "my_rule",
      testCase "anonymous rule has Nothing name" $ do
        rule <- singleRule [simpleModule (Simplification [leqQual])]
        rule.name @?= Nothing
    ]

--------------------------------------------------------------------------------
-- Symbol table
--------------------------------------------------------------------------------

symbolTableTests :: TestTree
symbolTableTests =
  testGroup
    "symbol-table"
    [ testCase "empty program yields empty table" $
        extractSymbolTable (D.Program [] [] Map.empty []) @?= mkSymbolTable [],
      testCase "one qualified constraint in head gets id 0" $ do
        let prog =
              D.Program
                [ D.Rule
                    Nothing
                    (noAnnP (Simplification [] :: Head) (D.Head [] [Constraint (Qualified "M" "leq") []]))
                    (noAnnP ([] :: [Term]) [])
                    (noAnnP ([] :: [Term]) [])
                ]
                []
                Map.empty
                []
        extractSymbolTable prog @?= mkSymbolTable [(Identifier (Qualified "M" "leq") 0, ConstraintType 0)],
      testCase "two distinct qualified constraints get sequential ids" $ do
        let prog =
              D.Program
                [ D.Rule
                    Nothing
                    (noAnnP (Simplification [] :: Head) (D.Head [] [Constraint (Qualified "A" "c") [], Constraint (Qualified "B" "d") []]))
                    (noAnnP ([] :: [Term]) [])
                    (noAnnP ([] :: [Term]) [])
                ]
                []
                Map.empty
                []
        let table = extractSymbolTable prog
        symbolTableSize table @?= 2,
      testCase "same constraint in head and body appears only once" $ do
        let prog =
              D.Program
                [ D.Rule
                    Nothing
                    (noAnnP (Simplification [] :: Head) (D.Head [] [Constraint (Qualified "M" "leq") []]))
                    (noAnnP ([] :: [Term]) [])
                    (noAnnP ([] :: [Term]) [D.BodyConstraint (Constraint (Qualified "M" "leq") [])])
                ]
                []
                Map.empty
                []
        extractSymbolTable prog @?= mkSymbolTable [(Identifier (Qualified "M" "leq") 0, ConstraintType 0)],
      testCase "unqualified name in body not in table" $ do
        let prog =
              D.Program
                [ D.Rule
                    Nothing
                    (noAnnP (Simplification [] :: Head) (D.Head [] [Constraint (Qualified "M" "leq") []]))
                    (noAnnP ([] :: [Term]) [])
                    (noAnnP ([] :: [Term]) [D.BodyHostStmt "print" []])
                ]
                []
                Map.empty
                []
        let table = extractSymbolTable prog
        lookupSymbol (Identifier (Unqualified "print") 0) table @?= Nothing,
      testCase "ids assigned in Set.toList order (module-first then name)" $ do
        -- Qualified "A" "z" < Qualified "B" "a" by derived Ord
        let prog =
              D.Program
                [ D.Rule
                    Nothing
                    ( noAnnP
                        (Simplification [] :: Head)
                        ( D.Head
                            []
                            [ Constraint (Qualified "A" "z") [],
                              Constraint (Qualified "B" "a") []
                            ]
                        )
                    )
                    (noAnnP ([] :: [Term]) [])
                    (noAnnP ([] :: [Term]) [])
                ]
                []
                Map.empty
                []
        let table = extractSymbolTable prog
        (lookupSymbol (Identifier (Qualified "A" "z") 0) table, lookupSymbol (Identifier (Qualified "B" "a") 0) table)
          @?= (Just (ConstraintType 0), Just (ConstraintType 1)),
      testCase "same name different arities get distinct ids" $ do
        let prog =
              D.Program
                [ D.Rule
                    Nothing
                    (noAnnP (Simplification [] :: Head) (D.Head [] [Constraint (Qualified "M" "foo") [VarTerm "X"]]))
                    (noAnnP ([] :: [Term]) [])
                    (noAnnP ([] :: [Term]) [D.BodyConstraint (Constraint (Qualified "M" "foo") [VarTerm "X", VarTerm "Y"])])
                ]
                []
                Map.empty
                []
        let table = extractSymbolTable prog
        symbolTableSize table @?= 2
    ]

--------------------------------------------------------------------------------
-- Lambda lifting
--------------------------------------------------------------------------------

lambdaLiftTests :: TestTree
lambdaLiftTests =
  testGroup
    "lambda-lift"
    [ testCase "lambda captures HNF-bound pattern variable" $ do
        -- f([X|Xs]) -> fun(Y) -> Y + X
        --
        -- HNF decomposes the compound pattern so that X is bound by a
        -- GuardGetArg, not by the surface parameter list. The
        -- lambda-lifter must therefore treat HNF-introduced bindings as
        -- in scope; otherwise the fun(Y) lambda would be lifted without
        -- capturing X and the reference inside the body would dangle.
        let lambdaBody = func "+" [var "Y", var "X"]
            lambdaTerm =
              CompoundTerm
                (Unqualified "->")
                [CompoundTerm (Unqualified "fun") [var "Y"], lambdaBody]
            listPattern = func "." [var "X", var "Xs"]
            funDecl =
              noAnn
                FunctionDecl
                  { name = "f",
                    arity = 1,
                    argTypes = Nothing,
                    returnType = Nothing
                  }
            funEq =
              noAnn
                FunctionEquation
                  { funName = "f",
                    args = [listPattern],
                    guard = noAnn [],
                    rhs = noAnn lambdaTerm
                  }
            m = (module' "M") {decls = [funDecl], equations = [funEq]}
        prog <- desugar [m]
        lifted <- case liftAllLambdas prog of
          Left errs -> assertFailure ("liftAllLambdas failed: " ++ show errs) >> error "unreachable"
          Right p -> pure p
        let isLambda f = case f.name of
              Qualified _ n -> n == "__lambda_0"
              _ -> False
        case filter isLambda lifted.functions of
          [lam] -> do
            lam.arity @?= 2
            case lam.equations.node of
              [eq] -> do
                eq.params @?= [var "X", var "Y"]
                eq.guards @?= []
                eq.rhs @?= lambdaBody
              eqs -> assertFailure $ "expected 1 equation, got " ++ show (length eqs)
          fs -> assertFailure $ "expected exactly one __lambda_0, got " ++ show (length fs),
      testCase "rejects non-variable lambda parameter" $ do
        -- fun("hello") -> "world" end should produce an InvalidLambdaParam error
        let lambdaTerm =
              CompoundTerm
                (Unqualified "->")
                [ CompoundTerm (Unqualified "fun") [TextTerm "hello"],
                  TextTerm "world"
                ]
            funDecl = Ann (FunctionDecl "f" 1 Nothing Nothing) dummyLoc
            funEq =
              Ann
                FunctionEquation
                  { funName = "f",
                    args = [var "X"],
                    guard = noAnn [],
                    rhs = noAnn lambdaTerm
                  }
                dummyLoc
            m = (module' "M") {decls = [funDecl], equations = [funEq]}
        prog <- desugar [m]
        case liftAllLambdas prog of
          Left errs -> errs @?= [InvalidLambdaParam dummyLoc (TextTerm "hello")]
          Right _ -> assertFailure "expected InvalidLambdaParam error"
    ]
