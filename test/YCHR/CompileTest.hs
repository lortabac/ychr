{-# LANGUAGE OverloadedStrings #-}

-- | Pure compilation tests: assertions about the VM code emitted by
-- 'YCHR.Compile.compile' for representative CHR programs. These tests
-- inspect the generated 'YCHR.VM.Program' AST directly without running
-- it through the interpreter.
module YCHR.CompileTest (tests) where

import Data.Text (Text)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import YCHR.Run (CompiledProgram (..), compileModules)
import YCHR.VM qualified as VM

tests :: TestTree
tests =
  testGroup
    "YCHR.Compile"
    [ indexConditionPushdownTests
    ]

-- ---------------------------------------------------------------------------
-- Shared helpers
-- ---------------------------------------------------------------------------

compileOrFail :: [(FilePath, Text)] -> IO CompiledProgram
compileOrFail inputs = case compileModules False inputs of
  Left err -> assertFailure $ show err
  Right (cp, _) -> pure cp

-- | Find the (single) Foreach statement reachable from a list of
-- statements. All compiler-generated occurrence procedures contain at
-- most one top-level Foreach per partner level; for the leqSource rules
-- below this helper returns the outermost (and only) Foreach.
findForeach :: [VM.Stmt] -> Maybe VM.Stmt
findForeach [] = Nothing
findForeach (s : rest) = case s of
  f@(VM.Foreach {}) -> Just f
  VM.If _ thn els -> case findForeach thn of
    Just f -> Just f
    Nothing -> case findForeach els of
      Just f -> Just f
      Nothing -> findForeach rest
  _ -> findForeach rest

foreachConditions :: VM.Stmt -> [(VM.ArgIndex, VM.Expr)]
foreachConditions (VM.Foreach _ _ _ conds _) = conds
foreachConditions _ = error "foreachConditions: not a Foreach"

-- | Look up a procedure by name in a compiled program.
findProcedure :: CompiledProgram -> Text -> Maybe VM.Procedure
findProcedure prog wanted =
  let want = VM.Name wanted
   in case filter (\p -> p.name == want) prog.program.procedures of
        [p] -> Just p
        _ -> Nothing

-- | Assert that the named occurrence procedure contains a Foreach with
-- the given index conditions.
assertForeachConditions ::
  CompiledProgram ->
  Text ->
  [(VM.ArgIndex, VM.Expr)] ->
  IO ()
assertForeachConditions prog procName expected =
  case findProcedure prog procName of
    Nothing -> assertFailure $ "procedure not found: " ++ show procName
    Just p -> case findForeach p.body of
      Nothing -> assertFailure $ "no Foreach in " ++ show procName
      Just f -> foreachConditions f @?= expected

-- ---------------------------------------------------------------------------
-- LEQ surface source (duplicated from RunTest so this module is
-- self-contained — both files exercise leq.chr but for different reasons).
-- ---------------------------------------------------------------------------

leqSource :: Text
leqSource =
  ":- module(order, [leq/2]).\n\
  \:- chr_constraint leq/2.\n\
  \\n\
  \reflexivity @ leq(X, X) <=> true.\n\
  \antisymmetry @ leq(X, Y), leq(Y, X) <=> X = Y.\n\
  \idempotence @ leq(X, Y) \\ leq(X, Y) <=> true.\n\
  \transitivity @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).\n"

-- ---------------------------------------------------------------------------
-- Foreach index-condition pushdown
-- ---------------------------------------------------------------------------

indexConditionPushdownTests :: TestTree
indexConditionPushdownTests =
  testGroup
    "Foreach index-condition pushdown"
    [ testCase "leq antisymmetry: both partner args constrained to active args" $ do
        -- antisymmetry @ leq(X, Y), leq(Y, X) <=> X = Y.
        -- Two occurrences (one per kept head); each must lift two
        -- equalities into the partner Foreach's conditions.
        prog <- compileOrFail [("order.chr", leqSource)]
        assertForeachConditions
          prog
          "occurrence_order__leq2_2"
          [(VM.ArgIndex 1, VM.Var "X_0"), (VM.ArgIndex 0, VM.Var "X_1")]
        assertForeachConditions
          prog
          "occurrence_order__leq2_3"
          [(VM.ArgIndex 0, VM.Var "X_1"), (VM.ArgIndex 1, VM.Var "X_0")],
      testCase "leq idempotence: both partner args constrained to active args" $ do
        -- idempotence @ leq(X, Y) \ leq(X, Y) <=> true.
        prog <- compileOrFail [("order.chr", leqSource)]
        assertForeachConditions
          prog
          "occurrence_order__leq2_4"
          [(VM.ArgIndex 0, VM.Var "X_0"), (VM.ArgIndex 1, VM.Var "X_1")]
        assertForeachConditions
          prog
          "occurrence_order__leq2_5"
          [(VM.ArgIndex 0, VM.Var "X_0"), (VM.ArgIndex 1, VM.Var "X_1")],
      testCase "leq transitivity: single shared variable lifted" $ do
        -- transitivity @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).
        -- Each occurrence has exactly one HNF equality on the partner.
        prog <- compileOrFail [("order.chr", leqSource)]
        assertForeachConditions
          prog
          "occurrence_order__leq2_6"
          [(VM.ArgIndex 1, VM.Var "X_0")]
        assertForeachConditions
          prog
          "occurrence_order__leq2_7"
          [(VM.ArgIndex 0, VM.Var "X_1")],
      testCase "leq reflexivity: no partners, equality stays residual" $ do
        -- reflexivity @ leq(X, X) <=> true.
        -- The Foreach is absent (single-headed rule), and the residual
        -- check guard contains the active-self equality.
        prog <- compileOrFail [("order.chr", leqSource)]
        case findProcedure prog "occurrence_order__leq2_1" of
          Nothing -> assertFailure "occurrence_order__leq2_1 not found"
          Just p -> do
            findForeach p.body @?= Nothing
            -- The residual check should contain Equal X_0 X_1.
            let hasSelfEqual = any containsSelfEqual p.body
            assertBool "expected residual Equal X_0 X_1" hasSelfEqual
    ]
  where
    containsSelfEqual (VM.If e _ _) = exprHasSelfEqual e
    containsSelfEqual _ = False
    exprHasSelfEqual (VM.Equal (VM.Var "X_0") (VM.Var "X_1")) = True
    exprHasSelfEqual (VM.Equal (VM.Var "X_1") (VM.Var "X_0")) = True
    exprHasSelfEqual (VM.And a b) = exprHasSelfEqual a || exprHasSelfEqual b
    exprHasSelfEqual _ = False
