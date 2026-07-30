{-# LANGUAGE OverloadedStrings #-}

-- | Pure compilation tests: assertions about the VM code emitted by
-- 'YCHR.Internal.Compile.compile' for representative CHR programs. These tests
-- inspect the generated 'YCHR.Internal.VM.Program' AST directly without running
-- it through the interpreter.
module YCHR.CompileTest (tests) where

import Data.Maybe (isJust, isNothing)
import Data.Text (Text)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import YCHR.Internal.VM qualified as VM
import YCHR.Run (CompiledProgram (..), compileModules)

tests :: TestTree
tests =
  testGroup
    "YCHR.Internal.Compile"
    [ indexConditionPushdownTests,
      passiveOccurrencesTests
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

foreachConditions :: VM.Stmt -> [(VM.ArgIndex, VM.ValExpr)]
foreachConditions (VM.Foreach _ _ _ conds _) = conds
foreachConditions _ = error "foreachConditions: not a Foreach"

-- | Whether any statement (recursively through If/Foreach and other
-- nested bodies) calls the named procedure in value position. Sufficient
-- for the activate procedure, whose occurrence calls are
-- @LetVal _ (CallExpr occName ..)@.
callsProcedure :: Text -> [VM.Stmt] -> Bool
callsProcedure name = any go
  where
    want = VM.Name name
    go (VM.LetVal _ e) = valCalls e
    go (VM.AssignVal _ e) = valCalls e
    go (VM.ExprStmt e) = valCalls e
    go (VM.Return e) = valCalls e
    go (VM.If _ t e) = callsProcedure name t || callsProcedure name e
    go (VM.Foreach _ _ _ _ body) = callsProcedure name body
    go (VM.DrainReactivationQueue _ body) = callsProcedure name body
    go _ = False
    valCalls (VM.CallExpr n _) = n == want
    valCalls _ = False

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
  [(VM.ArgIndex, VM.ValExpr)] ->
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
    [ testCase "leq antisymmetry: active occurrence's partner args constrained" $ do
        -- antisymmetry @ leq(X, Y), leq(Y, X) <=> X = Y.
        -- Occurrence 3 (the second head) is elided as a passive symmetric
        -- occurrence (see passiveOccurrencesTests); the surviving
        -- occurrence 2 lifts both equalities into its partner Foreach.
        prog <- compileOrFail [("order.chr", leqSource)]
        assertForeachConditions
          prog
          "occurrence_order__leq2_2"
          [(VM.ArgIndex 1, VM.Var "X_0"), (VM.ArgIndex 0, VM.Var "X_1")],
      testCase "leq idempotence: active occurrence's partner args constrained" $ do
        -- idempotence @ leq(X, Y) \ leq(X, Y) <=> true.
        -- Occurrence 5 (the kept head) is elided as subsumed by the
        -- removed head; occurrence 4 survives.
        prog <- compileOrFail [("order.chr", leqSource)]
        assertForeachConditions
          prog
          "occurrence_order__leq2_4"
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
    exprHasSelfEqual (VM.BEqual (VM.Var "X_0") (VM.Var "X_1")) = True
    exprHasSelfEqual (VM.BEqual (VM.Var "X_1") (VM.Var "X_0")) = True
    exprHasSelfEqual (VM.BAnd a b) = exprHasSelfEqual a || exprHasSelfEqual b
    exprHasSelfEqual _ = False

-- ---------------------------------------------------------------------------
-- Passive occurrences
-- ---------------------------------------------------------------------------

-- | A non-symmetric two-head simplification: the two heads share only one
-- variable (in different positions), so neither occurrence is passive.
nonSymSource :: Text
nonSymSource =
  ":- module(m, [nsym/2]).\n\
  \:- chr_constraint nsym/2.\n\
  \r @ nsym(X, Y), nsym(Y, Z) <=> true.\n"

passiveOccurrencesTests :: TestTree
passiveOccurrencesTests =
  testGroup
    "Passive occurrences"
    [ testCase "leq: passive occurrence procedures are elided" $ do
        prog <- compileOrFail [("order.chr", leqSource)]
        -- Occurrence 3 (antisymmetry, by symmetry) and occurrence 5
        -- (idempotence, kept head subsumed by removed) are passive, so no
        -- procedure is emitted for them.
        assertAbsent prog "occurrence_order__leq2_3"
        assertAbsent prog "occurrence_order__leq2_5"
        -- Every active occurrence is still present, with its ωr number
        -- unchanged (numbering runs before the passivity pass).
        mapM_
          (assertPresent prog)
          [ "occurrence_order__leq2_1",
            "occurrence_order__leq2_2",
            "occurrence_order__leq2_4",
            "occurrence_order__leq2_6",
            "occurrence_order__leq2_7"
          ],
      testCase "leq: activate does not call passive occurrences" $ do
        prog <- compileOrFail [("order.chr", leqSource)]
        case findProcedure prog "activate_order__leq2" of
          Nothing -> assertFailure "activate_order__leq2 not found"
          Just p -> do
            assertBool "activate must not call passive occurrence 3" $
              not (callsProcedure "occurrence_order__leq2_3" p.body)
            assertBool "activate must not call passive occurrence 5" $
              not (callsProcedure "occurrence_order__leq2_5" p.body)
            mapM_
              ( \n ->
                  assertBool ("activate must still call " ++ show n) $
                    callsProcedure n p.body
              )
              [ "occurrence_order__leq2_2",
                "occurrence_order__leq2_4",
                "occurrence_order__leq2_6",
                "occurrence_order__leq2_7"
              ],
      testCase "non-symmetric two-head rule keeps both occurrences" $ do
        prog <- compileOrFail [("m.chr", nonSymSource)]
        assertPresent prog "occurrence_m__nsym2_1"
        assertPresent prog "occurrence_m__nsym2_2"
    ]
  where
    assertAbsent prog n =
      assertBool (show n ++ " should be elided (passive)") $
        isNothing (findProcedure prog n)
    assertPresent prog n =
      assertBool (show n ++ " should be present") $
        isJust (findProcedure prog n)
