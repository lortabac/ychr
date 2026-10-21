{-# LANGUAGE OverloadedStrings #-}

-- | Pure compilation tests: assertions about the VM code emitted by
-- 'YCHR.Internal.Compile.compile' for representative CHR programs. These tests
-- inspect the generated 'YCHR.Internal.VM.Program' AST directly without running
-- it through the interpreter.
module YCHR.CompileTest (tests) where

import Data.Map.Strict qualified as Map
import Data.Maybe (isJust, isNothing)
import Data.Text (Text)
import Data.Text qualified as T
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertEqual, assertFailure, testCase, (@?=))
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..))
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Types qualified as Types
import YCHR.Internal.VM qualified as VM
import YCHR.TestHelpers (compileOrFail)

-- | The VM code 'YCHR.Internal.Compile.compile' emits for representative CHR programs.
tests :: TestTree
tests =
  testGroup
    "YCHR.Internal.Compile"
    [ indexConditionPushdownTests,
      passiveOccurrencesTests,
      distinctnessElisionTests,
      boolPatternTests,
      softGuardWrapTests,
      callablesDispatchTests,
      aggregateFoldTests,
      aggregateResultTests,
      aggregateGoalTests,
      selectionTests,
      nestedAggregateTests
    ]

-- ---------------------------------------------------------------------------
-- Shared helpers
-- ---------------------------------------------------------------------------

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

-- | The index conditions of a @Foreach@.
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

-- | Every boolean expression tested by an @If@ anywhere in a statement
-- list, flattened through nested bodies and through the @BoolExpr@
-- connectives. Guard tests reach the VM as @If@ conditions, so this is
-- how a test asks "what does the compiler check here?".
ifConditions :: [VM.Stmt] -> [VM.BoolExpr]
ifConditions = concatMap go
  where
    go (VM.If e t f) = flatten e ++ ifConditions t ++ ifConditions f
    go (VM.Foreach _ _ _ _ body) = ifConditions body
    go (VM.DrainReactivationQueue _ body) = ifConditions body
    go _ = []
    flatten e =
      e : case e of
        VM.BNot a -> flatten a
        VM.BAnd a b -> flatten a ++ flatten b
        VM.BOr a b -> flatten a ++ flatten b
        VM.BEvalDeep a -> flatten a
        VM.BSoftGuard a -> flatten a
        _ -> []

-- | Look up a procedure by name in a compiled program.
findProcedure :: CompiledProgram -> Text -> Maybe VM.Procedure
findProcedure prog wanted =
  let want = VM.Name wanted
   in case filter (\p -> p.name == want) prog.program.procedures of
        [p] -> Just p
        _ -> Nothing

-- | Find the generated fold procedure for the aggregate at source index
-- @aggIdx@ of the @userIdx@-th rule of a program with @userRules@ user
-- rules. The absolute rule index — and therefore the procedure name —
-- depends on how many rules the stdlib contributes, so it is counted from
-- the end rather than pinned.
findAggregateProcedure :: CompiledProgram -> Int -> Int -> Int -> Maybe VM.Procedure
findAggregateProcedure prog userRules userIdx aggIdx =
  findProcedure prog (T.pack ("aggregate_" <> show ruleIdx <> "_" <> show aggIdx))
  where
    ruleIdx = length prog.program.ruleNames - userRules + userIdx

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
-- LEQ surface source
-- ---------------------------------------------------------------------------

-- | The leq program. A copy of the one in RunTest, so this module is
-- self-contained.
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
          [(VM.ArgIndex 1, VM.Var "$X_0"), (VM.ArgIndex 0, VM.Var "$X_1")],
      testCase "leq idempotence: active occurrence's partner args constrained" $ do
        -- idempotence @ leq(X, Y) \ leq(X, Y) <=> true.
        -- Occurrence 5 (the kept head) is elided as subsumed by the
        -- removed head; occurrence 4 survives.
        prog <- compileOrFail [("order.chr", leqSource)]
        assertForeachConditions
          prog
          "occurrence_order__leq2_4"
          [(VM.ArgIndex 0, VM.Var "$X_0"), (VM.ArgIndex 1, VM.Var "$X_1")],
      testCase "leq transitivity: single shared variable lifted" $ do
        -- transitivity @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).
        -- Each occurrence has exactly one HNF equality on the partner.
        prog <- compileOrFail [("order.chr", leqSource)]
        assertForeachConditions
          prog
          "occurrence_order__leq2_6"
          [(VM.ArgIndex 1, VM.Var "$X_0")]
        assertForeachConditions
          prog
          "occurrence_order__leq2_7"
          [(VM.ArgIndex 0, VM.Var "$X_1")],
      testCase "leq reflexivity: no partners, equality stays residual" $ do
        -- reflexivity @ leq(X, X) <=> true.
        -- The Foreach is absent (single-headed rule), and the residual
        -- check guard contains the active-self equality.
        prog <- compileOrFail [("order.chr", leqSource)]
        case findProcedure prog "occurrence_order__leq2_1" of
          Nothing -> assertFailure "occurrence_order__leq2_1 not found"
          Just p -> do
            findForeach p.body @?= Nothing
            -- The residual check should contain Equal $X_0 $X_1.
            let hasSelfEqual = any containsSelfEqual p.body
            assertBool "expected residual Equal $X_0 $X_1" hasSelfEqual
    ]
  where
    containsSelfEqual (VM.If e _ _) = exprHasSelfEqual e
    containsSelfEqual _ = False
    exprHasSelfEqual (VM.BEqual (VM.Var "$X_0") (VM.Var "$X_1")) = True
    exprHasSelfEqual (VM.BEqual (VM.Var "$X_1") (VM.Var "$X_0")) = True
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

-- ---------------------------------------------------------------------------
-- Constraint-id distinctness elision
-- ---------------------------------------------------------------------------

-- | Two rules, one across constraint types and one within a single type.
-- @cross@'s partner can never be the same suspension as its active
-- constraint, so the generated distinctness test is statically true and
-- must be dropped; @same@'s partner can be, so its test must survive.
distinctnessSource :: Text
distinctnessSource =
  ":- module(m, [p/1, q/1, r/2]).\n\
  \:- chr_constraint p/1, q/1, r/2.\n\
  \cross @ p(X), q(Y) <=> true.\n\
  \same  @ r(X, Y), r(Y, Z) <=> true.\n"

distinctnessElisionTests :: TestTree
distinctnessElisionTests =
  testGroup
    "Constraint-id distinctness elision"
    [ testCase "a partner of a different constraint type needs no test" $ do
        prog <- compileOrFail [("m.chr", distinctnessSource)]
        assertBool "occurrence_m__p1_1 must not test id distinctness" $
          not (hasIdEqual prog "occurrence_m__p1_1")
        assertBool "occurrence_m__q1_1 must not test id distinctness" $
          not (hasIdEqual prog "occurrence_m__q1_1"),
      testCase "a partner of the same constraint type keeps its test" $ do
        prog <- compileOrFail [("m.chr", distinctnessSource)]
        -- Reciprocal to the test above: if the compiler ever stopped
        -- emitting distinctness tests altogether, the previous case
        -- would still pass and this one would fail.
        assertBool "occurrence_m__r2_1 must test id distinctness" $
          hasIdEqual prog "occurrence_m__r2_1"
        assertBool "occurrence_m__r2_2 must test id distinctness" $
          hasIdEqual prog "occurrence_m__r2_2"
    ]
  where
    hasIdEqual prog procName =
      case findProcedure prog procName of
        Nothing -> error ("procedure not found: " ++ show procName)
        Just p -> any isIdEqual (ifConditions p.body)
    isIdEqual (VM.BIdEqual _ _) = True
    isIdEqual _ = False

-- ---------------------------------------------------------------------------
-- Boolean constructors in pattern position
-- ---------------------------------------------------------------------------

-- | @true@ / @false@ in a head or equation pattern. Their /values/ are
-- compiled to @BoolLit@, so the pattern side has to test for a boolean
-- too: a @BMatchTerm@ against the atom @prelude__true@ would never
-- match a @VBool@ and the rule would silently never fire.
boolPatternSource :: Text
boolPatternSource =
  ":- module(m, [go/2, neg/1]).\n\
  \:- chr_constraint go(bool, any).\n\
  \:- function neg(bool) -> bool.\n\
  \neg(true) -> false.\n\
  \neg(false) -> true.\n\
  \r @ go(true, R) <=> R = 1.\n"

boolPatternTests :: TestTree
boolPatternTests =
  testGroup
    "Boolean constructors in pattern position"
    [ testCase "head pattern tests a boolean, not an atom functor" $ do
        prog <- compileOrFail [("m.chr", boolPatternSource)]
        assertBoolPattern prog "occurrence_m__go2_1" True,
      testCase "equation pattern tests a boolean, not an atom functor" $ do
        prog <- compileOrFail [("m.chr", boolPatternSource)]
        assertBoolPattern prog "func_m__neg1" True
        assertBoolPattern prog "func_m__neg1" False
    ]
  where
    -- The scrutinee must be the pattern's operand, not just any
    -- expression: an equality between two literals would satisfy a
    -- looser check while leaving the argument untested.
    testsOperand b (VM.BEqual (VM.Var _) (VM.Lit (VM.BoolLit b'))) = b' == b
    testsOperand b (VM.BEqual (VM.FieldArg _ _) (VM.Lit (VM.BoolLit b'))) = b' == b
    testsOperand _ _ = False
    isBoolFunctorTest (VM.BMatchTerm _ f 0) =
      f `elem` [VM.Name "prelude__true", VM.Name "prelude__false"]
    isBoolFunctorTest _ = False
    assertBoolPattern prog procName b =
      case findProcedure prog procName of
        Nothing -> assertFailure $ "procedure not found: " ++ show procName
        Just p -> do
          let conds = ifConditions p.body
          assertBool
            (show procName ++ ": expected its operand tested against " ++ show b)
            (any (testsOperand b) conds)
          assertBool
            (show procName ++ ": bool pattern must not compile to BMatchTerm")
            (not (any isBoolFunctorTest conds))

-- ---------------------------------------------------------------------------
-- Soft-guard wrapping
-- ---------------------------------------------------------------------------

-- | A program with a user guard and a non-linear head.
softGuardSource :: Text
softGuardSource =
  ":- module(m, [g/1, eq/2]).\n\
  \:- use_module(library(prelude)).\n\
  \:- chr_constraint g(int), eq(int, int).\n\
  \guarded @ g(N) <=> N > 0 | true.\n\
  \nonlinear @ eq(X, X) <=> true.\n"

-- | 'softenGuard' wraps a rule-occurrence guard residual in
-- 'VM.BSoftGuard' only when the residual can actually raise — in
-- practice, when it contains a @BFromVal@. A residual that is a pure
-- @BEqual@ conjunction is total (ask equality answers @False@ on
-- unbound operands) and is emitted unwrapped, so the hot path pays
-- nothing.
--
-- Both halves matter and neither is covered by the golden tests: a
-- @canRaise@ stuck at @True@ would only cost performance, and a
-- @canRaise@ stuck at @False@ would be caught by the goldens but not
-- explained by them.
softGuardWrapTests :: TestTree
softGuardWrapTests =
  testGroup
    "soft-guard wrapping of guard residuals"
    [ testCase "a user-written guard is wrapped" $ do
        prog <- compileOrFail [("m.chr", softGuardSource)]
        assertBool
          "expected the N > 0 residual to be wrapped in BSoftGuard"
          (hasSoftGuard prog "occurrence_m__g1_1"),
      testCase "an HNF equality residual is left unwrapped" $ do
        prog <- compileOrFail [("m.chr", softGuardSource)]
        assertBool
          "expected an equality-only residual to be emitted unwrapped"
          (not (hasSoftGuard prog "occurrence_m__eq2_1"))
    ]
  where
    isSoftGuard (VM.BSoftGuard _) = True
    isSoftGuard _ = False
    hasSoftGuard prog procName =
      case findProcedure prog procName of
        Nothing -> error ("procedure not found: " ++ show procName)
        Just p -> any isSoftGuard (ifConditions p.body)

-- ---------------------------------------------------------------------------
-- Callables dispatch table
-- ---------------------------------------------------------------------------

-- | The compiler emits a /table/ for dynamic calls, not a set of
-- @call_N@ dispatcher procedures: one entry per user-defined function
-- and per lifted lambda, keyed by the shape of the closure value that
-- designates it, and every @'$call'@ compiles to the closure-apply
-- construct that consults it.
--
-- These tests pin the table's shape and the absence of @call_N@
-- dispatchers. The behavior the table encodes is exercised at run time
-- by @RunTest@ and the @closure_dispatch_errors@ / @lambda_test@ golden
-- directories, on both backends.
callablesDispatchTests :: TestTree
callablesDispatchTests =
  testGroup
    "Callables dispatch"
    [ testCase "one entry per function, with no duplicate keys" $ do
        prog <- compileOrFail [("order.chr", leqSource)]
        assertEqual
          "one callables entry per function"
          (length prog.allFunctions)
          (length prog.program.callables)
        -- The runtime builds a Map, which keeps the last entry for a
        -- repeated key silently; the table must not rely on that.
        assertEqual
          "distinct callables keys"
          (length prog.program.callables)
          (Map.size (Map.fromList prog.program.callables)),
      testCase "a function reference is keyed by flat name and arity" $ do
        prog <- compileOrFail [("order.chr", leqSource)]
        assertEqual
          "prelude:call/2 entry"
          (Just "func_prelude__call2")
          (lookupCallable prog (funRefKey "prelude:call" 2)),
      testCase "a lifted lambda is keyed by its identity and declared arity" $ do
        prog <- compileOrFail [("m.chr", lambdaSource)]
        case filter isLiftedLambda prog.allFunctions of
          [func] -> do
            -- The lifted function is arity 5 (three declared parameters
            -- plus two captures) and lives in module @m@, so its
            -- procedure is @func_m____lambda_05@ and its closure
            -- identity is @m____lambda_0@: the VM encoding the
            -- desugarer bakes into the closure term.
            assertEqual
              "lifted lambda qualified name"
              (Types.QualifiedName "m" "__lambda_0")
              func.name
            assertEqual
              "lifted lambda callables entry"
              (Just "func_m____lambda_05")
              ( lookupCallable
                  prog
                  (lambdaKey (VM.Name "m____lambda_0") 3)
              )
          _ -> assertFailure "expected exactly one lifted lambda",
      testCase "no call_N dispatcher is emitted for any arity" $ do
        prog <- compileOrFail [("order.chr", leqSource)]
        mapM_
          ( \n ->
              assertBool
                ("call_" ++ show n ++ " must not exist")
                (isNothing (findProcedure prog ("call_" <> T.pack (show n))))
          )
          [1 .. 12 :: Int],
      testCase "a dynamic call compiles to the closure-apply construct" $ do
        prog <- compileOrFail [("m.chr", lambdaSource)]
        assertBool
          "expected an ApplyClosure in some procedure body"
          (any (hasApplyClosure . (.body)) prog.program.procedures)
    ]
  where
    funRefKey identity arity =
      VM.CallableKey
        { functor = VM.funRefFunctor,
          identity = identity,
          arity = arity
        }
    lambdaKey identity arity =
      VM.CallableKey
        { functor = VM.lambdaClosureFunctor,
          identity = identity,
          arity = arity
        }
    lookupCallable :: CompiledProgram -> VM.CallableKey -> Maybe Text
    lookupCallable prog key =
      case lookup key prog.program.callables of
        Just (VM.Name n) -> Just n
        Nothing -> Nothing
    isLiftedLambda :: D.Function -> Bool
    isLiftedLambda func = T.isPrefixOf "__lambda_" func.name.baseName

-- | Does any expression in these statements contain the closure-apply
-- construct? A dynamic call site that still compiled to a @call_N@
-- reference would leave the table unconsumed.
hasApplyClosure :: [VM.Stmt] -> Bool
hasApplyClosure = any goStmt
  where
    goStmt s = case s of
      VM.LetVal _ e -> goVal e
      VM.LetId _ e -> goId e
      VM.AssignVal _ e -> goVal e
      VM.AssignId _ e -> goId e
      VM.If c ts es -> goBool c || any goStmt ts || any goStmt es
      VM.Foreach _ _ _ conds body ->
        any (goVal . snd) conds || any goStmt body
      VM.Continue _ -> False
      VM.Break _ -> False
      VM.Return e -> goVal e
      VM.ExprStmt e -> goVal e
      VM.BoolExprStmt e -> goBool e
      VM.Store e -> goId e
      VM.Kill e -> goId e
      VM.AddHistory _ _ -> False
      VM.DrainReactivationQueue _ body -> any goStmt body
      VM.TellTerm _ g es -> goVal g || any goVal es
      VM.PushFrame _ -> False
    goVal e = case e of
      VM.ApplyClosure {} -> True
      VM.Var _ -> False
      VM.Lit _ -> False
      VM.CallExpr _ args -> any goArg args
      VM.HostCall _ es -> any goVal es
      VM.EvalDeep e' -> goVal e'
      VM.EvalIs e' -> goVal e'
      VM.NewVar -> False
      VM.MakeTerm _ es -> any goVal es
      VM.GetArg e' _ -> goVal e'
      VM.FieldArg e' _ -> goId e'
      VM.FieldType e' -> goId e'
    goArg (VM.AVal e) = goVal e
    goArg (VM.AId e) = goId e
    goBool b = case b of
      VM.BLit _ -> False
      VM.BNot e -> goBool e
      VM.BAnd a b' -> goBool a || goBool b'
      VM.BOr a b' -> goBool a || goBool b'
      VM.BMatchTerm e _ _ -> goVal e
      VM.BEqual a b' -> goVal a || goVal b'
      VM.BIdEqual a b' -> goId a || goId b'
      VM.BAlive e -> goId e
      VM.BIsConstraintType e _ -> goId e
      VM.BNotInHistory _ ids -> any goId (VM.historyIdsList ids)
      VM.BUnify a b' -> goVal a || goVal b'
      VM.BFromVal e -> goVal e
      VM.BEvalDeep e -> goBool e
      VM.BSoftGuard e -> goBool e
    goId e = case e of
      VM.IdVar _ -> False
      VM.CreateConstraint _ es -> any goVal es

-- | A module whose only lambda takes three parameters and captures two
-- free variables, so the lifted function has arity 5 and its closure
-- arity is 4.
lambdaSource :: Text
lambdaSource =
  ":- module(m, [go/3, mk/2]).\n\
  \:- use_module(library(prelude)).\n\
  \:- chr_constraint go(any, any, any).\n\
  \:- function mk/2.\n\
  \mk(X, Y) -> fun(A, B, C) -> X + Y + A + B + C end.\n\
  \r @ go(X, Y, R) <=> F is mk(X, Y), R is '$call'(F, 1, 2, 3).\n"

--------------------------------------------------------------------------------
-- Aggregate folds
--------------------------------------------------------------------------------

-- | A rule whose head carries one aggregate over a goal.
aggregateSource :: Text
aggregateSource =
  ":- module(aggm, [c/1, d/1, n/2]).\n\
  \:- use_module(library(aggregates)).\n\
  \:- chr_constraint c/1, d/1, n/2.\n\
  \\n\
  \c(X), count(d(X), N) ==> n(X, N).\n"

-- | A simplification rule with an aggregate: it removes its only regular
-- head, and still has to fire at most once per combination of regular heads.
aggregateHistorySource :: Text
aggregateHistorySource =
  ":- module(aggh, [c/1, d/1, n/2]).\n\
  \:- use_module(library(aggregates)).\n\
  \:- chr_constraint c/1, d/1, n/2.\n\
  \\n\
  \c(X), count(d(X), N) <=> n(X, N).\n"

-- | A rule shaped like a symmetric simplification, plus an aggregate. Both
-- of its occurrences have to be tried: the later one would be marked passive
-- without the aggregate exemption.
aggregatePassiveSource :: Text
aggregatePassiveSource =
  ":- module(aggp, [c/2, d/1]).\n\
  \:- use_module(library(aggregates)).\n\
  \:- chr_constraint c/2, d/1.\n\
  \\n\
  \passive @ c(X, Y) \\ c(Y, X), count(d(X), N) <=> true.\n"

-- | Every statement of a body, flattened through nested bodies.
nestedStmts :: [VM.Stmt] -> [VM.Stmt]
nestedStmts = concatMap go
  where
    go s =
      s : case s of
        VM.If _ t e -> nestedStmts t ++ nestedStmts e
        VM.Foreach _ _ _ _ b -> nestedStmts b
        VM.DrainReactivationQueue _ b -> nestedStmts b
        _ -> []

-- | Every @BUnify@ reachable from the boolean positions of a body, with
-- the boolean connectives flattened.
bunifyExprs :: [VM.Stmt] -> [VM.BoolExpr]
bunifyExprs = concatMap go
  where
    go s = case s of
      VM.If b t e -> flatten b ++ bunifyExprs t ++ bunifyExprs e
      VM.BoolExprStmt b -> flatten b
      VM.Foreach _ _ _ _ b -> bunifyExprs b
      VM.DrainReactivationQueue _ b -> bunifyExprs b
      _ -> []
    flatten b = case b of
      VM.BUnify {} -> [b]
      VM.BAnd a c -> flatten a ++ flatten c
      VM.BOr a c -> flatten a ++ flatten c
      VM.BNot a -> flatten a
      VM.BSoftGuard a -> flatten a
      VM.BEvalDeep a -> flatten a
      _ -> []

-- | Whether a statement mutates the runtime's bookkeeping. An aggregate
-- procedure is called from a guard, so none of these may be reachable
-- from one.
mutatingStmt :: VM.Stmt -> Bool
mutatingStmt s = case s of
  VM.Store _ -> True
  VM.Kill _ -> True
  VM.AddHistory {} -> True
  VM.TellTerm {} -> True
  VM.DrainReactivationQueue {} -> True
  _ -> False

-- | Whether a boolean expression is a history guard.
isNotInHistory :: VM.BoolExpr -> Bool
isNotInHistory (VM.BNotInHistory _ _) = True
isNotInHistory _ = False

-- | Whether a statement writes the firing history.
isAddHistory :: VM.Stmt -> Bool
isAddHistory (VM.AddHistory _ _) = True
isAddHistory _ = False

aggregateFoldTests :: TestTree
aggregateFoldTests =
  testGroup
    "aggregate folds"
    [ testCase "a rule with an aggregate gets one fold procedure" $ do
        prog <- compileOrFail [("m.chr", aggregateSource)]
        case findAggregateProcedure prog 1 0 0 of
          Nothing -> assertFailure "no fold procedure for aggregate_0"
          Just p -> do
            assertBool "expected parameters" (not (null p.params))
            -- The procedure is tagged as a function with a reserved name,
            -- so the tracer renders it without pretending it is a user
            -- function and no export clause picks it up.
            case p.procKind of
              VM.PKFunction qn _ -> qn.moduleName @?= "$aggregate"
              other -> assertFailure ("unexpected proc kind: " ++ show other),
      testCase "the fold procedure only reads, apart from binding its out-cells" $ do
        prog <- compileOrFail [("m.chr", aggregateSource)]
        case findAggregateProcedure prog 1 0 0 of
          Nothing -> assertFailure "no fold procedure for aggregate_0"
          Just p -> do
            assertBool
              ( "a fold procedure reachable from a guard must not"
                  ++ " store, kill, add history or tell"
              )
              (not (any mutatingStmt (nestedStmts p.body)))
            -- Every binding it does make targets an out-cell, and the
            -- out-cell is the left operand: unification binds its left
            -- operand and returns that operand's observers, so this is
            -- what keeps the binding from enqueuing reactivation.
            assertBool
              "expected at least one out-cell binding"
              (not (null (bunifyExprs p.body)))
            mapM_
              ( \b -> case b of
                  VM.BUnify (VM.Var n) _ ->
                    assertBool
                      ( "bunify binds something that is not an out-cell: "
                          ++ show n.unName
                      )
                      ("aggregate_out_" `T.isPrefixOf` n.unName)
                  other -> assertFailure ("unexpected bunify shape: " ++ show other)
              )
              (bunifyExprs p.body),
      testCase "the guard calls the fold inside a soft guard" $ do
        prog <- compileOrFail [("m.chr", aggregateSource)]
        case findProcedure prog "occurrence_aggm__c1_1" of
          Nothing -> assertFailure "no c/1 occurrence procedure"
          Just p ->
            assertBool
              "expected the aggregate call to be soft-guarded"
              (any isSoftGuard (ifConditions p.body))
            where
              isSoftGuard (VM.BSoftGuard _) = True
              isSoftGuard _ = False,
      testCase "a rule that removes a regular head keeps a firing history" $ do
        prog <- compileOrFail [("m.chr", aggregateHistorySource)]
        case findProcedure prog "occurrence_aggh__c1_1" of
          Nothing -> assertFailure "no c/1 occurrence procedure"
          Just p -> do
            assertBool
              "expected a history guard"
              (any isNotInHistory (ifConditions p.body))
            assertBool
              "expected a history write"
              (any isAddHistory (nestedStmts p.body)),
      testCase "an aggregate rule's occurrences are never passive" $ do
        prog <- compileOrFail [("m.chr", aggregatePassiveSource)]
        mapM_
          ( \name -> case findProcedure prog (T.pack name) of
              Just _ -> pure ()
              Nothing -> assertFailure ("missing occurrence procedure " ++ name)
          )
          ["occurrence_aggp__c2_1", "occurrence_aggp__c2_2"],
      testCase "a program without aggregates emits no fold procedure" $ do
        prog <- compileOrFail [("m.chr", leqSource)]
        let folded =
              [ p.name.unName
              | p <- prog.program.procedures,
                "aggregate_" `T.isPrefixOf` p.name.unName
              ]
        folded @?= []
    ]

--------------------------------------------------------------------------------
-- Aggregate goal occurrences
--------------------------------------------------------------------------------

-- | A rule whose aggregate goal constraint is told after its head: the
-- ordinary occurrence cannot fire (its guard fails while the store is
-- empty), so only a goal occurrence of @d\/1@ can reach the rule.
lateGoalSource :: Text
lateGoalSource =
  ":- module(aggl, [c/1, d/1, n/2]).\n\
  \:- use_module(library(aggregates)).\n\
  \:- chr_constraint c/1, d/1, n/2.\n\
  \\n\
  \c(X), count(d(X), N) ==> N > 0 | n(X, N).\n"

-- | A goal with two conjuncts of the same type: the fold needs a
-- distinctness test between their suspensions.
distinctGoalSource :: Text
distinctGoalSource =
  ":- module(aggd, [c/1, d/1, n/2]).\n\
  \:- use_module(library(aggregates)).\n\
  \:- chr_constraint c/1, d/1, n/2.\n\
  \\n\
  \c(X), count((d(_), d(_)), N) ==> N > 0 | n(X, N).\n"

-- | A goal whose second conjunct must be looped outside the regular-head
-- loops: @e\/1@ is not a head, so a goal occurrence of @d\/1@ nests the
-- @e\/1@ loop outside the @c\/1@ partner loop.
nestGoalSource :: Text
nestGoalSource =
  ":- module(aggn, [c/1, d/1, e/1, n/2]).\n\
  \:- use_module(library(aggregates)).\n\
  \:- chr_constraint c/1, d/1, e/1, n/2.\n\
  \\n\
  \c(X), count((d(X), e(X)), N) ==> N > 0 | n(X, N).\n"

-- | A rule whose aggregate goal carries a @?@ guard: the fold evaluates
-- it, the location phase must not (it can only over-approximate there).
guardGoalSource :: Text
guardGoalSource =
  ":- module(aggq, [c/1, d/1, n/2]).\n\
  \:- use_module(library(aggregates)).\n\
  \:- chr_constraint c/1, d/1, n/2.\n\
  \\n\
  \c(X), count((d(Y), ? Y > 1), N) ==> n(X, N).\n"

-- | A rule with no aggregate of its own that removes a constraint which
-- another rule's aggregate goal observes: its firing has to run the
-- removal step.
removalStepSource :: Text
removalStepSource =
  ":- module(aggr, [task/1, depends/2, done/1, ready/1]).\n\
  \:- use_module(library(aggregates)).\n\
  \:- chr_constraint task/1, depends/2, done/1, ready/1.\n\
  \\n\
  \task(T), \\+ depends(T, _) ==> ready(T).\n\
  \done(D) \\ depends(_, D) <=> true.\n"

-- | The argument lists of every call to the named procedure, in
-- traversal order.
callsTo :: Text -> [VM.Stmt] -> [[VM.CallArg]]
callsTo name = concatMap stmt
  where
    want = VM.Name name
    stmt s = case s of
      VM.LetVal _ e -> val e
      VM.AssignVal _ e -> val e
      VM.ExprStmt e -> val e
      VM.Return e -> val e
      VM.If _ t f -> callsTo name t ++ callsTo name f
      VM.Foreach _ _ _ _ b -> callsTo name b
      VM.DrainReactivationQueue _ b -> callsTo name b
      _ -> []
    val e = case e of
      VM.CallExpr n args -> [args | n == want] ++ concatMap arg args
      VM.HostCall _ es -> concatMap val es
      VM.EvalDeep x -> val x
      VM.EvalIs x -> val x
      VM.ApplyClosure f es -> val f ++ concatMap val es
      VM.MakeTerm _ es -> concatMap val es
      VM.GetArg x _ -> val x
      VM.FieldArg i _ -> idVal i
      VM.FieldType i -> idVal i
      _ -> []
    arg a = case a of
      VM.AVal v -> val v
      VM.AId i -> idVal i
    idVal i = case i of
      VM.IdVar _ -> []
      VM.CreateConstraint _ es -> concatMap val es

-- | The labels of every 'Foreach' reachable from a statement list, in
-- pre-order: outer loops before inner ones.
foreachLabels :: [VM.Stmt] -> [VM.Label]
foreachLabels = concatMap go
  where
    go (VM.Foreach l _ _ _ b) = l : foreachLabels b
    go (VM.If _ t f) = foreachLabels t ++ foreachLabels f
    go (VM.DrainReactivationQueue _ b) = foreachLabels b
    go _ = []

-- | Is this an id comparison against an aggregate's goal suspension?
isSuspDistinct :: VM.BoolExpr -> Bool
isSuspDistinct (VM.BIdEqual (VM.IdVar a) (VM.IdVar b)) =
  any ("$aggregate_susp_" `T.isPrefixOf`) [a.unName, b.unName]
isSuspDistinct _ = False

-- | Is this a @Store@?
isStoreStmt :: VM.Stmt -> Bool
isStoreStmt (VM.Store _) = True
isStoreStmt _ = False

-- | Whether a boolean expression evaluates a goal's @?@ guard expression
-- (a host call under @bfrom-val . eval-deep@), as opposed to an aggregate
-- procedure call.
isGuardEval :: VM.BoolExpr -> Bool
isGuardEval (VM.BFromVal (VM.EvalDeep (VM.HostCall _ _))) = True
isGuardEval _ = False

-- | Whether every 'Store' reachable from a statement list sits under an
-- @If@ whose condition tests liveness. A goal occurrence is called by the
-- removal step with a dead constraint, so none of its stores may run
-- unguarded.
storesAliveGuarded :: [VM.Stmt] -> Bool
storesAliveGuarded = go False
  where
    go alive = all (one alive)
    one alive s = case s of
      VM.Store _ -> alive
      VM.If e t f ->
        let guarded = alive || any isAlive (flatten e)
         in go guarded t && go guarded f
      VM.Foreach _ _ _ _ b -> go alive b
      VM.DrainReactivationQueue _ b -> go alive b
      _ -> True
    flatten e =
      e : case e of
        VM.BNot a -> flatten a
        VM.BAnd a b -> flatten a ++ flatten b
        VM.BOr a b -> flatten a ++ flatten b
        VM.BEvalDeep a -> flatten a
        VM.BSoftGuard a -> flatten a
        _ -> []
    isAlive (VM.BAlive _) = True
    isAlive _ = False

aggregateGoalTests :: TestTree
aggregateGoalTests =
  testGroup
    "aggregate goal occurrences"
    [ testCase "a goal occurrence takes the removal-step flag, an ordinary one does not" $ do
        prog <- compileOrFail [("m.chr", lateGoalSource)]
        case findProcedure prog "occurrence_aggl__d1_1" of
          Nothing -> assertFailure "no d/1 goal occurrence procedure"
          Just p -> length p.params @?= 3
        case findProcedure prog "occurrence_aggl__c1_1" of
          Nothing -> assertFailure "no c/1 ordinary occurrence procedure"
          Just p -> length p.params @?= 2,
      testCase "activate calls the goal occurrence with the flag false" $ do
        prog <- compileOrFail [("m.chr", lateGoalSource)]
        case findProcedure prog "activate_aggl__d1" of
          Nothing -> assertFailure "no d/1 activate procedure"
          Just p ->
            callsTo "occurrence_aggl__d1_1" p.body
              @?= [ [ VM.AId (VM.IdVar "active"),
                      VM.AVal (VM.Var (VM.Name "$X_0")),
                      VM.AVal (VM.Lit (VM.BoolLit False))
                    ]
                  ],
      testCase "a goal occurrence's loops sit outside the head loops" $ do
        prog <- compileOrFail [("m.chr", nestGoalSource)]
        case findProcedure prog "occurrence_aggn__d1_1" of
          Nothing -> assertFailure "no d/1 goal occurrence procedure"
          Just p ->
            -- The active conjunct is d/1 at goal position 0, so the only
            -- loop is e/1 at goal position 1, outside the c/1 head loop.
            foreachLabels p.body
              @?= [VM.Label "aggregate_loop_0_1", VM.Label "L1"]
        -- The e/1 occurrence's active conjunct is at goal position 1 and
        -- its HNF guard compares a variable of the earlier d/1 conjunct
        -- with a fresh name, so the d/1 loop has to run first.
        case findProcedure prog "occurrence_aggn__e1_1" of
          Nothing -> assertFailure "no e/1 goal occurrence procedure"
          Just p ->
            foreachLabels p.body
              @?= [VM.Label "aggregate_loop_0_0", VM.Label "L1"],
      testCase "two same-type conjuncts in one goal must match distinct suspensions" $ do
        prog <- compileOrFail [("m.chr", distinctGoalSource)]
        case findAggregateProcedure prog 1 0 0 of
          Nothing -> assertFailure "no fold procedure"
          Just p -> do
            foreachLabels p.body
              @?= [VM.Label "aggregate_loop_0_0", VM.Label "aggregate_loop_0_1"]
            assertBool
              "expected a suspension distinctness test"
              (any isSuspDistinct (ifConditions p.body)),
      testCase "a goal occurrence stores its active constraint only while alive" $ do
        prog <- compileOrFail [("m.chr", lateGoalSource)]
        case findProcedure prog "occurrence_aggl__d1_1" of
          Nothing -> assertFailure "no d/1 goal occurrence procedure"
          Just p -> do
            assertBool
              "expected a store in the goal occurrence"
              (any isStoreStmt (nestedStmts p.body))
            assertBool
              "expected every store under a liveness test"
              (storesAliveGuarded p.body),
      testCase "a rule removing a goal-observed constraint runs the removal step" $ do
        prog <- compileOrFail [("m.chr", removalStepSource)]
        case findProcedure prog "occurrence_aggr__done1_1" of
          Nothing -> assertFailure "no done/1 occurrence procedure"
          Just p ->
            callsTo "occurrence_aggr__depends2_1" p.body
              @?= [ [ VM.AId (VM.IdVar "pId_0"),
                      VM.AVal (VM.Var (VM.Name "pArg_0_0")),
                      VM.AVal (VM.Var (VM.Name "pArg_0_1")),
                      VM.AVal (VM.Lit (VM.BoolLit True))
                    ]
                  ],
      testCase "the location phase drops ? guards; the fold keeps them" $ do
        prog <- compileOrFail [("m.chr", guardGoalSource)]
        case findProcedure prog "occurrence_aggq__d1_1" of
          Nothing -> assertFailure "no d/1 goal occurrence procedure"
          Just p ->
            assertBool
              "the location phase must not evaluate the guard"
              (not (any isGuardEval (ifConditions p.body)))
        case findAggregateProcedure prog 1 0 0 of
          Nothing -> assertFailure "no fold procedure"
          Just p ->
            assertBool
              "the fold must evaluate the guard"
              (any isGuardEval (ifConditions p.body)),
      testCase "a rule that removes nothing has no removal step" $ do
        prog <- compileOrFail [("m.chr", lateGoalSource)]
        case findProcedure prog "occurrence_aggl__c1_1" of
          Nothing -> assertFailure "no c/1 ordinary occurrence procedure"
          Just p -> callsTo "occurrence_aggl__d1_1" p.body @?= []
    ]

--------------------------------------------------------------------------------
-- Aggregate result patterns
--------------------------------------------------------------------------------

-- | A result pattern with a compound and a literal, plus one repeated
-- variable: the tests it induces must be emitted.
resultPatternSource :: Text
resultPatternSource =
  ":- module(aggrp, [c/1, d/1, out/2]).\n\
  \:- use_module(library(aggregates)).\n\
  \:- chr_constraint c/1, d/1, out/2.\n\
  \\n\
  \c(X), collect(Y, d(Y), [H, 2]) ==> out(H, X).\n\
  \c(X), collect(Y, d(Y), [A, A]) ==> out(A, X).\n"

-- | A shared variable inside a compound goal argument: the fold must test
-- the extracted value against the shared input instead of rebinding it.
compoundGoalSource :: Text
compoundGoalSource =
  ":- module(aggc, [c/1, e/1, n/2]).\n\
  \:- use_module(library(aggregates)).\n\
  \:- chr_type t ---> f(any).\n\
  \:- chr_constraint c/1, e/1, n/2.\n\
  \\n\
  \c(K), count(e(f(K)), N) ==> n(K, N).\n"

aggregateResultTests :: TestTree
aggregateResultTests =
  testGroup
    "aggregate result patterns"
    [ testCase "a literal test in the result pattern is emitted" $ do
        prog <- compileOrFail [("m.chr", resultPatternSource)]
        case findAggregateProcedure prog 2 0 0 of
          Nothing -> assertFailure "no fold procedure"
          Just p ->
            assertBool
              "expected the literal 2 to be tested against the payload"
              (any isTwoTest (ifConditions p.body)),
      testCase "a repeated result variable is bound once and tested" $ do
        prog <- compileOrFail [("m.chr", resultPatternSource)]
        case findAggregateProcedure prog 2 1 0 of
          Nothing -> assertFailure "no second fold procedure"
          Just p -> do
            length (bunifyExprs p.body) @?= 1
            assertBool
              "expected a test between the two payload paths"
              (any isPayloadTest (ifConditions p.body)),
      testCase "a shared variable in a compound goal argument is a test" $ do
        prog <- compileOrFail [("m.chr", compoundGoalSource)]
        case findAggregateProcedure prog 1 0 0 of
          Nothing -> assertFailure "no fold procedure"
          Just p -> do
            assertBool
              "expected the extracted value to be tested against the shared input"
              (any isSharedFieldTest (ifConditions p.body))
            assertBool
              "the shared input K must not be rebound in the fold"
              (not (any isVLet (nestedStmts p.body)))
    ]
  where
    isTwoTest (VM.BEqual (VM.Lit (VM.IntLit 2)) _) = True
    isTwoTest (VM.BEqual _ (VM.Lit (VM.IntLit 2))) = True
    isTwoTest _ = False
    isPayloadTest (VM.BEqual a b) = isPayloadPath a && isPayloadPath b
    isPayloadTest _ = False
    isPayloadPath (VM.Var n) = n.unName == "$aggregate_payload"
    isPayloadPath (VM.GetArg e _) = isPayloadPath e
    isPayloadPath _ = False
    isSharedFieldTest (VM.BEqual (VM.Var n) (VM.GetArg _ _)) =
      n.unName == "aggregate_shared_0"
    isSharedFieldTest (VM.BEqual (VM.GetArg _ _) (VM.Var n)) =
      n.unName == "aggregate_shared_0"
    isSharedFieldTest _ = False
    isVLet (VM.LetVal (VM.Name "K") _) = True
    isVLet _ = False

--------------------------------------------------------------------------------
-- Selection aggregates
--------------------------------------------------------------------------------

-- | An argmin over a goal with one shared variable (K) and two visible
-- ones (X and G).
argminSource :: Text
argminSource =
  ":- module(sela, [p/1, item/3, best/3]).\n\
  \:- chr_constraint p/1, item/3, best/3.\n\
  \\n\
  \p(K), argmin(X, item(K, X, G)) ==> best(K, X, G).\n"

-- | A takemin that removes the selected job.
takeminSource :: Text
takeminSource =
  ":- module(selt, [m/1, job/3, run/1]).\n\
  \:- chr_constraint m/1, job/3, run/1.\n\
  \\n\
  \m(M) \\ takemin(D, job(M, D, J)) <=> run(J).\n"

-- | Is this a @Kill@?
isKillStmt :: VM.Stmt -> Bool
isKillStmt (VM.Kill _) = True
isKillStmt _ = False

selectionTests :: TestTree
selectionTests =
  testGroup
    "selection aggregates"
    [ testCase "an argmin procedure binds one out-cell per visible goal variable" $ do
        prog <- compileOrFail [("m.chr", argminSource)]
        case findAggregateProcedure prog 1 0 0 of
          Nothing -> assertFailure "no selection procedure"
          Just p -> do
            let outs =
                  [ n.unName
                  | n <- p.params,
                    "aggregate_out_" `T.isPrefixOf` n.unName
                  ]
            -- X and G are bound; K is a shared input.
            length outs @?= 2
            length p.params @?= 3,
      testCase "the selection procedure only reads, apart from binding its out-cells" $ do
        prog <- compileOrFail [("m.chr", argminSource)]
        case findAggregateProcedure prog 1 0 0 of
          Nothing -> assertFailure "no selection procedure"
          Just p -> do
            assertBool
              "a selection procedure must not store, kill, add history or tell"
              (not (any mutatingStmt (nestedStmts p.body)))
            mapM_
              ( \b -> case b of
                  VM.BUnify (VM.Var n) _ ->
                    assertBool
                      ( "bunify binds something that is not an out-cell: "
                          ++ show n.unName
                      )
                      ("aggregate_out_" `T.isPrefixOf` n.unName)
                  other -> assertFailure ("unexpected bunify shape: " ++ show other)
              )
              (bunifyExprs p.body),
      testCase "an argmin firing kills nothing" $ do
        prog <- compileOrFail [("m.chr", argminSource)]
        case findProcedure prog "occurrence_sela__p1_1" of
          Nothing -> assertFailure "no p/1 occurrence procedure"
          Just p ->
            assertBool
              "an argmin keeps its goal's constraints"
              (not (any isKillStmt (nestedStmts p.body))),
      testCase "a takemin firing finds its match again before the kills" $ do
        prog <- compileOrFail [("m.chr", takeminSource)]
        case findProcedure prog "occurrence_selt__m1_1" of
          Nothing -> assertFailure "no m/1 occurrence procedure"
          Just p -> do
            let stmts = nestedStmts p.body
                label = VM.Label "selection_loop_0_0"
                selId = VM.IdVar "$selection_id_0_0"
                selected = VM.Kill selId
                position x = lookup x (zip stmts [0 :: Int ..])
            assertBool "expected the relocation loop" (label `elem` foreachLabels p.body)
            case (position (VM.Break label), position selected) of
              (Just b, Just k) ->
                assertBool "the break must come before the kill" (b < k)
              other -> assertFailure ("missing break or kill: " ++ show other)
            callsTo "occurrence_selt__job3_1" p.body
              @?= [ VM.AId selId
                      : [ VM.AVal (VM.FieldArg selId (VM.ArgIndex i))
                        | i <- [0, 1, 2]
                        ]
                      ++ [VM.AVal (VM.Lit (VM.BoolLit True))]
                  ]
    ]

--------------------------------------------------------------------------------
-- Nested aggregates
--------------------------------------------------------------------------------

-- | An aggregate nested in a goal: a @\\+@ inside a @count@.
nestedSource :: Text
nestedSource =
  ":- module(aggx, [c/1, d/1, e/1, n/2]).\n\
  \:- use_module(library(aggregates)).\n\
  \:- chr_constraint c/1, d/1, e/1, n/2.\n\
  \\n\
  \c(X), count((d(Y), \\+ e(Y)), N) ==> N > 0 | n(X, N).\n"

-- | The same type in the outer and the nested goal.
nestedSameTypeSource :: Text
nestedSameTypeSource =
  ":- module(aggy, [c/1, d/1, n/2]).\n\
  \:- use_module(library(aggregates)).\n\
  \:- chr_constraint c/1, d/1, n/2.\n\
  \\n\
  \c(X), count((d(Y), \\+ d(Y)), N) ==> N > 0 | n(X, N).\n"

-- | The procedure of the aggregate at @path@ in the last rule of a program
-- with one user rule.
findNestedProcedure :: CompiledProgram -> [Int] -> Maybe VM.Procedure
findNestedProcedure prog path =
  findProcedure
    prog
    (T.intercalate "_" ("aggregate" : map (T.pack . show) (ruleIdx : path)))
  where
    ruleIdx = length prog.program.ruleNames - 1

-- | How many @if@ conditions call the named procedure: an aggregate is
-- called from a condition, which 'callsTo' does not look into.
conditionCalls :: VM.Name -> [VM.Stmt] -> Int
conditionCalls name body =
  length [() | VM.BFromVal (VM.CallExpr n _) <- ifConditions body, n == name]

-- | Is this a @BSoftGuard@?
isSoftWrap :: VM.BoolExpr -> Bool
isSoftWrap (VM.BSoftGuard _) = True
isSoftWrap _ = False

-- | Is this a @BIdEqual@?
isIdTest :: VM.BoolExpr -> Bool
isIdTest (VM.BIdEqual _ _) = True
isIdTest _ = False

nestedAggregateTests :: TestTree
nestedAggregateTests =
  testGroup
    "nested aggregates"
    [ testCase "a nested aggregate gets a procedure named by its path" $ do
        prog <- compileOrFail [("m.chr", nestedSource)]
        assertBool "no outer procedure" (isJust (findNestedProcedure prog [0]))
        assertBool "no nested procedure" (isJust (findNestedProcedure prog [0, 1])),
      testCase "the fold calls the nested procedure in place, not soft-guarded" $ do
        prog <- compileOrFail [("m.chr", nestedSource)]
        case (findNestedProcedure prog [0], findNestedProcedure prog [0, 1]) of
          (Just outer, Just nested) -> do
            conditionCalls nested.name outer.body @?= 1
            assertBool
              "the call must not have its own soft guard"
              (not (any isSoftWrap (ifConditions outer.body)))
          _ -> assertFailure "missing aggregate procedures",
      testCase "goal occurrences come outer goal first, then the nested goal" $ do
        prog <- compileOrFail [("m.chr", nestedSameTypeSource)]
        -- d/1 at position 0 of the outer goal: the nested aggregate is
        -- skipped, so only the head loop is left.
        case findProcedure prog "occurrence_aggy__d1_1" of
          Nothing -> assertFailure "no outer d/1 goal occurrence"
          Just p -> foreachLabels p.body @?= [VM.Label "L1"]
        -- d/1 in the nested goal: the outer goal is looped at level 0,
        -- then the head.
        case findProcedure prog "occurrence_aggy__d1_2" of
          Nothing -> assertFailure "no nested d/1 goal occurrence"
          Just p ->
            foreachLabels p.body
              @?= [VM.Label "aggregate_loop_0_0", VM.Label "L1"],
      testCase "the location phase tests distinctness within one goal only" $ do
        prog <- compileOrFail [("m.chr", nestedSameTypeSource)]
        case findProcedure prog "occurrence_aggy__d1_2" of
          Nothing -> assertFailure "no nested d/1 goal occurrence"
          Just p ->
            assertBool
              "an outer-goal loop must not be compared with the nested active"
              (not (any isIdTest (ifConditions p.body))),
      testCase "the location phase does not compute a nested aggregate" $ do
        prog <- compileOrFail [("m.chr", nestedSource)]
        case ( findProcedure prog "occurrence_aggx__d1_1",
               findNestedProcedure prog [0],
               findNestedProcedure prog [0, 1]
             ) of
          (Just p, Just outer, Just nested) -> do
            -- The fire step computes the outer aggregate, which computes
            -- the nested one; the occurrence never calls it directly.
            conditionCalls outer.name p.body @?= 1
            conditionCalls nested.name p.body @?= 0
          _ -> assertFailure "missing procedures"
    ]
