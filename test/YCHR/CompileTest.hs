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
import YCHR.Embedded (stdlib)
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..))
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Types qualified as Types
import YCHR.Internal.VM qualified as VM
import YCHR.Run (compileModules)

tests :: TestTree
tests =
  testGroup
    "YCHR.Internal.Compile"
    [ indexConditionPushdownTests,
      passiveOccurrencesTests,
      distinctnessElisionTests,
      boolPatternTests,
      softGuardWrapTests,
      callablesDispatchTests
    ]

-- ---------------------------------------------------------------------------
-- Shared helpers
-- ---------------------------------------------------------------------------

compileOrFail :: [(FilePath, Text)] -> IO CompiledProgram
compileOrFail inputs = case compileModules stdlib False inputs of
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
-- These tests pin the table's shape and the absence of the old
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
