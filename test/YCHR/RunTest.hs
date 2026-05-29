{-# LANGUAGE OverloadedStrings #-}

module YCHR.RunTest (tests) where

import Control.Exception (SomeException, fromException, try)
import Data.Foldable (toList)
import Data.List (isInfixOf)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import YCHR.Display (displayMsg)
import YCHR.Run
  ( Chr,
    CompiledProgram (..),
    ConstraintType,
    Error (..),
    GoalRejection (..),
    Value (..),
    compileModules,
    equal,
    newVar,
    resolveQueryConstraint,
    runProgramWithGoal,
    runProgramWithQuery,
    tellConstraint,
    toSessionInput,
    withCHR,
  )
import YCHR.Runtime.Interpreter (HostCallFn (..), HostCallRegistry)
import YCHR.Runtime.Store (getStoreSnapshot, isSuspAlive)
import YCHR.Types
  ( Constraint (..),
    Identifier (..),
    Name (..),
    QualifiedConstraint (..),
    QualifiedName (..),
    Term (..),
    lookupSymbol,
  )
import YCHR.VM qualified as VM

tests :: TestTree
tests =
  testGroup
    "YCHR.Run"
    [ leqTests,
      fibTests,
      visibilityTests,
      queryErrorTests,
      queryBodyTests,
      unicodeTests,
      arityOverloadTests
    ]

-- ---------------------------------------------------------------------------
-- Shared helpers
-- ---------------------------------------------------------------------------

compileOrFail :: [(FilePath, Text)] -> IO CompiledProgram
compileOrFail inputs = case compileModules False inputs of
  Left err -> assertFailure $ show err
  Right (cp, _) -> pure cp

countAlive :: VM.ConstraintType -> Chr Int
countAlive cType = do
  snapshot <- getStoreSnapshot cType
  alives <- traverse isSuspAlive (toList snapshot)
  pure (length (filter id alives))

-- ---------------------------------------------------------------------------
-- LEQ surface source
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

lookupType :: CompiledProgram -> Identifier -> ConstraintType
lookupType prog ident =
  case lookupSymbol ident prog.symbolTable of
    Just ct -> ct
    Nothing -> error $ "constraint type not found: " ++ show ident

leqHostCalls :: HostCallRegistry
leqHostCalls = Map.empty

leqTests :: TestTree
leqTests =
  testGroup
    "LEQ handler (from surface language)"
    [ testCase "reflexivity: leq(3, 3) fires, store empty" $ do
        prog <- compileOrFail [("order.chr", leqSource)]
        let leqType = lookupType prog (Identifier (Qualified "order" "leq") 2)
        n <- withCHR (toSessionInput prog) leqHostCalls $ do
          tellConstraint (Unqualified "leq") [VInt 3, VInt 3]
          countAlive leqType
        n @?= 0,
      testCase "no rule fires: leq(1, 2) stays" $ do
        prog <- compileOrFail [("order.chr", leqSource)]
        let leqType = lookupType prog (Identifier (Qualified "order" "leq") 2)
        n <- withCHR (toSessionInput prog) leqHostCalls $ do
          tellConstraint (Unqualified "leq") [VInt 1, VInt 2]
          countAlive leqType
        n @?= 1,
      testCase "antisymmetry: leq(X, Y), leq(Y, X) unifies X=Y, store empty" $ do
        prog <- compileOrFail [("order.chr", leqSource)]
        let leqType = lookupType prog (Identifier (Qualified "order" "leq") 2)
        (n, areEqual) <- withCHR (toSessionInput prog) leqHostCalls $ do
          x <- newVar
          y <- newVar
          tellConstraint (Unqualified "leq") [x, y]
          tellConstraint (Unqualified "leq") [y, x]
          n <- countAlive leqType
          eq <- equal x y
          pure (n, eq)
        n @?= 0
        assertBool "X and Y should be unified" areEqual,
      testCase "transitivity: leq(1,2), leq(2,3) produces leq(1,3)" $ do
        prog <- compileOrFail [("order.chr", leqSource)]
        let leqType = lookupType prog (Identifier (Qualified "order" "leq") 2)
        n <- withCHR (toSessionInput prog) leqHostCalls $ do
          tellConstraint (Unqualified "leq") [VInt 1, VInt 2]
          tellConstraint (Unqualified "leq") [VInt 2, VInt 3]
          countAlive leqType
        n @?= 3,
      testCase "idempotence: leq(1,2), leq(1,2) removes duplicate" $ do
        prog <- compileOrFail [("order.chr", leqSource)]
        let leqType = lookupType prog (Identifier (Qualified "order" "leq") 2)
        n <- withCHR (toSessionInput prog) leqHostCalls $ do
          tellConstraint (Unqualified "leq") [VInt 1, VInt 2]
          tellConstraint (Unqualified "leq") [VInt 1, VInt 2]
          countAlive leqType
        n @?= 1,
      testCase "full cycle: leq(a,b), leq(b,c), leq(c,a) — all removed, all unified" $ do
        prog <- compileOrFail [("order.chr", leqSource)]
        let leqType = lookupType prog (Identifier (Qualified "order" "leq") 2)
        (n, eqAB, eqBC) <- withCHR (toSessionInput prog) leqHostCalls $ do
          a <- newVar
          b <- newVar
          c <- newVar
          tellConstraint (Unqualified "leq") [a, b]
          tellConstraint (Unqualified "leq") [b, c]
          tellConstraint (Unqualified "leq") [c, a]
          n <- countAlive leqType
          eqAB <- equal a b
          eqBC <- equal b c
          pure (n, eqAB, eqBC)
        n @?= 0
        assertBool "a and b should be unified" eqAB
        assertBool "b and c should be unified" eqBC
    ]

-- ---------------------------------------------------------------------------
-- Fibonacci surface source
-- ---------------------------------------------------------------------------

fibSource :: Text
fibSource =
  ":- module(fib, [fib/2]).\n\
  \:- chr_constraint fib/2.\n\
  \\n\
  \base0 @ fib(0, R) <=> R = 0.\n\
  \base1 @ fib(1, R) <=> R = 1.\n\
  \rec @ fib(N, R) <=> N1 is host:'-'(N, 1), N2 is host:'-'(N, 2), \
  \fib(N1, R1), fib(N2, R2), Tmp is host:'+'(R1, R2), R = Tmp.\n"

extractIntArgs :: String -> [Value] -> (Integer, Integer)
extractIntArgs _ [VInt a, VInt b] = (a, b)
extractIntArgs context vals =
  error $
    context ++ ": expected 2 Int arguments, got " ++ show (length vals)

fibHostCalls :: HostCallRegistry
fibHostCalls =
  Map.fromList
    [ ( VM.Name "+",
        HostCallFn $ \args ->
          let (a, b) = extractIntArgs "+" args in pure (VInt (a + b))
      ),
      ( VM.Name "-",
        HostCallFn $ \args ->
          let (a, b) = extractIntArgs "-" args in pure (VInt (a - b))
      )
    ]

fibTests :: TestTree
fibTests =
  testGroup
    "Fibonacci (from surface language)"
    [ testCase "fib 10 = 55" $ do
        prog <- compileOrFail [("fib.chr", fibSource)]
        bindings <- runProgramWithGoal prog fibHostCalls "fib:fib(10, R)"
        Map.lookup "R" bindings @?= Just (IntTerm 55)
    ]

-- ---------------------------------------------------------------------------
-- Query visibility
-- ---------------------------------------------------------------------------

hiddenSource :: Text
hiddenSource =
  ":- module(secret, []).\n\
  \:- chr_constraint hidden/1.\n\
  \\n\
  \hidden(X) <=> true.\n"

exportedSource :: Text
exportedSource =
  ":- module(pub, [visible/1]).\n\
  \:- chr_constraint visible/1.\n\
  \:- chr_constraint internal/1.\n\
  \\n\
  \visible(X) <=> true.\n\
  \internal(X) <=> true.\n"

ambiguousSourceA :: Text
ambiguousSourceA =
  ":- module(modA, [foo/1]).\n\
  \:- chr_constraint foo/1.\n\
  \\n\
  \foo(X) <=> true.\n"

ambiguousSourceB :: Text
ambiguousSourceB =
  ":- module(modB, [foo/1]).\n\
  \:- chr_constraint foo/1.\n\
  \\n\
  \foo(X) <=> true.\n"

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

visibilityTests :: TestTree
visibilityTests =
  testGroup
    "Query visibility"
    [ testCase "unqualified resolves to unique exported constraint" $ do
        cp <- compileOrFail [("pub.chr", exportedSource)]
        let q = Constraint (Unqualified "visible") [VarTerm "X"]
        case resolveQueryConstraint cp q of
          Right (QualifiedConstraint (QualifiedName "pub" "visible") _) -> pure ()
          other ->
            assertFailure $
              "Expected Right (Qualified pub visible), got: " ++ show other,
      testCase "unqualified hidden constraint fails" $ do
        cp <- compileOrFail [("secret.chr", hiddenSource)]
        let q = Constraint (Unqualified "hidden") [VarTerm "X"]
        assertBool "Should fail for hidden constraint" (isLeft (resolveQueryConstraint cp q)),
      testCase "qualified exported constraint succeeds" $ do
        cp <- compileOrFail [("pub.chr", exportedSource)]
        let q = Constraint (Qualified "pub" "visible") [VarTerm "X"]
        case resolveQueryConstraint cp q of
          Right _ -> pure ()
          Left err -> assertFailure $ "Should succeed: " ++ show err,
      testCase "qualified hidden constraint fails" $ do
        cp <- compileOrFail [("secret.chr", hiddenSource)]
        let q = Constraint (Qualified "secret" "hidden") [VarTerm "X"]
        assertBool
          "Should fail for hidden qualified constraint"
          ( isLeft
              (resolveQueryConstraint cp q)
          ),
      testCase "qualified non-exported internal constraint fails" $ do
        cp <- compileOrFail [("pub.chr", exportedSource)]
        let q = Constraint (Qualified "pub" "internal") [VarTerm "X"]
        assertBool
          "Should fail for non-exported constraint"
          ( isLeft
              ( resolveQueryConstraint
                  cp
                  q
              )
          ),
      testCase "ambiguous unqualified name fails" $ do
        cp <-
          compileOrFail
            [ ("a.chr", ambiguousSourceA),
              ("b.chr", ambiguousSourceB)
            ]
        let q = Constraint (Unqualified "foo") [VarTerm "X"]
        assertBool
          "Should fail for ambiguous constraint"
          ( isLeft
              ( resolveQueryConstraint
                  cp
                  q
              )
          ),
      testCase "ambiguous name resolved with qualification" $ do
        cp <-
          compileOrFail
            [ ("a.chr", ambiguousSourceA),
              ("b.chr", ambiguousSourceB)
            ]
        let q = Constraint (Qualified "modA" "foo") [VarTerm "X"]
        case resolveQueryConstraint cp q of
          Right _ -> pure ()
          Left err -> assertFailure $ "Should succeed with qualification: " ++ show err
    ]

-- ---------------------------------------------------------------------------
-- Query-time error paths
-- ---------------------------------------------------------------------------
--
-- 'visibilityTests' above already covers the @Left@/@Right@ split for
-- 'resolveQueryConstraint'. The cases below pin the /rejection variant/
-- for each failure mode (since the user-visible rendering is built by
-- the 'Display' instance on @GoalNotAConstraint@), plus one end-to-end
-- check on the displayed message.

leftRejection :: Either GoalRejection b -> IO GoalRejection
leftRejection (Left r) = pure r
leftRejection (Right _) = assertFailure "expected Left, got Right"

queryErrorTests :: TestTree
queryErrorTests =
  testGroup
    "Query errors"
    [ testCase "unknown unqualified constraint → NoSuchConstraint" $ do
        cp <- compileOrFail [("pub.chr", exportedSource)]
        let q = Constraint (Unqualified "nope") [VarTerm "X"]
        r <- leftRejection (resolveQueryConstraint cp q)
        case r of
          NoSuchConstraint -> pure ()
          other -> assertFailure $ "expected NoSuchConstraint, got: " ++ show other,
      testCase "unknown qualified constraint → ConstraintNotExported" $ do
        cp <- compileOrFail [("pub.chr", exportedSource)]
        let q = Constraint (Qualified "pub" "internal") [VarTerm "X"]
        r <- leftRejection (resolveQueryConstraint cp q)
        case r of
          ConstraintNotExported (QualifiedName "pub" "internal") -> pure ()
          other ->
            assertFailure $
              "expected ConstraintNotExported pub:internal, got: " ++ show other,
      testCase "ambiguous unqualified → AmbiguousConstraint lists modules" $ do
        cp <-
          compileOrFail
            [ ("a.chr", ambiguousSourceA),
              ("b.chr", ambiguousSourceB)
            ]
        let q = Constraint (Unqualified "foo") [VarTerm "X"]
        r <- leftRejection (resolveQueryConstraint cp q)
        case r of
          AmbiguousConstraint ms -> do
            assertBool ("expected 'modA' in: " ++ show ms) ("modA" `elem` ms)
            assertBool ("expected 'modB' in: " ++ show ms) ("modB" `elem` ms)
          other -> assertFailure $ "expected AmbiguousConstraint, got: " ++ show other,
      testCase "displayMsg renders YCHR-20013 with REPL hint" $ do
        let q = Constraint (Unqualified "nope") [VarTerm "X"]
            rendered = displayMsg (GoalNotAConstraint q NoSuchConstraint)
        assertBool ("expected 'YCHR-20013' in: " ++ rendered) $
          "YCHR-20013" `isInfixOf` rendered
        assertBool ("expected 'nope/1' in: " ++ rendered) $
          "nope/1" `isInfixOf` rendered
        assertBool ("expected REPL hint in: " ++ rendered) $
          "ychr repl" `isInfixOf` rendered,
      testCase "runProgramWithGoal: malformed goal throws ParseError" $ do
        cp <- compileOrFail [("pub.chr", exportedSource)]
        outcome <-
          try @SomeException
            (runProgramWithGoal cp Map.empty "this is not a valid goal")
        case outcome of
          Left exc -> case fromException exc :: Maybe Error of
            Just (ParseError _ _) -> pure ()
            Just other ->
              assertFailure $
                "expected ParseError, got Error:\n" ++ displayMsg other
            Nothing ->
              assertFailure $
                "expected ParseError, got non-Error exception: " ++ show exc
          Right _ -> assertFailure "expected exception, got success",
      testCase "runProgramWithGoal: undeclared constraint → GoalNotAConstraint" $ do
        cp <- compileOrFail [("pub.chr", exportedSource)]
        outcome <-
          try @SomeException (runProgramWithGoal cp Map.empty "nope(X)")
        case outcome of
          Left exc -> case fromException exc :: Maybe Error of
            Just (GoalNotAConstraint _ NoSuchConstraint) -> pure ()
            Just other ->
              assertFailure $
                "expected GoalNotAConstraint NoSuchConstraint, got Error:\n"
                  ++ displayMsg other
            Nothing ->
              assertFailure $
                "expected Error, got non-Error exception: " ++ show exc
          Right _ ->
            assertFailure "expected an exception for unknown constraint",
      testCase "runProgramWithQuery: parse error in one goal aborts the whole query" $ do
        cp <- compileOrFail [("pub.chr", exportedSource)]
        outcome <-
          try @SomeException
            (runProgramWithQuery cp Map.empty "visible(X), !!bogus!!.")
        case outcome of
          Left exc -> case fromException exc :: Maybe Error of
            Just (ParseError _ _) -> pure ()
            Just other ->
              assertFailure $
                "expected ParseError, got Error:\n" ++ displayMsg other
            Nothing ->
              assertFailure $
                "expected ParseError, got non-Error exception: " ++ show exc
          Right _ -> assertFailure "expected exception, got success"
    ]

-- ---------------------------------------------------------------------------
-- Non-ASCII constraint names
-- ---------------------------------------------------------------------------

unicodeSource :: Text
unicodeSource =
  ":- module(uni, ['\xe9cho'/1]).\n\
  \:- chr_constraint '\xe9cho'/1.\n\
  \\n\
  \'\xe9cho'(X) <=> X = done.\n"

unicodeTests :: TestTree
unicodeTests =
  testGroup
    "Non-ASCII constraint names"
    [ testCase "constraint with non-ASCII name compiles and runs" $ do
        prog <- compileOrFail [("uni.chr", unicodeSource)]
        bindings <- runProgramWithGoal prog Map.empty "uni:'\xe9cho'(R)"
        Map.lookup "R" bindings @?= Just (CompoundTerm (Unqualified "done") [])
    ]

-- ---------------------------------------------------------------------------
-- Arity overloading
-- ---------------------------------------------------------------------------

arityOverloadSource :: Text
arityOverloadSource =
  ":- module(m, [foo/1, foo/2]).\n\
  \:- chr_constraint foo/1, foo/2.\n\
  \\n\
  \foo(X) <=> X = one.\n\
  \foo(X, Y) <=> X = two, Y = args.\n"

arityOverloadTests :: TestTree
arityOverloadTests =
  testGroup
    "Arity overloading"
    [ testCase "foo/1 and foo/2 are distinct constraints" $ do
        prog <- compileOrFail [("m.chr", arityOverloadSource)]
        bindings1 <- runProgramWithGoal prog Map.empty "m:foo(R)"
        Map.lookup "R" bindings1 @?= Just (CompoundTerm (Unqualified "one") []),
      testCase "foo/2 fires its own rule" $ do
        prog <- compileOrFail [("m.chr", arityOverloadSource)]
        bindings2 <- runProgramWithGoal prog Map.empty "m:foo(R1, R2)"
        Map.lookup "R1" bindings2 @?= Just (CompoundTerm (Unqualified "two") [])
        Map.lookup "R2" bindings2 @?= Just (CompoundTerm (Unqualified "args") [])
    ]

-- ---------------------------------------------------------------------------
-- Multi-goal query body forms
-- ---------------------------------------------------------------------------
--
-- Most existing 'RunTest' cases exercise queries shaped like a single
-- @tell@ — they hit 'D.BodyTell' and the simple expression shapes inside
-- it, but leave the other 'executeBodyGoal' arms in 'YCHR.Run' (BodyTrue,
-- BodyUnify standalone, BodyHostStmt, BodyCall, BodyApply) and the
-- 'evalNestedExpr' shapes for ApplyExpr / FunRefExpr untouched. The cases
-- below pin each of those arms through the public 'runProgramWithQuery'
-- entry point, and pin the user-visible error messages for the runtime
-- unification-failure and unknown-host-function paths.
--
-- All cases assert on the final bindings or on the thrown exception —
-- no store/history introspection.

qbodySource :: Text
qbodySource =
  ":- module(qbody, [keep/1, fun triple/1]).\n\
  \:- chr_constraint keep/1.\n\
  \:- function triple/1.\n\
  \triple(X) -> host:'*'(X, 3).\n\
  \keep(_) <=> true.\n"

qbodyHostCalls :: HostCallRegistry
qbodyHostCalls =
  Map.fromList
    [ ( VM.Name "+",
        HostCallFn $ \args ->
          let (a, b) = extractIntArgs "+" args in pure (VInt (a + b))
      ),
      ( VM.Name "*",
        HostCallFn $ \args ->
          let (a, b) = extractIntArgs "*" args in pure (VInt (a * b))
      )
    ]

expectErrorContaining :: String -> IO a -> IO ()
expectErrorContaining needle act = do
  outcome <- try @SomeException act
  case outcome of
    Left exc ->
      assertBool
        ("expected exception message to contain " ++ show needle ++ ", got: " ++ show exc)
        (needle `isInfixOf` show exc)
    Right _ ->
      assertFailure ("expected exception containing " ++ show needle ++ ", got success")

queryBodyTests :: TestTree
queryBodyTests =
  testGroup
    "Query body forms"
    [ testCase "BodyTrue: 'true, R = 1' binds R" $ do
        prog <- compileOrFail [("qbody.chr", qbodySource)]
        bindings <- runProgramWithQuery prog qbodyHostCalls "true, R = 1."
        Map.lookup "R" bindings @?= Just (IntTerm 1),
      testCase "BodyUnify chain: X = 1, Y = X, R = Y" $ do
        prog <- compileOrFail [("qbody.chr", qbodySource)]
        bindings <- runProgramWithQuery prog qbodyHostCalls "X = 1, Y = X, R = Y."
        Map.lookup "R" bindings @?= Just (IntTerm 1),
      testCase "BodyUnify failure: 1 = 2 raises 'unification failure'" $ do
        prog <- compileOrFail [("qbody.chr", qbodySource)]
        expectErrorContaining "unification failure" $
          runProgramWithQuery prog qbodyHostCalls "1 = 2.",
      testCase "BodyIs re-bind with matching value succeeds" $ do
        prog <- compileOrFail [("qbody.chr", qbodySource)]
        bindings <- runProgramWithQuery prog qbodyHostCalls "R is 1, R is 1."
        Map.lookup "R" bindings @?= Just (IntTerm 1),
      testCase "BodyIs re-bind with conflicting value raises 'unification failure'" $ do
        prog <- compileOrFail [("qbody.chr", qbodySource)]
        expectErrorContaining "unification failure" $
          runProgramWithQuery prog qbodyHostCalls "R is 1, R is 2.",
      testCase "BodyHostStmt: host:'+'(1, 2) as statement runs and is discarded" $ do
        prog <- compileOrFail [("qbody.chr", qbodySource)]
        bindings <-
          runProgramWithQuery prog qbodyHostCalls "host:'+'(1, 2), R = ok."
        Map.lookup "R" bindings @?= Just (CompoundTerm (Unqualified "ok") []),
      testCase "BodyCall: triple(5) as statement runs and is discarded" $ do
        prog <- compileOrFail [("qbody.chr", qbodySource)]
        bindings <- runProgramWithQuery prog qbodyHostCalls "triple(5), R = ok."
        Map.lookup "R" bindings @?= Just (CompoundTerm (Unqualified "ok") []),
      testCase "BodyApply: '$call'(F, X) as statement runs and is discarded" $ do
        prog <- compileOrFail [("qbody.chr", qbodySource)]
        bindings <-
          runProgramWithQuery
            prog
            qbodyHostCalls
            "F = fun(X) -> X end, '$call'(F, 1), R = ok."
        Map.lookup "R" bindings @?= Just (CompoundTerm (Unqualified "ok") []),
      testCase "ApplyExpr in is: R is '$call'(fun triple/1, 4)" $ do
        prog <- compileOrFail [("qbody.chr", qbodySource)]
        bindings <-
          runProgramWithQuery
            prog
            qbodyHostCalls
            "R is '$call'(fun triple/1, 4)."
        Map.lookup "R" bindings @?= Just (IntTerm 12),
      testCase "unknown host function raises 'Unknown host function'" $ do
        prog <- compileOrFail [("qbody.chr", qbodySource)]
        expectErrorContaining "Unknown host function" $
          runProgramWithQuery prog qbodyHostCalls "R is host:nope(1).",
      testCase "BodyUnify with FloatExpr RHS binds R to FloatTerm" $ do
        prog <- compileOrFail [("qbody.chr", qbodySource)]
        bindings <- runProgramWithQuery prog qbodyHostCalls "R = 1.5."
        Map.lookup "R" bindings @?= Just (FloatTerm 1.5),
      testCase "BodyUnify with TextExpr RHS binds R to TextTerm" $ do
        prog <- compileOrFail [("qbody.chr", qbodySource)]
        bindings <- runProgramWithQuery prog qbodyHostCalls "R = \"hello\"."
        Map.lookup "R" bindings @?= Just (TextTerm "hello")
    ]
