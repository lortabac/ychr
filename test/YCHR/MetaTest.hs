{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module YCHR.MetaTest (tests) where

import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Effectful (runEff)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase)
import YCHR.EndToEnd (CompiledProgram (..), compileModules, runProgramWithQuery)
import YCHR.Meta (metaHostCallRegistry)
import YCHR.Runtime.Interpreter (HostCallFn (..), HostCallRegistry, baseHostCallRegistry)
import YCHR.Runtime.Store (runCHRStore)
import YCHR.Runtime.Types (RuntimeVal (..), Value (..))
import YCHR.Runtime.Var (deref, equal, runUnify)
import YCHR.Types (Term (..))
import YCHR.Types qualified as Types
import YCHR.VM (Name (..))

tests :: TestTree
tests =
  testGroup
    "YCHR.Meta"
    [ readTermTests
    ]

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

hostCalls :: HostCallRegistry
hostCalls = baseHostCallRegistry <> metaHostCallRegistry

-- | Invoke the read_term_from_string host call directly and return the Value.
readTerm :: Text -> IO Value
readTerm s = case Map.lookup (Name "read_term_from_string") metaHostCallRegistry of
  Nothing -> assertFailure "read_term_from_string not found in registry"
  Just (HostCallFn f) -> do
    result <- runEff . runUnify . runCHRStore [] $ f [RVal (VText s)]
    case result of
      RVal v -> pure v
      _ -> assertFailure "read_term_from_string returned non-RVal"

compileOrFail :: [(FilePath, Text)] -> IO CompiledProgram
compileOrFail inputs = case compileModules False inputs of
  Left err -> assertFailure $ show err
  Right (cp, _) -> pure cp

-- ---------------------------------------------------------------------------
-- read_term_from_string tests
-- ---------------------------------------------------------------------------

readTermTests :: TestTree
readTermTests =
  testGroup
    "read_term_from_string"
    [ testCase "integer" $ do
        v <- readTerm "42"
        case v of
          VInt 42 -> pure ()
          _ -> assertFailure "expected VInt 42",
      testCase "negative integer" $ do
        v <- readTerm "-7"
        case v of
          VInt (-7) -> pure ()
          _ -> assertFailure "expected VInt (-7)",
      testCase "atom" $ do
        v <- readTerm "hello"
        case v of
          VAtom "hello" -> pure ()
          _ -> assertFailure "expected VAtom hello",
      testCase "quoted atom" $ do
        v <- readTerm "'hello world'"
        case v of
          VAtom "hello world" -> pure ()
          _ -> assertFailure "expected VAtom 'hello world'",
      testCase "string" $ do
        v <- readTerm "\"hello\""
        case v of
          VText "hello" -> pure ()
          _ -> assertFailure "expected VText hello",
      testCase "wildcard" $ do
        v <- readTerm "_"
        case v of
          VWildcard -> pure ()
          _ -> assertFailure "expected VWildcard",
      testCase "compound term" $ do
        v <- readTerm "f(1, hello)"
        case v of
          VTerm "f" [VInt 1, VAtom "hello"] -> pure ()
          _ -> assertFailure "unexpected result for f(1, hello)",
      testCase "nested compound term" $ do
        v <- readTerm "f(g(1), h(2, 3))"
        case v of
          VTerm "f" [VTerm "g" [VInt 1], VTerm "h" [VInt 2, VInt 3]] -> pure ()
          _ -> assertFailure "unexpected result for f(g(1), h(2, 3))",
      testCase "variable produces a fresh unbound var" $ do
        v <- readTerm "X"
        v' <- runEff . runUnify . runCHRStore [] $ deref v
        case v' of
          VVar _ -> pure ()
          _ -> assertFailure "expected unbound variable",
      testCase "same variable name maps to same var" $ do
        v <- readTerm "f(X, X)"
        eq <- runEff . runUnify . runCHRStore [] $ case v of
          VTerm "f" [a, b] -> equal a b
          _ -> pure False
        assertBool "both X args should be the same variable" eq,
      testCase "different variable names map to different vars" $ do
        v <- readTerm "f(X, Y)"
        eq <- runEff . runUnify . runCHRStore [] $ case v of
          VTerm "f" [a, b] -> equal a b
          _ -> pure True
        assertBool "X and Y should be different variables" (not eq),
      testCase "list syntax" $ do
        v <- readTerm "[1, 2, 3]"
        -- [1,2,3] desugars to '.'(1, '.'(2, '.'(3, '[]')))
        case v of
          VTerm "." [VInt 1, VTerm "." [VInt 2, VTerm "." [VInt 3, VAtom "[]"]]] -> pure ()
          _ -> assertFailure "unexpected result for [1, 2, 3]",
      testCase "infix operator <=> parses as compound term" $ do
        v <- readTerm "a <=> b"
        case v of
          VTerm "<=>" [VAtom "a", VAtom "b"] -> pure ()
          _ -> assertFailure "unexpected result for a <=> b",
      testCase "infix operator = parses as compound term" $ do
        v <- readTerm "a = b"
        case v of
          VTerm "=" [VAtom "a", VAtom "b"] -> pure ()
          _ -> assertFailure "unexpected result for a = b",
      endToEndReadTermTest
    ]

endToEndReadTermTest :: TestTree
endToEndReadTermTest =
  testCase "end-to-end: read_term_from_string in CHR query" $ do
    let src =
          ":- module(m, [check/2]).\n\
          \:- chr_constraint check/2.\n\
          \\n\
          \check(X, X) <=> true.\n"
    prog <- compileOrFail [("m.chr", src)]
    bindings <-
      runProgramWithQuery
        prog
        hostCalls
        "T is host:read_term_from_string(\"f(1, hello)\"), check(T, f(1, hello))."
    -- check/2 should fire (both args unify), leaving no bindings
    -- except T bound to f(1, hello)
    case Map.lookup "T" bindings of
      Just (CompoundTerm (Types.Unqualified "f") [IntTerm 1, AtomTerm "hello"]) -> pure ()
      other -> assertFailure $ "Expected T = f(1, hello), got: " ++ show other
