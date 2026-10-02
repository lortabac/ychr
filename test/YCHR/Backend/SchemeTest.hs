{-# LANGUAGE OverloadedStrings #-}

-- | Scheme-backend control-flow codegen tests.
--
-- The backend compiles a procedure whose @Return@s all leave it from tail
-- position to a plain value-producing expression, and keeps a @call\/cc@
-- escape only when a @Return@ is trapped inside a 'Foreach' or
-- 'DrainReactivationQueue' body (see 'YCHR.Internal.Backend.Scheme'). A
-- non-tail-recursive user function that took the escape path used to
-- capture a continuation on every call, which is where the Scheme
-- backend's recursion cost came from; these tests pin the shape so it
-- cannot come back silently.
module YCHR.Backend.SchemeTest (tests) where

import Data.Text (Text)
import Data.Text qualified as T
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase)
import YCHR.Embedded (stdlib)
import YCHR.Internal.Backend.Scheme (generateScheme)
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..))
import YCHR.Internal.VM.SExpr (VMProgram (..))
import YCHR.Run (compileModules)

tests :: TestTree
tests =
  testGroup
    "YCHR.Internal.Backend.Scheme"
    [ testCase "a tail-return function program emits no call/cc" $ do
        code <- schemeFor sumSource
        assertNotInfix "call/cc" code,
      -- Pin the procedure escape itself, not just any `call/cc`: leq's
      -- output also contains the Continue escape, so a bare `call/cc`
      -- scan would still pass if `needsEscape` stopped keeping the
      -- `%return` binding and the generated code referenced an unbound
      -- name.
      testCase "a loop-trapped Return keeps a %return escape" $ do
        code <- schemeFor leqSource
        assertInfix "(lambda (%return)" code,
      testCase "a loop that names Continue keeps its continue escape" $ do
        code <- schemeFor leqSource
        assertInfix "%continue-" code,
      testCase "a loop that never names Break drops the break escape" $ do
        code <- schemeFor leqSource
        assertNotInfix "%break-" code
    ]

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

compileOrFail :: [(FilePath, Text)] -> IO CompiledProgram
compileOrFail inputs = case compileModules stdlib False inputs of
  Left err -> assertFailure $ show err
  Right (cp, _) -> pure cp

-- | Compile a source program and render its Scheme library.
schemeFor :: Text -> IO Text
schemeFor src = do
  cp <- compileOrFail [("prog.chr", src)]
  pure $
    generateScheme
      ["ychr", "generated", "test"]
      VMProgram
        { program = cp.program,
          exportedSet = cp.exportedSet,
          symbolTable = cp.symbolTable
        }

assertInfix :: Text -> Text -> IO ()
assertInfix needle haystack =
  assertBool
    ("expected " ++ show needle ++ " in generated Scheme")
    (needle `T.isInfixOf` haystack)

assertNotInfix :: Text -> Text -> IO ()
assertNotInfix needle haystack =
  assertBool
    ("did not expect " ++ show needle ++ " in generated Scheme")
    (not (needle `T.isInfixOf` haystack))

-- ---------------------------------------------------------------------------
-- Sources
-- ---------------------------------------------------------------------------

-- | A non-tail-recursive user function plus a constraint that calls it —
-- the shape whose generated code was dominated by one @call\/cc@ per
-- recursion level (and one per prelude arithmetic helper).
sumSource :: Text
sumSource =
  ":- module(sum, [compute/2, fun sum/1]).\n\
  \:- chr_constraint compute(int, int).\n\
  \:- function sum(int) -> int.\n\
  \\n\
  \sum(0) -> 0.\n\
  \sum(N) | N > 0 -> N + sum(N - 1).\n\
  \\n\
  \compute(N, R) <=> R is sum(N).\n"

-- | The standard @leq@ handler. Its multi-headed occurrences carry
-- partner loops whose bodies hold a @Return@ (early drop) and a
-- @Continue@ (backjump), so at least one procedure must keep the escape.
leqSource :: Text
leqSource =
  ":- module(order, [leq/2]).\n\
  \:- chr_constraint leq/2.\n\
  \\n\
  \reflexivity @ leq(X, X) <=> true.\n\
  \antisymmetry @ leq(X, Y), leq(Y, X) <=> X = Y.\n\
  \idempotence @ leq(X, Y) \\ leq(X, Y) <=> true.\n\
  \transitivity @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).\n"
