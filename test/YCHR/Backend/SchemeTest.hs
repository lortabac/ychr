{-# LANGUAGE OverloadedStrings #-}

-- | Scheme-backend control-flow codegen tests.
--
-- The backend compiles a procedure whose @Return@s all leave it from tail
-- position to a plain value-producing expression, and keeps a @call\/cc@
-- escape only when a @Return@ is trapped inside a 'Foreach' or
-- 'DrainReactivationQueue' body (see 'YCHR.Internal.Backend.Scheme'). A
-- non-tail-recursive user function routed through the escape path captures
-- a continuation on every call — the backend's main recursion cost; these
-- tests pin the shape so it cannot come back silently.
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

-- | Scheme-backend control-flow codegen: when a 'Return' needs a @call\/cc@ escape.
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
        assertNotInfix "%break-" code,
      -- The program's operator table is not derivable from the VM
      -- program, so the backend emits it as a `make-op-table` literal in
      -- the session thunk. Without it `read_term_from_string` would
      -- parse with the built-in table only and reject the prelude's `+`.
      -- The assertions cover a declared operator, a built-in one, and
      -- the escaping `printSExpr` applies to the backslash entry.
      testCase "the generated library threads the program's operator table" $ do
        code <- schemeFor declaredOpSource
        assertInfix "(make-op-table" code
        assertInfix "(500 yfx \"&&&\")" code
        assertInfix "(700 xfx \"===\")" code
        assertInfix "(1201 fx \"end\")" code
        assertInfix "(1100 xfx \"\\\\\")" code
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
      cp.opTable

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

-- | A program that declares operators of its own. Their entries must
-- reach the emitted table with their fixity and type, or a run-time
-- @read_term_from_string@ could not spell them. @===@ is @xfx@ where
-- @&&&@ is @yfx@, so 'opTypeText' is exercised for more than one type.
declaredOpSource :: Text
declaredOpSource =
  ":- module(opdecl, [go/2, op(500, yfx, '&&&'), op(700, xfx, '===')]).\n\
  \:- chr_constraint go/2.\n\
  \\n\
  \go(X, Y) <=> X = Y.\n"
