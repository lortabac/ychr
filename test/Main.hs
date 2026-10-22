module Main (main) where

import Test.Tasty (Timeout, defaultMain, localOption, mkTimeout, testGroup)
import YCHR.Backend.SchemeTest qualified
import YCHR.CollectTest qualified
import YCHR.CompileTest qualified
import YCHR.ConvertTest qualified
import YCHR.DSLTest qualified
import YCHR.DeclMacroTest qualified
import YCHR.Desugar.InlineTest qualified
import YCHR.DesugarTest qualified
import YCHR.ErrorCodeTest qualified
import YCHR.ExhaustivenessTest qualified
import YCHR.GenerateTest qualified
import YCHR.GoldenTest qualified
import YCHR.Interpreter.SlotsTest qualified
import YCHR.MetaTest qualified
import YCHR.PExprRoundtripTest qualified
import YCHR.PExprTest qualified
import YCHR.ParserTest qualified
import YCHR.PrettyTest qualified
import YCHR.Rename.MacroTest qualified
import YCHR.RenameTest qualified
import YCHR.ResourcesTest qualified
import YCHR.RoundtripTest qualified
import YCHR.RunTest qualified
import YCHR.Runtime.HistoryTest qualified
import YCHR.Runtime.IndexTest qualified
import YCHR.Runtime.InterpreterTest qualified
import YCHR.Runtime.ReactivationTest qualified
import YCHR.Runtime.StoreTest qualified
import YCHR.Runtime.VarTest qualified
import YCHR.TextShimTest qualified
import YCHR.TypeCheckTest qualified
import YCHR.TypeSoundnessTest qualified
import YCHR.VM.ClosureTest qualified
import YCHR.VM.SExprTest qualified

-- | Per-test wall-clock cap. Most tests run in milliseconds, so this
-- only fires on a real hang, e.g. a type-checker rule that builds a
-- cyclic term whose deref never returns. Without it a hang wedges the
-- runner and the failure names no test.
--
-- The cap is generous on purpose: "YCHR.TypeSoundness" runs two 300-case
-- hedgehog properties at about 85s of CPU each, and `make test` runs the
-- other suites at the same time, so on a few-core machine they can take
-- several times their CPU time. A 60s cap gave false timeouts there.
testTimeout :: Timeout
testTimeout = mkTimeout 600_000_000

-- | Run the whole Haskell test suite.
main :: IO ()
main = do
  golden <- YCHR.GoldenTest.tests
  defaultMain $
    localOption testTimeout $
      testGroup
        "ychr"
        [ golden,
          YCHR.CollectTest.tests,
          YCHR.CompileTest.tests,
          YCHR.Backend.SchemeTest.tests,
          YCHR.PrettyTest.tests,
          YCHR.RunTest.tests,
          YCHR.MetaTest.tests,
          YCHR.DSLTest.tests,
          YCHR.ConvertTest.tests,
          YCHR.DesugarTest.tests,
          YCHR.Desugar.InlineTest.tests,
          YCHR.ErrorCodeTest.tests,
          YCHR.ExhaustivenessTest.tests,
          YCHR.GenerateTest.tests,
          YCHR.ParserTest.tests,
          YCHR.DeclMacroTest.tests,
          YCHR.PExprTest.tests,
          YCHR.PExprRoundtripTest.tests,
          YCHR.RoundtripTest.tests,
          YCHR.RenameTest.tests,
          YCHR.Rename.MacroTest.tests,
          YCHR.ResourcesTest.tests,
          YCHR.TextShimTest.tests,
          YCHR.TypeCheckTest.tests,
          YCHR.TypeSoundnessTest.tests,
          YCHR.Runtime.VarTest.tests,
          YCHR.Runtime.StoreTest.tests,
          YCHR.Runtime.IndexTest.tests,
          YCHR.Runtime.HistoryTest.tests,
          YCHR.Runtime.ReactivationTest.tests,
          YCHR.Runtime.InterpreterTest.tests,
          YCHR.Interpreter.SlotsTest.tests,
          YCHR.VM.SExprTest.tests,
          YCHR.VM.ClosureTest.tests
        ]
