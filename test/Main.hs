{-# LANGUAGE NumericUnderscores #-}

module Main (main) where

import Test.Tasty (Timeout, defaultMain, localOption, mkTimeout, testGroup)
import YCHR.CollectTest qualified
import YCHR.CompileTest qualified
import YCHR.ConvertTest qualified
import YCHR.DSLTest qualified
import YCHR.DesugarTest qualified
import YCHR.ErrorCodeTest qualified
import YCHR.ExhaustivenessTest qualified
import YCHR.GoldenTest qualified
import YCHR.MetaTest qualified
import YCHR.PExprRoundtripTest qualified
import YCHR.PExprTest qualified
import YCHR.ParserTest qualified
import YCHR.PrettyTest qualified
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
import YCHR.VM.SExprTest qualified

-- | Per-test wall-clock cap. Most of the suite runs in milliseconds, so
-- this only ever fires on a genuine non-termination — a type-checker
-- rule that builds a cyclic term, say, whose deref never returns.
-- Without it such a regression wedges the runner and reports a
-- suite-level failure that names no test.
--
-- The cap is deliberately generous: "YCHR.TypeSoundness" runs two
-- 300-case hedgehog properties that take roughly 85s of CPU each (the
-- pair overlaps to about that wall-clock when the two run in parallel),
-- and when the "Golden" group saturates every CPU they legitimately
-- take over a minute. A 60s cap turned that contention into a false
-- timeout for both properties; 300s leaves ample headroom while still
-- catching a real hang.
testTimeout :: Timeout
testTimeout = mkTimeout 300_000_000

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
          YCHR.PrettyTest.tests,
          YCHR.RunTest.tests,
          YCHR.MetaTest.tests,
          YCHR.DSLTest.tests,
          YCHR.ConvertTest.tests,
          YCHR.DesugarTest.tests,
          YCHR.ErrorCodeTest.tests,
          YCHR.ExhaustivenessTest.tests,
          YCHR.ParserTest.tests,
          YCHR.PExprTest.tests,
          YCHR.PExprRoundtripTest.tests,
          YCHR.RoundtripTest.tests,
          YCHR.RenameTest.tests,
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
          YCHR.VM.SExprTest.tests
        ]
