module Main (main) where

import Test.Tasty (defaultMain, testGroup)
import YCHR.CollectTest qualified
import YCHR.CompileTest qualified
import YCHR.DSLTest qualified
import YCHR.DesugarTest qualified
import YCHR.EndToEndTest qualified
import YCHR.GoldenTest qualified
import YCHR.MetaTest qualified
import YCHR.PExprRoundtripTest qualified
import YCHR.PExprTest qualified
import YCHR.ParserTest qualified
import YCHR.PrettyTest qualified
import YCHR.RenameTest qualified
import YCHR.RoundtripTest qualified
import YCHR.Runtime.HistoryTest qualified
import YCHR.Runtime.InterpreterTest qualified
import YCHR.Runtime.ReactivationTest qualified
import YCHR.Runtime.StoreTest qualified
import YCHR.Runtime.VarTest qualified
import YCHR.VM.SExprTest qualified

main :: IO ()
main = do
  golden <- YCHR.GoldenTest.tests
  defaultMain $
    testGroup
      "ychr"
      [ golden,
        YCHR.CollectTest.tests,
        YCHR.CompileTest.tests,
        YCHR.PrettyTest.tests,
        YCHR.EndToEndTest.tests,
        YCHR.MetaTest.tests,
        YCHR.DSLTest.tests,
        YCHR.DesugarTest.tests,
        YCHR.ParserTest.tests,
        YCHR.PExprTest.tests,
        YCHR.PExprRoundtripTest.tests,
        YCHR.RoundtripTest.tests,
        YCHR.RenameTest.tests,
        YCHR.Runtime.VarTest.tests,
        YCHR.Runtime.StoreTest.tests,
        YCHR.Runtime.HistoryTest.tests,
        YCHR.Runtime.ReactivationTest.tests,
        YCHR.Runtime.InterpreterTest.tests,
        YCHR.VM.SExprTest.tests
      ]
