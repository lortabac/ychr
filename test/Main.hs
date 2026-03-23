module Main (main) where

import Test.Tasty (defaultMain, testGroup)
import YCHR.DSLTest qualified
import YCHR.DesugarTest qualified
import YCHR.EndToEndTest qualified
import YCHR.ParserTest qualified
import YCHR.RenameTest qualified
import YCHR.Runtime.HistoryTest qualified
import YCHR.Runtime.InterpreterTest qualified
import YCHR.Runtime.ReactivationTest qualified
import YCHR.Runtime.StoreTest qualified
import YCHR.Runtime.VarTest qualified

main :: IO ()
main =
  defaultMain $
    testGroup
      "ychr"
      [ YCHR.EndToEndTest.tests,
        YCHR.DSLTest.tests,
        YCHR.DesugarTest.tests,
        YCHR.ParserTest.tests,
        YCHR.RenameTest.tests,
        YCHR.Runtime.VarTest.tests,
        YCHR.Runtime.StoreTest.tests,
        YCHR.Runtime.HistoryTest.tests,
        YCHR.Runtime.ReactivationTest.tests,
        YCHR.Runtime.InterpreterTest.tests
      ]
