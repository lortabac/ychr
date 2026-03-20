module Main (main) where

import Test.Tasty (defaultMain, testGroup)

import qualified YCHR.Runtime.VarTest
import qualified YCHR.Runtime.StoreTest
import qualified YCHR.Runtime.HistoryTest
import qualified YCHR.Runtime.ReactivationTest
import qualified YCHR.Runtime.InterpreterTest

main :: IO ()
main = defaultMain $ testGroup "ychr"
  [ YCHR.Runtime.VarTest.tests
  , YCHR.Runtime.StoreTest.tests
  , YCHR.Runtime.HistoryTest.tests
  , YCHR.Runtime.ReactivationTest.tests
  , YCHR.Runtime.InterpreterTest.tests
  ]
