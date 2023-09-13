module Main where

import Test.Tasty
import qualified YCHR.Compiler.Normalize.Tests as Normalize
import qualified YCHR.Compiler.Parse.Tests as Parse
import qualified YCHR.Compiler.Rename.Tests as Rename

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "YCHR tests"
    [Parse.tests, Rename.tests, Normalize.tests]
