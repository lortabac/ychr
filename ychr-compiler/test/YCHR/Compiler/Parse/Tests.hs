{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module YCHR.Compiler.Parse.Tests (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import Text.Megaparsec (parseMaybe)
import YCHR.Compiler.Parse
import YCHR.Types.Common
import YCHR.Types.Parsed

tests :: TestTree
tests =
  testGroup
    "parser tests"
    [ testCase "simplification - unnamed, single head" $
        parseMaybe parseRule "foo(1) <=> true." @?= Just simpl1
    ]

simpl1 :: PsRule
simpl1 = Simplification Nothing h g b
  where
    h = Head [ChrConstraint (PsName "foo") [Int 1]]
    g = Guard []
    b = Body [TrueConstr]
