{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module YCHR.Compiler.Normalize.Tests (tests) where

import Data.Text (Text)
import Test.Tasty
import Test.Tasty.HUnit
import YCHR.Compiler.Normalize
import YCHR.Types.Common
import YCHR.Types.Normalized
import YCHR.Types.Renamed

tests :: TestTree
tests =
  testGroup
    "normalizer tests"
    [ testCase "remove ground terms" $
        normalizeRule simpl1 @?= nmSimpl1,
      testCase "make linear" $
        normalizeRule simpl2 @?= nmSimpl2,
      testCase "make linear - 3 vars" $
        normalizeRule simpl3 @?= nmSimpl3
    ]

simpl1 :: RnRule
simpl1 = Simplification Nothing h g b
  where
    h = Head [ChrConstraint (q "foo") [Int 1]]
    g = Guard []
    b = Body [TrueConstr]

nmSimpl1 :: NormalRule
nmSimpl1 =
  NormalRule
    { head = Head [],
      remove = Remove [ChrConstraint (q "foo") [Var "$0"]],
      guard = Guard [EqConstr (Var "$0") (Int 1)],
      body = Body [TrueConstr]
    }

simpl2 :: RnRule
simpl2 = Simplification Nothing h g b
  where
    h = Head [ChrConstraint (q "foo") [Var "x", Var "x"]]
    g = Guard []
    b = Body [TrueConstr]

nmSimpl2 :: NormalRule
nmSimpl2 =
  NormalRule
    { head = Head [],
      remove = Remove [ChrConstraint (q "foo") [Var "x", Var "x$0"]],
      guard = Guard [EqConstr (Var "x") (Var "x$0")],
      body = Body [TrueConstr]
    }

simpl3 :: RnRule
simpl3 = Simplification Nothing h g b
  where
    h = Head [ChrConstraint (q "foo") [Var "x", Var "x", Var "x"]]
    g = Guard []
    b = Body [TrueConstr]

nmSimpl3 :: NormalRule
nmSimpl3 =
  NormalRule
    { head = Head [],
      remove = Remove [ChrConstraint (q "foo") [Var "x", Var "x$0", Var "x$1"]],
      guard =
        Guard
          [ EqConstr (Var "x") (Var "x$0"),
            EqConstr (Var "x") (Var "x$1")
          ],
      body = Body [TrueConstr]
    }

q :: Text -> QualifiedName
q = QualifiedName "test"
