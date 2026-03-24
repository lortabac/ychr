{-# LANGUAGE OverloadedStrings #-}

module YCHR.PrettyTest (tests) where

import Data.Map.Strict qualified as Map
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import YCHR.Pretty (prettyBindings, prettyTerm)
import YCHR.Types (Name (..), Term (..))

tests :: TestTree
tests =
  testGroup
    "YCHR.Pretty"
    [ testCase "prettyTerm IntTerm" $
        prettyTerm (IntTerm 42) @?= "42",
      testCase "prettyTerm AtomTerm" $
        prettyTerm (AtomTerm "foo") @?= "foo",
      testCase "prettyTerm VarTerm" $
        prettyTerm (VarTerm "X") @?= "_",
      testCase "prettyTerm Wildcard" $
        prettyTerm Wildcard @?= "_",
      testCase "prettyTerm CompoundTerm unqualified" $
        prettyTerm (CompoundTerm (Unqualified "f") [IntTerm 1, AtomTerm "a"])
          @?= "f(1, a)",
      testCase "prettyTerm CompoundTerm qualified" $
        prettyTerm (CompoundTerm (Qualified "m" "f") [IntTerm 1])
          @?= "m:f(1)",
      testCase "prettyTerm nested compound" $
        prettyTerm (CompoundTerm (Unqualified "f") [CompoundTerm (Unqualified "g") [IntTerm 0]])
          @?= "f(g(0))",
      testCase "prettyBindings sorted with trailing newline" $
        prettyBindings (Map.fromList [("R", IntTerm 55), ("X", VarTerm "X")])
          @?= "R = 55\nX = _\n",
      testCase "prettyBindings empty" $
        prettyBindings Map.empty @?= ""
    ]
