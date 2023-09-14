{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module YCHR.Compiler.Parse.Tests (tests) where

import Control.Monad (void)
import Data.Text (Text)
import qualified Data.Text as T
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
        testVariants
          parseRule
          simpl1
          [ "foo(1)<=>true.",
            "foo(1) <=>true.",
            "foo(1)<=> true.",
            "foo(1) <=> true.",
            "foo(1) <=> true .",
            "foo(1) <=> true. "
          ],
      testCase "space after constraint name" $
        testFailure parseRule "foo (1) <=> true.",
      testCase "simplification - named, single head" $
        testVariants
          parseRule
          simpl1Named
          [ "name@foo(1)<=>true.",
            "name @foo(1)<=>true.",
            "name@ foo(1)<=>true.",
            "name @ foo(1)<=>true."
          ],
      testCase "simplification - unnamed, multi-head" $
        testVariants
          parseRule
          simpl2
          [ "foo(1),foo(1)<=>true.",
            "foo(1) ,foo(1)<=>true.",
            "foo(1), foo(1)<=>true.",
            "foo(1) , foo(1)<=>true."
          ],
      testCase "simpagation - unnamed, single head" $
        testVariants
          parseRule
          simpag1
          [ "foo(1)\\baz(2)<=>true.",
            "foo(1) \\baz(2) <=>true.",
            "foo(1)\\ baz(2)<=> true.",
            "foo(1) \\ baz(2)<=> true."
          ],
      testCase "propagation - unnamed, single head" $
        testVariants
          parseRule
          prop1
          [ "foo(1)==>true.",
            "foo(1) ==>true.",
            "foo(1)==> true.",
            "foo(1) ==> true.",
            "foo(1) ==> true .",
            "foo(1) ==> true. "
          ]
    ]

simpl1 :: PsRule
simpl1 = Simplification Nothing h g b
  where
    h = Head [ChrConstraint (PsName "foo") [Int 1]]
    g = Guard []
    b = Body [TrueConstr]

simpl1Named :: PsRule
simpl1Named = Simplification (Just "name") h g b
  where
    h = Head [ChrConstraint (PsName "foo") [Int 1]]
    g = Guard []
    b = Body [TrueConstr]

simpl2 :: PsRule
simpl2 = Simplification Nothing h g b
  where
    h = Head [ChrConstraint (PsName "foo") [Int 1], ChrConstraint (PsName "foo") [Int 1]]
    g = Guard []
    b = Body [TrueConstr]

simpag1 :: PsRule
simpag1 = Simpagation Nothing h r g b
  where
    h = Head [ChrConstraint (PsName "foo") [Int 1]]
    r = Remove [ChrConstraint (PsName "baz") [Int 2]]
    g = Guard []
    b = Body [TrueConstr]

prop1 :: PsRule
prop1 = Propagation Nothing h g b
  where
    h = Head [ChrConstraint (PsName "foo") [Int 1]]
    g = Guard []
    b = Body [TrueConstr]

testFailure :: (Eq a, Show a) => Parser a -> Text -> IO ()
testFailure parser txt =
  assertEqual
    ("Parsed text: " <> T.unpack txt)
    Nothing
    (parseMaybe parser txt)

testVariants :: (Eq a, Show a) => Parser a -> a -> [Text] -> IO ()
testVariants parser parsed =
  void
    . traverse
      (\txt -> assertEqual ("Parsed text: " <> T.unpack txt) (Just parsed) (parseMaybe parser txt))
