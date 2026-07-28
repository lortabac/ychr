{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module YCHR.ConvertTest (tests) where

import Data.List (sort)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import GHC.Generics (Generic)
import Hedgehog (Gen, Property, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import Test.Tasty.Hedgehog (testProperty)
import YCHR.Convert
import YCHR.Convert.Generic (genericFromTerm, genericToTerm)
import YCHR.DSL
  ( declaring,
    defining,
    exporting,
    int,
    is,
    module',
    term,
    var,
    (.*),
    (.=.),
    (//),
    (<=>),
  )
import YCHR.Run (compileParsedModules)
import YCHR.Types (Name (..), Term (..))

tests :: TestTree
tests =
  testGroup
    "YCHR.Convert"
    [ roundTripTests,
      encodingTests,
      acceptanceTests,
      errorTests,
      endToEndTests
    ]

-- ---------------------------------------------------------------------------
-- A generic-derived fixture type
-- ---------------------------------------------------------------------------

data Shape = Dot | Circle Int | Rect Int Int
  deriving (Eq, Show, Generic)

instance ToTerm Shape where
  toTerm = genericToTerm

instance FromTerm Shape where
  fromTerm = genericFromTerm

-- | Type-pinned 'fromTerm' at 'Shape', to keep the error-case tests short.
decodeShape :: Term -> Either ConvertError Shape
decodeShape = fromTerm

-- ---------------------------------------------------------------------------
-- Generators
-- ---------------------------------------------------------------------------

genInt :: Gen Int
genInt = Gen.int (Range.linearFrom 0 (-100000) 100000)

genInteger :: Gen Integer
genInteger = Gen.integral (Range.linearFrom 0 (-1000000000) 1000000000)

genDouble :: Gen Double
genDouble = Gen.double (Range.linearFracFrom 0 (-1000000) 1000000)

genText :: Gen Text
genText = Gen.text (Range.linear 0 12) Gen.unicode

genShape :: Gen Shape
genShape =
  Gen.choice
    [ pure Dot,
      Circle <$> genInt,
      Rect <$> genInt <*> genInt
    ]

-- ---------------------------------------------------------------------------
-- Round-trip properties
-- ---------------------------------------------------------------------------

roundTrip :: (ToTerm a, FromTerm a, Eq a, Show a) => Gen a -> Property
roundTrip gen = property $ do
  x <- forAll gen
  fromTerm (toTerm x) === Right x

roundTripTests :: TestTree
roundTripTests =
  testGroup
    "round-trip"
    [ testProperty "Int" (roundTrip genInt),
      testProperty "Integer" (roundTrip genInteger),
      testProperty "Double" (roundTrip genDouble),
      testProperty "Bool" (roundTrip Gen.bool),
      testProperty "Text" (roundTrip genText),
      testProperty "()" (roundTrip (pure ())),
      testProperty "Maybe Int" (roundTrip (Gen.maybe genInt)),
      testProperty
        "Either Int Text"
        (roundTrip (Gen.choice [Left <$> genInt, Right <$> genText]) :: Property),
      testProperty "[Int]" (roundTrip (Gen.list (Range.linear 0 10) genInt)),
      testProperty
        "[[Int]]"
        (roundTrip (Gen.list (Range.linear 0 5) (Gen.list (Range.linear 0 5) genInt))),
      testProperty "(Int, Text)" (roundTrip ((,) <$> genInt <*> genText)),
      testProperty
        "(Int, Text, Bool)"
        (roundTrip ((,,) <$> genInt <*> genText <*> Gen.bool)),
      testProperty "Shape (generic)" (roundTrip genShape)
    ]

-- ---------------------------------------------------------------------------
-- Exact-encoding unit tests
-- ---------------------------------------------------------------------------

encodingTests :: TestTree
encodingTests =
  testGroup
    "encoding"
    [ testCase "True" $
        toTerm True @?= CompoundTerm (Unqualified "true") [],
      testCase "False" $
        toTerm False @?= CompoundTerm (Unqualified "false") [],
      testCase "Nothing" $
        toTerm (Nothing :: Maybe Int) @?= CompoundTerm (Unqualified "nothing") [],
      testCase "Just 1" $
        toTerm (Just (1 :: Int)) @?= CompoundTerm (Unqualified "just") [IntTerm 1],
      testCase "[]" $
        toTerm ([] :: [Int]) @?= CompoundTerm (Unqualified "[]") [],
      testCase "[1]" $
        toTerm [1 :: Int]
          @?= CompoundTerm (Unqualified ".") [IntTerm 1, CompoundTerm (Unqualified "[]") []],
      testCase "(1, \"a\")" $
        toTerm (1 :: Int, "a" :: Text)
          @?= CompoundTerm (Unqualified "tuple") [IntTerm 1, TextTerm "a"],
      testCase "()" $
        toTerm () @?= CompoundTerm (Unqualified "()") [],
      testCase "Dot (generic nullary)" $
        toTerm Dot @?= CompoundTerm (Unqualified "dot") [],
      testCase "Circle 3 (generic product)" $
        toTerm (Circle 3) @?= CompoundTerm (Unqualified "circle") [IntTerm 3]
    ]

-- ---------------------------------------------------------------------------
-- Decode acceptance: result-shaped inputs (prelude-qualified / mangled forms)
-- ---------------------------------------------------------------------------

acceptanceTests :: TestTree
acceptanceTests =
  testGroup
    "decode acceptance"
    [ testCase "prelude:true decodes to True" $
        (fromTerm (CompoundTerm (Qualified "prelude" "true") []) :: Either ConvertError Bool)
          @?= Right True,
      testCase "prelude:[] decodes to []" $
        (fromTerm (CompoundTerm (Qualified "prelude" "[]") []) :: Either ConvertError [Int])
          @?= Right [],
      testCase "unqualified cons list decodes" $
        ( fromTerm
            (CompoundTerm (Unqualified ".") [IntTerm 1, CompoundTerm (Unqualified "[]") []]) ::
            Either ConvertError [Int]
        )
          @?= Right [1]
    ]

-- ---------------------------------------------------------------------------
-- Decode error cases
-- ---------------------------------------------------------------------------

errorTests :: TestTree
errorTests =
  testGroup
    "decode errors"
    [ testCase "unknown functor" $
        case decodeShape (CompoundTerm (Unqualified "square") [IntTerm 1]) of
          Left (UnknownFunctor names found) -> do
            found @?= Unqualified "square"
            sort names @?= ["circle", "dot", "rect"]
          other -> assertFailure ("expected UnknownFunctor, got: " <> show other),
      testCase "arity mismatch" $
        decodeShape (CompoundTerm (Unqualified "circle") [IntTerm 1, IntTerm 2])
          @?= Left (ArityMismatch (Unqualified "circle") 1 2),
      testCase "unbound value" $
        (fromTerm (VarTerm "X") :: Either ConvertError Int)
          @?= Left (UnboundValue (VarTerm "X")),
      testCase "type mismatch" $
        (fromTerm (IntTerm 1) :: Either ConvertError Text)
          @?= Left (TypeMismatch "Text" (IntTerm 1)),
      testCase "missing binding" $
        (decodeVar "missing" Map.empty :: Either ConvertError Int)
          @?= Left (MissingBinding "missing")
    ]

-- ---------------------------------------------------------------------------
-- End-to-end typed queries (compile + run + decode)
-- ---------------------------------------------------------------------------

endToEndTests :: TestTree
endToEndTests =
  testGroup
    "end-to-end"
    [ e2eScalar,
      e2eList,
      e2eRecord,
      e2eMalformedGoal,
      e2eCompiled
    ]

-- | 'runQueryCompiled' compiles a program once and drives several
-- independent queries against it, each decoded with 'FromTerm'.
e2eCompiled :: TestTree
e2eCompiled =
  testCase "runQueryCompiled: compile once, query twice" $ do
    let m =
          module' "conv_double_c"
            `exporting` ["double" // 2]
            `declaring` ["double" // 2]
            `defining` [ [term "double" [var "X", var "R"]]
                           <=> [var "R" `is` (var "X" .* int 2)]
                       ]
    cp <- case compileParsedModules True [m] of
      Left err -> assertFailure ("compile failed: " ++ show err)
      Right (cp, _warnings) -> pure cp
    r1 <- runQueryCompiled cp (term "double" [int 21, var "R"]) "R"
    r1 @?= (Right 42 :: Either ConvertError Int)
    r2 <- runQueryCompiled cp (term "double" [int 50, var "R"]) "R"
    r2 @?= (Right 100 :: Either ConvertError Int)

-- | A non-compound goal is reported as a 'ConvertError', not a crash.
e2eMalformedGoal :: TestTree
e2eMalformedGoal =
  testCase "runQuery: non-compound goal -> Left MalformedGoal" $ do
    let m = module' "conv_noop" `declaring` ["p" // 1]
    r <- runQuery [m] (int 5) "R"
    r @?= (Left (MalformedGoal (IntTerm 5)) :: Either ConvertError Int)

-- | A numeric result decoded as an 'Int'.
e2eScalar :: TestTree
e2eScalar =
  testCase "runQuery: double(21, R) -> R = 42 :: Int" $ do
    let m =
          module' "conv_double"
            `exporting` ["double" // 2]
            `declaring` ["double" // 2]
            `defining` [ [term "double" [var "X", var "R"]]
                           <=> [var "R" `is` (var "X" .* int 2)]
                       ]
    r <- runQuery [m] (term "double" [int 21, var "R"]) "R"
    r @?= (Right 42 :: Either ConvertError Int)

-- | A structural list result decoded as @[Int]@. The list term built by
-- 'toTerm' round-trips through unification and the runtime binding.
e2eList :: TestTree
e2eList =
  testCase "runQuery: pack(R) -> R = [1,2,3] :: [Int]" $ do
    let m =
          module' "conv_pack"
            `exporting` ["pack" // 1]
            `declaring` ["pack" // 1]
            `defining` [ [term "pack" [var "R"]]
                           <=> [var "R" .=. toTerm ([1, 2, 3] :: [Int])]
                       ]
    r <- runQuery [m] (term "pack" [var "R"]) "R"
    r @?= (Right [1, 2, 3] :: Either ConvertError [Int])

-- | 'runQueryWith' decoding several goal variables into a tuple.
e2eRecord :: TestTree
e2eRecord =
  testCase "runQueryWith: pair(X, Y) -> (1, 2)" $ do
    let m =
          module' "conv_pair"
            `exporting` ["pair" // 2]
            `declaring` ["pair" // 2]
            `defining` [ [term "pair" [var "X", var "Y"]]
                           <=> [var "X" .=. int 1, var "Y" .=. int 2]
                       ]
    r <-
      runQueryWith
        [m]
        (term "pair" [var "X", var "Y"])
        (\bs -> (,) <$> decodeVar "X" bs <*> decodeVar "Y" bs)
    r @?= (Right (1, 2) :: Either ConvertError (Int, Int))
