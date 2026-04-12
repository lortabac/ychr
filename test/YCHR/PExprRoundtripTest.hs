{-# LANGUAGE OverloadedStrings #-}

module YCHR.PExprRoundtripTest (tests) where

import Data.Text (Text)
import Data.Text qualified as Text
import Hedgehog (Gen, Property, annotate, failure, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import YCHR.Loc (Ann (..), noAnn)
import YCHR.PExpr

-- ---------------------------------------------------------------------------
-- Operator table
-- ---------------------------------------------------------------------------

-- | A representative operator table for testing.
testOps :: OpTable
testOps =
  mkOpTable
    [ (200, [(InfixL, "*"), (InfixL, "/")]),
      (300, [(InfixL, "+"), (InfixL, "-")]),
      (500, [(Prefix, "~")]),
      (700, [(InfixN, "is")])
    ]

-- ---------------------------------------------------------------------------
-- Generators
-- ---------------------------------------------------------------------------

-- | Generate a safe unquoted atom: lowercase-starting alphanumeric, not a
-- word operator, and no double underscore.
genSafeAtom :: Gen Text
genSafeAtom = Gen.filter isOk $ do
  c <- Gen.lower
  rest <- Gen.list (Range.linear 0 5) (Gen.choice [Gen.alphaNum, pure '_'])
  pure (Text.pack (c : rest))
  where
    isOk s =
      s `notElem` wordOps
        && not ("__" `Text.isInfixOf` s)
    wordOps = [name | (_, ty, name) <- opTableEntries testOps, not (isSymOp ty name)]
    isSymOp Prefix _ = True
    isSymOp Postfix _ = True
    isSymOp _ name = Text.all (`elem` (":=<>+-*/#@^~!&?" :: [Char])) name

-- | Generate atoms including cases that require quoting.
genAtom :: Gen Text
genAtom =
  Gen.choice
    [ genSafeAtom,
      pure "",
      -- Atom with embedded quote
      do
        s <- genSafeAtom
        pure (s <> "'s"),
      -- Uppercase-starting atom (needs quoting)
      do
        c <- Gen.upper
        rest <- Gen.list (Range.linear 0 4) Gen.alphaNum
        pure (Text.pack (c : rest))
    ]

-- | Generate a variable name.
genVar :: Gen Text
genVar = do
  c <- Gen.upper
  rest <- Gen.list (Range.linear 0 4) (Gen.choice [Gen.alphaNum, pure '_'])
  pure (Text.pack (c : rest))

-- | Generate a string literal body.
genStringContent :: Gen Text
genStringContent =
  Text.pack
    <$> Gen.list
      (Range.linear 0 10)
      ( Gen.choice
          [ Gen.alphaNum,
            Gen.element [' ', '"', '\\', '\n', '\t']
          ]
      )

-- | Generate a non-operator PExpr (no operators in structure).
genPExpr :: Gen PExpr
genPExpr =
  Gen.recursive
    Gen.choice
    -- Base cases
    [ Var <$> genVar,
      Int <$> Gen.int (Range.linear (-1000) 1000),
      Atom <$> genAtom,
      Str <$> genStringContent,
      pure Wildcard,
      pure (Atom "[]")
    ]
    -- Recursive cases
    [ -- Compound with safe atom functor
      Gen.subtermM genPExpr $ \t -> do
        f <- genSafeAtom
        pure (Compound f [noAnn t]),
      Gen.subtermM2 genPExpr genPExpr $ \t1 t2 -> do
        f <- genSafeAtom
        pure (Compound f [noAnn t1, noAnn t2]),
      -- Zero-arg compound
      do
        f <- genSafeAtom
        pure (Compound f []),
      -- List (2-3 elements)
      do
        elems <- Gen.list (Range.linear 1 3) genPExpr
        let nil = Atom "[]"
        pure (foldr (\h t -> Compound "." [noAnn h, noAnn t]) nil elems),
      -- Head|Tail list
      Gen.subtermM2 genPExpr genPExpr $ \h t ->
        pure (Compound "." [noAnn h, noAnn t])
    ]

-- | Generate a PExpr that may contain operator-shaped compounds.
genPExprWithOps :: Gen PExpr
genPExprWithOps =
  Gen.recursive
    Gen.choice
    -- Base cases (same as genPExpr)
    [ Var <$> genVar,
      Int <$> Gen.int (Range.linear (-1000) 1000),
      Atom <$> genAtom,
      Str <$> genStringContent,
      pure Wildcard,
      pure (Atom "[]")
    ]
    -- Recursive cases: base + operator expressions
    [ Gen.subtermM genPExprWithOps $ \t -> do
        f <- genSafeAtom
        pure (Compound f [noAnn t]),
      Gen.subtermM2 genPExprWithOps genPExprWithOps $ \t1 t2 -> do
        f <- genSafeAtom
        pure (Compound f [noAnn t1, noAnn t2]),
      -- Infix operator
      Gen.subtermM2 genPExprWithOps genPExprWithOps $ \l r -> do
        op <- Gen.element ["+", "-", "*", "/", "is"]
        pure (Compound op [noAnn l, noAnn r]),
      -- Prefix operator
      Gen.subtermM genPExprWithOps $ \x ->
        pure (Compound "~" [noAnn x]),
      -- List
      do
        elems <- Gen.list (Range.linear 1 3) genPExprWithOps
        pure (foldr (\h t -> Compound "." [noAnn h, noAnn t]) (Atom "[]") elems)
    ]

-- ---------------------------------------------------------------------------
-- Stripping
-- ---------------------------------------------------------------------------

-- | Strip source locations for structural comparison.
strip :: Ann PExpr -> PExpr
strip (Ann t _) = case t of
  Compound f args -> Compound f (map (noAnn . strip) args)
  other -> other

-- ---------------------------------------------------------------------------
-- Properties
-- ---------------------------------------------------------------------------

prop_roundtrip :: OpTable -> Gen PExpr -> Property
prop_roundtrip ops gen = property $ do
  expr <- forAll gen
  let src = prettyPExpr ops expr
  annotate src
  case parseTerms ops "<roundtrip>" (Text.pack (src ++ ".")) of
    Left err -> annotate (show err) >> failure
    Right [ann] -> strip ann === expr
    Right ts -> annotate ("expected 1 term, got " ++ show (length ts)) >> failure

-- ---------------------------------------------------------------------------
-- Test tree
-- ---------------------------------------------------------------------------

tests :: TestTree
tests =
  testGroup
    "YCHR.PExpr.Roundtrip"
    [ testProperty "roundtrip without operators" (prop_roundtrip emptyOps genPExpr),
      testProperty "roundtrip with operators" (prop_roundtrip testOps genPExprWithOps)
    ]
  where
    emptyOps = mkOpTable []
