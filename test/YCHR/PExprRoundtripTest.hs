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
    [ (200, [(Yfx, "*"), (Yfx, "/")]),
      (300, [(Yfx, "+"), (Yfx, "-")]),
      (500, [(Fx, "~")]),
      (700, [(Xfx, "is")])
    ]

-- | Operator table covering every fixity kind, including postfix.
--
-- '**' (Yf) is chosen as a symbol token disjoint from '*' under
-- the parser's greedy longest-match rule, so 'X * Y' and 'X **'
-- remain unambiguous.
fullOps :: OpTable
fullOps =
  mkOpTable
    [ (200, [(Yfx, "*"), (Yfx, "/")]),
      (300, [(Yfx, "+"), (Yfx, "-")]),
      (500, [(Fx, "~")]),
      (700, [(Xfx, "is")]),
      (250, [(Xf, "!"), (Yf, "**")])
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
    isSymOp ty name
      | isPrefix ty || isPostfix ty = True
      | otherwise = Text.all (`elem` (":=<>+-*/#@^~!&?" :: [Char])) name

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

-- | Generate a Double whose Haskell 'show' does not use scientific
-- notation (so the parser, which only accepts @digit+ '.' digit+@,
-- can roundtrip it).  Discards values whose show contains an 'e'/'E';
-- with magnitudes mostly in [1, 1000] the rejection rate is negligible.
genFloat :: Gen Double
genFloat = Gen.filter showsDecimal $ do
  whole <- Gen.int (Range.linearFrom 0 (-1000) 1000)
  fracLen <- Gen.int (Range.linear 1 6)
  fracDigits <- Gen.list (Range.singleton fracLen) (Gen.element ['0' .. '9'])
  pure (read (show whole ++ "." ++ fracDigits) :: Double)
  where
    showsDecimal d =
      let s = show d
       in 'e' `notElem` s && 'E' `notElem` s

-- | Build a lambda PExpr from a sub-generator: up to three params and a
-- body, both drawn from @sub@.  The resulting shape is what the
-- pretty-printer emits as @fun(...) -> ... end@ and what 'lambdaP'
-- recognises on parse.
genLambda :: Gen PExpr -> Gen PExpr
genLambda sub = do
  paramCount <- Gen.int (Range.linear 0 3)
  params <- Gen.list (Range.singleton paramCount) sub
  body <- sub
  pure
    ( Compound
        "->"
        [ noAnn (Compound "fun" (map noAnn params)),
          noAnn body
        ]
    )

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
      Int <$> Gen.integral (Range.linear (-1000) 1000),
      Float <$> genFloat,
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
        pure (Compound "." [noAnn h, noAnn t]),
      -- Lambda
      genLambda genPExpr
    ]

-- | Generate a PExpr that may contain operator-shaped compounds.
genPExprWithOps :: Gen PExpr
genPExprWithOps =
  Gen.recursive
    Gen.choice
    -- Base cases (same as genPExpr)
    [ Var <$> genVar,
      Int <$> Gen.integral (Range.linear (-1000) 1000),
      Float <$> genFloat,
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
        pure (foldr (\h t -> Compound "." [noAnn h, noAnn t]) (Atom "[]") elems),
      -- Lambda
      genLambda genPExprWithOps
    ]

-- | Generate a PExpr covering the full grammar: operator expressions,
-- postfix ops, lambdas, lists, floats, and the base atoms/vars/strings.
genPExprFull :: Gen PExpr
genPExprFull =
  Gen.recursive
    Gen.choice
    [ Var <$> genVar,
      Int <$> Gen.integral (Range.linear (-1000) 1000),
      Float <$> genFloat,
      Atom <$> genAtom,
      Str <$> genStringContent,
      pure Wildcard,
      pure (Atom "[]")
    ]
    [ Gen.subtermM genPExprFull $ \t -> do
        f <- genSafeAtom
        pure (Compound f [noAnn t]),
      Gen.subtermM2 genPExprFull genPExprFull $ \t1 t2 -> do
        f <- genSafeAtom
        pure (Compound f [noAnn t1, noAnn t2]),
      Gen.subtermM2 genPExprFull genPExprFull $ \l r -> do
        op <- Gen.element ["+", "-", "*", "/", "is"]
        pure (Compound op [noAnn l, noAnn r]),
      Gen.subtermM genPExprFull $ \x ->
        pure (Compound "~" [noAnn x]),
      -- Xf postfix
      Gen.subtermM genPExprFull $ \x ->
        pure (Compound "!" [noAnn x]),
      -- Yf postfix
      Gen.subtermM genPExprFull $ \x ->
        pure (Compound "**" [noAnn x]),
      do
        elems <- Gen.list (Range.linear 1 3) genPExprFull
        pure (foldr (\h t -> Compound "." [noAnn h, noAnn t]) (Atom "[]") elems),
      genLambda genPExprFull
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
      testProperty "roundtrip with operators" (prop_roundtrip testOps genPExprWithOps),
      testProperty "roundtrip with full grammar" (prop_roundtrip fullOps genPExprFull)
    ]
  where
    emptyOps = mkOpTable []
