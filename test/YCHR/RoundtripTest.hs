{-# LANGUAGE OverloadedStrings #-}

-- | Roundtrip property tests: prettyTermSrc / prettyConstraintSrc are
-- right-inverses of the parser.
module YCHR.RoundtripTest (tests) where

import Data.Text (Text)
import Data.Text qualified as Text
import Hedgehog (Gen, Property, annotate, failure, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import YCHR.Parsed qualified as P
import YCHR.Parser (parseConstraint, parseRule, parseTerm)
import YCHR.Pretty (prettyConstraintSrc, prettyRuleSrc, prettyTermSrc)
import YCHR.Types (Constraint (..), Name (..), Term (..))

-- ---------------------------------------------------------------------------
-- Generators
-- ---------------------------------------------------------------------------

-- | Generate a safe unquoted atom: lowercase-starting alphanumeric,
-- not a reserved word or infix operator name.
genSafeAtom :: Gen Text
genSafeAtom = Gen.filter isOk $ do
  c <- Gen.lower
  rest <- Gen.list (Range.linear 0 5) Gen.alphaNum
  pure (Text.pack (c : rest))
  where
    forbidden = ["is", "true", "false"] :: [Text]
    isOk s = s `notElem` forbidden && not (Text.null s)

-- | Generate atoms for use as 'AtomTerm' values, including cases that
-- require quoting (empty, uppercase-starting, embedded single quote).
genAtom :: Gen Text
genAtom =
  Gen.choice
    [ genSafeAtom,
      pure "",
      do
        s <- genSafeAtom
        pure (s <> "'s"),
      do
        c <- Gen.upper
        rest <- Gen.list (Range.linear 0 4) Gen.alphaNum
        pure (Text.pack (c : rest))
    ]

-- | Generate content for a 'TextTerm' (double-quoted string).
-- Includes plain text, embedded double quotes, backslashes, and escape chars.
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

-- | Generate a valid variable name (uppercase-starting).
genVarName :: Gen Text
genVarName = do
  c <- Gen.upper
  rest <- Gen.list (Range.linear 0 4) (Gen.choice [Gen.alphaNum, pure '_'])
  pure (Text.pack (c : rest))

-- | Generate an arbitrary 'Term'. Compound terms use safe atom functors only
-- (no infix operators, no qualified names) so that 'prettyTermSrc' produces
-- output that parses back through 'termP'.
genTerm :: Gen Term
genTerm =
  Gen.recursive
    Gen.choice
    -- Base cases
    [ VarTerm <$> genVarName,
      IntTerm <$> Gen.int (Range.linear (-1000) 1000),
      AtomTerm <$> genAtom,
      TextTerm <$> genStringContent,
      pure Wildcard
    ]
    -- Recursive cases (arity 1 and 2)
    [ Gen.subtermM genTerm $ \t -> do
        f <- genSafeAtom
        pure (CompoundTerm (Unqualified f) [t]),
      Gen.subtermM2 genTerm genTerm $ \t1 t2 -> do
        f <- genSafeAtom
        pure (CompoundTerm (Unqualified f) [t1, t2])
    ]

-- | Generate a constraint name (unqualified or qualified).
genConstraintName :: Gen Name
genConstraintName =
  Gen.choice
    [ Unqualified <$> genSafeAtom,
      Qualified <$> genSafeAtom <*> genSafeAtom
    ]

-- | Generate an arbitrary 'Constraint'.
genConstraint :: Gen Constraint
genConstraint = do
  name <- genConstraintName
  args <- Gen.list (Range.linear 0 3) genTerm
  pure (Constraint name args)

-- | Generate a parsed 'P.Head'.
genHead :: Gen P.Head
genHead =
  Gen.choice
    [ P.Simplification <$> Gen.list (Range.linear 1 3) genConstraint,
      P.Propagation <$> Gen.list (Range.linear 1 3) genConstraint,
      P.Simpagation
        <$> Gen.list (Range.linear 1 2) genConstraint
        <*> Gen.list (Range.linear 1 2) genConstraint
    ]

-- | Generate a parsed 'P.Rule'.
genRule :: Gen P.Rule
genRule = do
  name <- Gen.maybe (P.noAnn <$> genSafeAtom)
  hd <- genHead
  guard_ <- Gen.list (Range.linear 0 2) genTerm
  body_ <- Gen.list (Range.linear 1 3) genTerm
  pure
    P.Rule
      { name = name,
        head = P.noAnn hd,
        guard = P.noAnn guard_,
        body = P.noAnn body_
      }

-- | Strip source locations from a parsed 'P.Rule' so we can compare
-- structurally (the parser produces real locations, generators use 'noAnn').
stripRuleAnn :: P.Rule -> P.Rule
stripRuleAnn r =
  P.Rule
    { name = P.noAnn . (.node) <$> r.name,
      head = P.noAnn r.head.node,
      guard = P.noAnn r.guard.node,
      body = P.noAnn r.body.node
    }

-- ---------------------------------------------------------------------------
-- Properties
-- ---------------------------------------------------------------------------

prop_termRoundtrip :: Property
prop_termRoundtrip = property $ do
  t <- forAll genTerm
  let src = prettyTermSrc t
  case parseTerm "<roundtrip>" (Text.pack src) of
    Left err -> annotate (show err) >> failure
    Right t' -> t' === t

prop_constraintRoundtrip :: Property
prop_constraintRoundtrip = property $ do
  c <- forAll genConstraint
  let src = prettyConstraintSrc c
  case parseConstraint "<roundtrip>" (Text.pack src) of
    Left err -> annotate (show err) >> failure
    Right c' -> c' === c

prop_ruleRoundtrip :: Property
prop_ruleRoundtrip = property $ do
  r <- forAll genRule
  let src = prettyRuleSrc r
  annotate src
  case parseRule "<roundtrip>" (Text.pack src) of
    Left err -> annotate (show err) >> failure
    Right r' -> stripRuleAnn r' === r

-- ---------------------------------------------------------------------------
-- Test tree
-- ---------------------------------------------------------------------------

tests :: TestTree
tests =
  testGroup
    "YCHR.Roundtrip"
    [ testProperty "term roundtrip (parse . prettyTermSrc = id)" prop_termRoundtrip,
      testProperty "constraint roundtrip (parse . prettyConstraintSrc = id)" prop_constraintRoundtrip,
      testProperty "rule roundtrip (parse . prettyRuleSrc = id)" prop_ruleRoundtrip
    ]
