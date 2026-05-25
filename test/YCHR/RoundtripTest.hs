{-# LANGUAGE OverloadedStrings #-}

-- | Roundtrip property tests: prettyTermSrc / prettyConstraintSrc are
-- right-inverses of the parser.
module YCHR.RoundtripTest (tests) where

import Data.List (intercalate)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Hedgehog
  ( Gen,
    Property,
    annotate,
    assert,
    evalIO,
    failure,
    forAll,
    forAllWith,
    property,
    (===),
  )
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import Test.Tasty.Hedgehog (testProperty)
import YCHR.Parsed qualified as P
import YCHR.Parser (parseConstraint, parseRule, parseTerm)
import YCHR.Pretty (prettyConstraintSrc, prettyRuleSrc, prettyTermSrc)
import YCHR.Runtime.Monad (Chr, initSessionEnv, runChr)
import YCHR.Runtime.Registry (HostCallFn (..), baseHostCallRegistry, valueList)
import YCHR.Runtime.Types (Value (..))
import YCHR.Types (Constraint (..), Name (..), Term (..))
import YCHR.VM qualified as VM

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
      IntTerm <$> Gen.integral (Range.linear (-1000) 1000),
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
        head = P.noAnnP hd,
        guard = P.noAnnP guard_,
        body = P.noAnnP body_
      }

-- | Strip source locations from a parsed 'P.Rule' so we can compare
-- structurally (the parser produces real locations, generators use 'noAnn').
stripRuleAnn :: P.Rule -> P.Rule
stripRuleAnn r =
  P.Rule
    { name = P.noAnn . (.node) <$> r.name,
      head = P.noAnnP r.head.node,
      guard = P.noAnnP r.guard.node,
      body = P.noAnnP r.body.node
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
    Right (Left validErr) -> annotate (show validErr) >> failure
    Right (Right c') -> c' === c

prop_ruleRoundtrip :: Property
prop_ruleRoundtrip = property $ do
  r <- forAll genRule
  let src = prettyRuleSrc r
  annotate src
  case parseRule "<roundtrip>" (Text.pack src) of
    Left err -> annotate (show err) >> failure
    Right (_, validErrs@(_ : _)) -> annotate (show validErrs) >> failure
    Right (Nothing, _) -> annotate "parser returned no rule" >> failure
    Right (Just r', []) -> stripRuleAnn r' === r

-- ---------------------------------------------------------------------------
-- =.. roundtrip
-- ---------------------------------------------------------------------------

-- | Generate a runtime 'Value' compound term (including arity 0).
genCompoundValue :: Gen Value
genCompoundValue =
  Gen.recursive
    Gen.choice
    -- Base: arity-0 compound terms
    [ do
        f <- genSafeAtom
        pure (VTerm f [])
    ]
    -- Recursive: arity 1–3
    [ Gen.subtermM genLeafOrCompound $ \t -> do
        f <- genSafeAtom
        pure (VTerm f [t]),
      Gen.subtermM2 genLeafOrCompound genLeafOrCompound $ \t1 t2 -> do
        f <- genSafeAtom
        pure (VTerm f [t1, t2]),
      do
        f <- genSafeAtom
        args <- Gen.list (Range.linear 1 3) genLeafOrCompound
        pure (VTerm f args)
    ]
  where
    genLeafOrCompound =
      Gen.recursive
        Gen.choice
        [ VInt <$> Gen.integral (Range.linear (-100) 100),
          VAtom <$> genSafeAtom,
          VBool <$> Gen.bool
        ]
        [ genCompoundValue
        ]

-- | Structural equality for ground 'Value's (no 'VVar').
groundEq :: Value -> Value -> Bool
groundEq (VInt a) (VInt b) = a == b
groundEq (VAtom a) (VAtom b) = a == b
groundEq (VText a) (VText b) = a == b
groundEq (VBool a) (VBool b) = a == b
groundEq VWildcard VWildcard = True
groundEq (VTerm f1 as1) (VTerm f2 as2) =
  f1 == f2 && length as1 == length as2 && and (zipWith groundEq as1 as2)
groundEq _ _ = False

-- | Show a ground 'Value' for test diagnostics.
showGroundValue :: Value -> String
showGroundValue (VInt n) = "VInt " ++ show n
showGroundValue (VFloat n) = "VFloat " ++ show n
showGroundValue (VAtom a) = "VAtom " ++ show a
showGroundValue (VText t) = "VText " ++ show t
showGroundValue (VBool b) = "VBool " ++ show b
showGroundValue VWildcard = "VWildcard"
showGroundValue (VTerm f args) =
  "VTerm " ++ show f ++ " [" ++ intercalate ", " (map showGroundValue args) ++ "]"
showGroundValue (VVar _) = "VVar <opaque>"

-- | Look up a host call by name, failing if not found.
lookupHostCall :: VM.Name -> HostCallFn
lookupHostCall name = case Map.lookup name baseHostCallRegistry of
  Just hc -> hc
  Nothing -> error $ "host call not found: " ++ show name

runChrEmpty :: Chr a -> IO a
runChrEmpty action = do
  env <- initSessionEnv [] Map.empty Map.empty Map.empty Map.empty Set.empty
  runChr action env

prop_compoundToListRoundtrip :: Property
prop_compoundToListRoundtrip = property $ do
  term <- forAllWith showGroundValue genCompoundValue
  let HostCallFn toList = lookupHostCall "compound_to_list"
      HostCallFn fromList = lookupHostCall "list_to_compound"
  list <- evalIO (runChrEmpty (toList [term]))
  term' <- evalIO (runChrEmpty (fromList [list]))
  annotate (showGroundValue term)
  annotate (showGroundValue term')
  assert (groundEq term term')

prop_listToCompoundRoundtrip :: Property
prop_listToCompoundRoundtrip = property $ do
  f <- forAll genSafeAtom
  args <-
    forAllWith (show . map showGroundValue) $
      Gen.list (Range.linear 0 3) $
        Gen.choice [VInt <$> Gen.integral (Range.linear 0 100), VAtom <$> genSafeAtom]
  let list = valueList (VAtom f : args)
  let HostCallFn fromList = lookupHostCall "list_to_compound"
      HostCallFn toList = lookupHostCall "compound_to_list"
  compound <- evalIO (runChrEmpty (fromList [list]))
  list' <- evalIO (runChrEmpty (toList [compound]))
  annotate (showGroundValue list)
  annotate (showGroundValue list')
  assert (groundEq list list')

-- ---------------------------------------------------------------------------
-- Fixed-case roundtrips
-- ---------------------------------------------------------------------------
--
-- The Hedgehog rule generator above avoids infix operators in functors
-- and emits only safe-atom heads (see 'genTerm' / 'genHead'), so it
-- never produces a named simpagation, never threads a guard through a
-- propagation rule, etc. The fixed cases below exercise those
-- structural shapes head-on.
--
-- Arithmetic and comparison operators come from @library(prelude)@,
-- not 'builtinOps', so 'parseRule' can't re-ingest @+@/@<@/@==@ in
-- isolation. Pretty-printing of those is covered indirectly by the
-- ~120 golden tests that print arithmetic and comparison results.
--
-- The check is: parse → pretty → parse, and assert (a) both parses
-- succeed without parse-validation errors and (b) the pretty output
-- is a fixed point (rule1 and rule2 print to the same source). That
-- pins both the pretty-printer being a valid inverse of the parser
-- and the rendering being canonical for these shapes.

assertRuleRoundtrips :: Text -> IO ()
assertRuleRoundtrips src = case parseRule "<roundtrip>" src of
  Left err -> assertFailure ("parse failed on input:\n" ++ Text.unpack src ++ "\n" ++ show err)
  Right (_, validErrs@(_ : _)) ->
    assertFailure ("parse validation errors on input:\n" ++ show validErrs)
  Right (Nothing, _) ->
    assertFailure ("parser returned no rule for input:\n" ++ Text.unpack src)
  Right (Just rule1, []) -> do
    let pretty1 = prettyRuleSrc rule1
    case parseRule "<roundtrip>" (Text.pack pretty1) of
      Left err ->
        assertFailure ("re-parse failed on pretty output:\n" ++ pretty1 ++ "\n" ++ show err)
      Right (_, validErrs@(_ : _)) ->
        assertFailure ("re-parse validation errors on pretty output:\n" ++ show validErrs)
      Right (Nothing, _) ->
        assertFailure ("re-parse produced no rule on pretty output:\n" ++ pretty1)
      Right (Just rule2, []) -> prettyRuleSrc rule2 @?= pretty1

fixedRuleCases :: TestTree
fixedRuleCases =
  testGroup
    "rule fixed cases"
    [ testCase "named simpagation" $
        assertRuleRoundtrips "subsumes @ leq(X, Y) \\ leq(X, Y) <=> true.",
      testCase "named simpagation with guard (unification ask)" $
        assertRuleRoundtrips "subsumes @ leq(X, Y) \\ leq(X, Z) <=> Y = Z | true.",
      testCase "named propagation" $
        assertRuleRoundtrips "trans @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).",
      testCase "named propagation with multi-atom body" $
        assertRuleRoundtrips
          "mul @ pair(X, Y), pair(Y, Z) ==> pair(X, Z), seen(Y).",
      testCase "simplification with multi-atom guard and body" $
        assertRuleRoundtrips
          "merge(X, Y, Z) <=> X = a, Y = b | step(X), step(Y), step(Z).",
      -- Multi-arg constraints with mixed argument kinds are syntactically
      -- distinctive: head separator, comma-arg lists, and the propagation
      -- arrow all interact.
      testCase "propagation with zero-arity head and body atoms" $
        assertRuleRoundtrips "go @ start, go ==> done."
    ]

-- ---------------------------------------------------------------------------
-- Test tree
-- ---------------------------------------------------------------------------

tests :: TestTree
tests =
  testGroup
    "YCHR.Roundtrip"
    [ testProperty "term roundtrip (parse . prettyTermSrc = id)" prop_termRoundtrip,
      testProperty
        "constraint roundtrip (parse . prettyConstraintSrc = id)"
        prop_constraintRoundtrip,
      testProperty "rule roundtrip (parse . prettyRuleSrc = id)" prop_ruleRoundtrip,
      fixedRuleCases,
      testProperty
        "compound_to_list roundtrip (list_to_compound . compound_to_list = id)"
        prop_compoundToListRoundtrip,
      testProperty
        "list_to_compound roundtrip (compound_to_list . list_to_compound = id)"
        prop_listToCompoundRoundtrip
    ]
