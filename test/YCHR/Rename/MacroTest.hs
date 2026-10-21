{-# LANGUAGE OverloadedStrings #-}

-- | Unit tests for the pure macro mechanics: clause matching, the
-- variant test behind the repeat check, and clause instantiation with
-- the construction primitives.
module YCHR.Rename.MacroTest (tests) where

import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import YCHR.Internal.Parsed (ExpansionStep (..), MacroClause (..), SourceLoc (..))
import YCHR.Internal.Rename.Macro
  ( PrimitiveError (..),
    PrimitiveOperand (..),
    instantiateBody,
    instantiateClause,
    isVariant,
    matchClause,
    renderExpansionChain,
  )
import YCHR.Internal.Types (Name (..), Term (..))

-- | Macro mechanics tests.
tests :: TestTree
tests =
  testGroup
    "Rename.Macro"
    [matchTests, variantTests, instantiateTests, chainTests]

-- | An unqualified atom.
atom :: Text -> Term
atom n = CompoundTerm (Unqualified n) []

-- | A variable.
var :: Text -> Term
var = VarTerm

-- | An unqualified compound.
app :: Text -> [Term] -> Term
app n = CompoundTerm (Unqualified n)

-- | A proper list, built from @.@ cells.
list :: [Term] -> Term
list = foldr (\h t -> app "." [h, t]) (atom "[]")

matchTests :: TestTree
matchTests =
  testGroup
    "matchClause"
    [ testCase "a variable binds any argument" $
        matchClause [var "X"] [app "f" [var "Y"]]
          @?= Just (Map.fromList [("X", app "f" [var "Y"])]),
      testCase "'_' matches and binds nothing" $
        matchClause [Wildcard] [atom "a"] @?= Just Map.empty,
      testCase "a repeated variable needs identical arguments" $ do
        matchClause [var "X", var "X"] [var "A", var "A"]
          @?= Just (Map.fromList [("X", var "A")])
        matchClause [var "X", var "X"] [var "A", var "B"] @?= Nothing,
      testCase "an argument containing '_' is never identical" $
        matchClause [var "X", var "X"] [Wildcard, Wildcard] @?= Nothing,
      testCase "a use-site variable matches only a variable pattern" $
        matchClause [atom "a"] [var "A"] @?= Nothing,
      testCase "constants match only equal constants" $ do
        matchClause [IntTerm 1] [IntTerm 1] @?= Just Map.empty
        matchClause [IntTerm 2] [app "+" [IntTerm 1, IntTerm 1]] @?= Nothing,
      testCase "lists match structurally" $
        matchClause [list [var "A", var "B"]] [app "." [atom "a", list [atom "b"]]]
          @?= Just (Map.fromList [("A", atom "a"), ("B", atom "b")]),
      testCase "names are compared as written" $
        matchClause [CompoundTerm (Qualified "graph" "edge") []] [atom "edge"]
          @?= Nothing,
      testCase "a qualified pattern with variables matches a qualified name" $
        matchClause
          [app ":" [atom "lib", var "F"]]
          [CompoundTerm (Qualified "lib" "x") [IntTerm 1]]
          @?= Just (Map.fromList [("F", app "x" [IntTerm 1])])
    ]

variantTests :: TestTree
variantTests =
  testGroup
    "isVariant"
    [ testCase "identical up to renaming" $
        isVariant [app "f" [var "X", var "Y"]] [app "f" [var "A", var "B"]] @?= True,
      testCase "the renaming must be a bijection" $ do
        isVariant [app "f" [var "X", var "X"]] [app "f" [var "A", var "B"]] @?= False
        isVariant [app "f" [var "X", var "Y"]] [app "f" [var "A", var "A"]] @?= False,
      testCase "each '_' is a distinct variable" $ do
        isVariant [Wildcard, Wildcard] [var "A", var "B"] @?= True
        isVariant [Wildcard, Wildcard] [var "A", var "A"] @?= False,
      testCase "different structure is not a variant" $
        isVariant [app "s" [var "X"]] [var "X"] @?= False
    ]

-- | Instantiate a clause with no head variables.
instantiate :: [Term] -> Either PrimitiveError [Term]
instantiate body = instantiateClause 0 Map.empty (MacroClause [] body)

-- | The integer 1.
one :: Term
one = IntTerm 1

instantiateTests :: TestTree
instantiateTests =
  testGroup
    "instantiateClause"
    [ testCase "head variables are substituted, others freshened" $
        instantiateClause
          7
          (Map.fromList [("X", atom "a")])
          (MacroClause [var "X"] [app "p" [var "X", var "T"]])
          @?= Right [app "p" [atom "a", var "_macro_7_T"]],
      testCase "a conjunction element is flattened" $
        instantiateClause 0 Map.empty (MacroClause [] [app "," [atom "a", atom "b"]])
          @?= Right [atom "a", atom "b"],
      testCase "primitives are evaluated innermost first" $
        instantiateClause
          0
          (Map.fromList [("F", atom "x"), ("X", IntTerm 1)])
          ( MacroClause
              [var "F", var "X"]
              [ app
                  "$compound"
                  [app "$atom" [list [atom "get_", var "F"]], list [var "X"]]
              ]
          )
          @?= Right [app "get_x" [IntTerm 1]],
      testCase "an integer part contributes its decimal text" $
        instantiate [app "$atom" [list [atom "n", IntTerm (-3)]]]
          @?= Right [atom "n-3"],
      testCase "a primitive arriving through an argument is not evaluated" $
        let prim = app "$atom" [list [atom "a"]]
         in instantiateClause
              0
              (Map.fromList [("G", prim)])
              (MacroClause [var "G"] [var "G"])
              @?= Right [prim],
      testCase "a qualified functor builds a qualified compound" $
        instantiateClause
          0
          Map.empty
          ( MacroClause
              []
              [app "$compound" [CompoundTerm (Qualified "m" "f") [], list [one]]]
          )
          @?= Right [CompoundTerm (Qualified "m" "f") [one]],
      testCase "'$atom' rejects a result containing '__'" $
        instantiate [app "$atom" [list [atom "a_", atom "_b"]]]
          @?= Left (PrimitiveError AtomResult (list [atom "a_", atom "_b"])),
      testCase "'$compound' rejects a non-atom functor" $
        instantiate [app "$compound" [IntTerm 1, list []]]
          @?= Left (PrimitiveError CompoundFunctor (IntTerm 1)),
      testCase "instantiateBody keeps a conjunction element whole" $
        instantiateBody
          "_decl_"
          3
          Map.empty
          (MacroClause [] [app "," [atom "a", var "V"]])
          @?= Right [app "," [atom "a", var "_decl_3_V"]]
    ]

chainTests :: TestTree
chainTests =
  testGroup
    "renderExpansionChain"
    [ testCase "consecutive uses of one macro are collapsed" $
        renderExpansionChain [step "r", step "r", step "r", step "outer"]
          @?= [ "in 3 nested expansions of m:r/1, innermost used at f.chr:2:1",
                "in the expansion of m:outer/1, used at f.chr:2:1"
              ],
      testCase "more than ten groups are summarized" $
        let chain = concat [[step "a", step "b"] | _ <- [1 :: Int .. 6]]
         in drop 10 (renderExpansionChain chain)
              @?= ["... and 2 more enclosing expansions"]
    ]
  where
    step n = ExpansionStep "m" n 1 (SourceLoc "f.chr" 2 1)
