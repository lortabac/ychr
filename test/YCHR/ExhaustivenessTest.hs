{-# LANGUAGE OverloadedStrings #-}

-- | Unit tests for the function exhaustiveness checker
-- ('YCHR.Exhaustiveness'). Each test drives the real compilation
-- pipeline on a small program and inspects the exhaustiveness warnings
-- it returns, so the witness and function name are pinned precisely
-- (the golden harness only asserts a warning's presence or absence).
module YCHR.ExhaustivenessTest (tests) where

import Data.Text (Text)
import Data.Text qualified as T
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import YCHR.Compile.Pipeline (Error, Warning (..), compileModules)
import YCHR.Diagnostic (Diagnostic (..))
import YCHR.Exhaustiveness (ExhaustivenessWarning (..))
import YCHR.Parsed (AnnP (..))
import YCHR.Pretty (prettyTermSrc)

-- | Compile a single-module program and return the exhaustiveness
-- warnings (function display name + rendered witness call).
exhWarnings :: Text -> IO [(Text, String)]
exhWarnings src =
  case compileModules False [("test.chr", src)] of
    Left err -> assertFailure ("unexpected compile error: " ++ show (err :: Error))
    Right (_, ws) ->
      pure
        [ (name, prettyTermSrc witness)
        | ExhaustivenessWarnings ds <- ws,
          Diagnostic _ (AnnP (NonExhaustiveMatch name witness) _ _) <- ds
        ]

tests :: TestTree
tests =
  testGroup
    "Exhaustiveness"
    [ testCase "exhaustive algebraic match emits no warning" $ do
        ws <-
          exhWarnings $
            mod_
              [ "rank(red) -> 1.",
                "rank(green) -> 2.",
                "rank(blue) -> 3."
              ]
        ws @?= [],
      testCase "missing constructor warns with that constructor as witness" $ do
        ws <-
          exhWarnings $
            mod_
              [ "rank(red) -> 1.",
                "rank(green) -> 2."
              ]
        ws @?= [("m:rank/1", "m:rank(m:blue)")],
      testCase "wildcard catch-all is exhaustive" $ do
        ws <-
          exhWarnings $
            mod_
              [ "rank(red) -> 1.",
                "rank(_) -> 0."
              ]
        ws @?= [],
      testCase "guarded equation does not count as covering" $ do
        -- Every constructor has a clause, but each clause is guarded, so
        -- none is guaranteed to match: the function is non-exhaustive.
        ws <-
          exhWarnings $
            mod_
              [ "rank(red) | true -> 1.",
                "rank(green) | true -> 2.",
                "rank(blue) | true -> 3."
              ]
        ws @?= [("m:rank/1", "m:rank(m:red)")],
      testCase "non-algebraic (int) argument never warns" $ do
        ws <-
          exhWarnings $
            T.unlines
              [ ":- module(m, [c/1]).",
                ":- chr_constraint c/1.",
                ":- function describe(int) -> int.",
                "describe(0) -> 100.",
                "describe(1) -> 200.",
                "c(R) <=> R is describe(0)."
              ]
        ws @?= [],
      testCase "fully guarded function over a non-algebraic type never warns" $ do
        -- Every equation is guarded (so none counts as covering) and the
        -- argument is int, which is not enumerable: the only witness is an
        -- all-wildcard one, which is not attributable to an algebraic gap.
        ws <-
          exhWarnings $
            T.unlines
              [ ":- module(m, [c/1]).",
                ":- chr_constraint c/1.",
                ":- function myabs(int) -> int.",
                "myabs(X) | X >= 0 -> X.",
                "myabs(X) | X < 0 -> 0 - X.",
                "c(R) <=> R is myabs(5)."
              ]
        ws @?= [],
      testCase "untyped function never warns" $ do
        -- No declared signature => no algebraic column to enumerate.
        ws <-
          exhWarnings $
            T.unlines
              [ ":- module(m, [c/1]).",
                ":- chr_type color ---> red ; green ; blue.",
                ":- chr_constraint c/1.",
                ":- function rank/1.",
                "rank(red) -> 1.",
                "c(R) <=> R is rank(red)."
              ]
        ws @?= [],
      testCase "open function is not checked" $ do
        ws <-
          exhWarnings $
            T.unlines
              [ ":- module(m, [c/1]).",
                ":- chr_type color ---> red ; green ; blue.",
                ":- chr_constraint c/1.",
                ":- open_function rank(color) -> int.",
                "rank(red) -> 1.",
                "rank(green) -> 2.",
                "c(R) <=> R is rank(red)."
              ]
        ws @?= [],
      testCase "nested missing case warns with a nested witness" $ do
        ws <-
          exhWarnings $
            T.unlines
              [ ":- module(m, [c/1]).",
                ":- chr_type color ---> red ; green ; blue.",
                ":- chr_type pair ---> pair(color, color).",
                ":- chr_constraint c/1.",
                ":- function pick(pair) -> int.",
                "pick(pair(red, _)) -> 1.",
                "pick(pair(green, _)) -> 2.",
                "c(R) <=> R is pick(pair(red, blue))."
              ]
        ws @?= [("m:pick/1", "m:pick(m:pair(m:blue, m:red))")],
      testCase "multi-argument gap warns with a wildcard in the covered column" $ do
        ws <-
          exhWarnings $
            T.unlines
              [ ":- module(m, [c/1]).",
                ":- chr_type color ---> red ; green ; blue.",
                ":- chr_constraint c/1.",
                ":- function m2(int, color) -> int.",
                "m2(_, red) -> 1.",
                "m2(_, green) -> 2.",
                "c(R) <=> R is m2(0, red)."
              ]
        ws @?= [("m:m2/2", "m:m2(_, m:blue)")]
    ]

-- | Wrap a list of @rank/1@ equations over the @color@ type in a minimal
-- module, declaring the function with a @color -> int@ signature and a
-- rule that exercises it.
mod_ :: [Text] -> Text
mod_ equations =
  T.unlines $
    [ ":- module(m, [c/1]).",
      ":- chr_type color ---> red ; green ; blue.",
      ":- chr_constraint c/1.",
      ":- function rank(color) -> int."
    ]
      ++ equations
      ++ ["c(R) <=> R is rank(red)."]
