{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.TextShimTest
-- Description : Pins "Data.Text.Shim" to the "Data.Text" semantics it stands in for.
--
-- 'Data.Text.Shim' replaces the native @Data.Text@ functions under GHC as
-- well as under MicroHs, so any divergence from @Data.Text@ would be a
-- silent behaviour change in the compiler rather than a build error.
--
-- The comparisons below run over an exhaustive small corpus: every string
-- over a three-character alphabet up to a fixed length. That corpus is
-- what caught a first-cut 'breakOnEnd' which reversed the haystack but not
-- the pattern (it agreed with @Data.Text@ on every single-character
-- pattern and failed on @breakOnEnd "a:b" "a:b:c"@).
--
-- Delete this module together with 'Data.Text.Shim'
-- (dev-docs/MICROHS_GAPS.md, gap 4).
module YCHR.TextShimTest (tests) where

-- 'try' comes from the shim so its type variables keep GHC's order
-- (dev-docs/MICROHS_GAPS.md, gap 7).
import Control.Exception.Shim (SomeException, evaluate, try)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Shim qualified as Shim
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase)

tests :: TestTree
tests =
  testGroup
    "Data.Text.Shim"
    [ testGroup
        "matches Data.Text"
        [ testCase "breakOn" $
            case [ (p, s)
                 | p <- needles,
                   s <- corpus 5,
                   Shim.breakOn p s /= T.breakOn p s
                 ] of
              [] -> pure ()
              ((p, s) : _) ->
                assertFailure $
                  "breakOn "
                    ++ show (p, s)
                    ++ ": shim gave "
                    ++ show (Shim.breakOn p s)
                    ++ ", Data.Text gives "
                    ++ show (T.breakOn p s),
          testCase "breakOnEnd" $
            case [ (p, s)
                 | p <- needles,
                   s <- corpus 5,
                   Shim.breakOnEnd p s /= T.breakOnEnd p s
                 ] of
              [] -> pure ()
              ((p, s) : _) ->
                assertFailure $
                  "breakOnEnd "
                    ++ show (p, s)
                    ++ ": shim gave "
                    ++ show (Shim.breakOnEnd p s)
                    ++ ", Data.Text gives "
                    ++ show (T.breakOnEnd p s),
          testCase "concatMap duplicating every character" $
            case [s | s <- corpus 4, Shim.concatMap expand s /= T.concatMap expand s] of
              [] -> pure ()
              (s : _) ->
                assertFailure $
                  "concatMap "
                    ++ show s
                    ++ ": shim gave "
                    ++ show (Shim.concatMap expand s)
                    ++ ", Data.Text gives "
                    ++ show (T.concatMap expand s),
          testCase "concatMap dropping the separator" $
            case [s | s <- corpus 4, Shim.concatMap dropSep s /= T.concatMap dropSep s] of
              [] -> pure ()
              (s : _) ->
                assertFailure $
                  "concatMap dropSep "
                    ++ show s
                    ++ ": shim gave "
                    ++ show (Shim.concatMap dropSep s)
                    ++ ", Data.Text gives "
                    ++ show (T.concatMap dropSep s),
          testCase "last" $
            case [s | s <- corpus 4, not (T.null s), Shim.last s /= T.last s] of
              [] -> pure ()
              (s : _) -> assertFailure $ "last " ++ show s ++ " differs from Data.Text"
        ],
      testGroup
        "partial functions"
        [ testCase "breakOn rejects an empty pattern, like Data.Text" $ do
            expectThrows (evaluate (Shim.breakOn T.empty "abc"))
            expectThrows (evaluate (T.breakOn T.empty "abc")),
          testCase "breakOnEnd rejects an empty pattern once a component is forced" $ do
            expectThrows (evaluate (T.length (fst (Shim.breakOnEnd T.empty "abc"))))
            expectThrows (evaluate (T.length (fst (T.breakOnEnd T.empty "abc")))),
          testCase "breakOnEnd does not force an empty pattern at the tuple" $ do
            expectNoThrow (evaluate (Shim.breakOnEnd T.empty "abc"))
            expectNoThrow (evaluate (T.breakOnEnd T.empty "abc")),
          testCase "last rejects an empty text, like Data.Text" $ do
            expectThrows (evaluate (Shim.last T.empty))
            expectThrows (evaluate (T.last T.empty))
        ]
    ]
  where
    expand c = T.pack [c, c]
    dropSep c
      | c == ':' = T.empty
      | otherwise = T.singleton c

-- ---------------------------------------------------------------------------
-- Corpus
-- ---------------------------------------------------------------------------

-- | Every string over @a:b@ up to the given length. The alphabet holds
-- the separator and a character that appears on both of its sides, so
-- overlapping pattern occurrences are covered.
corpus :: Int -> [Text]
corpus n = map T.pack (concatMap (`sequences` "a:b") [0 .. n])
  where
    sequences 0 _ = [[]]
    sequences k as = [a : rest | a <- as, rest <- sequences (k - 1) as]

-- | Every non-empty pattern the corpus offers, up to length three.
--
-- Length three is what generates the @breakOnEnd "a:b" "a:b:c"@ witness
-- named in the module Haddock.
needles :: [Text]
needles = filter (not . T.null) (corpus 3)

-- ---------------------------------------------------------------------------
-- Partiality helpers
-- ---------------------------------------------------------------------------

-- | Assert that forcing the action raises an exception.
expectThrows :: IO a -> IO ()
expectThrows act = do
  outcome <- try @SomeException act
  case outcome of
    Left _ -> pure ()
    Right _ -> assertFailure "expected an exception, got a value"

-- | Assert that forcing the action raises no exception.
expectNoThrow :: IO a -> IO ()
expectNoThrow act = do
  outcome <- try @SomeException act
  case outcome of
    Left exc -> assertFailure ("expected no exception, got: " ++ show exc)
    Right _ -> pure ()
