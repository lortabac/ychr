{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.ResourcesTest
-- Description : Pins the run-time resources loader to the compile-time embedder.
--
-- Under GHC the bundled resources are baked in by a Template Haskell
-- splice; under MicroHs they are read from disk at run time
-- (@dev-docs\/MICROHS_GAPS.md@, gap 5). "YCHR.Internal.Resources" is the
-- loader both this executable's provider and the MicroHs one share, so
-- these tests run it under GHC — where the embedded values are available
-- to compare against — and pin the directory lookup, the @YCHR_LIB_DIR@
-- policy, the @.chr@ filter and sort, and the error reporting for a
-- missing or empty directory.
--
-- The content comparison is exact, but only where the file paths match:
-- the embedder reads @libraries\/x.chr@, so the test parses what
-- 'readChrDir' returns for that same directory. A load through a
-- different root (the @YCHR_LIB_DIR@ tests) can only be compared by
-- library name, because the parsed module carries the path it came from.
-- A content mismatch can also mean a stale Template Haskell embed rather
-- than a loader bug: cabal does not reliably rebuild the splice when a
-- @libraries\/*.chr@ file changes (see @embed\/YCHR\/Embedded\/StdLib.hs@),
-- so a failure here after editing a library source may need a
-- @cabal clean@.
module YCHR.ResourcesTest (tests) where

-- 'evaluate' forces the lazy type-checker binding; 'try' is not used here.
import Control.Exception (evaluate)
import Data.List (sort)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import System.Directory (getCurrentDirectory)
import System.Environment (lookupEnv, setEnv, unsetEnv)
import System.FilePath (dropExtension, takeExtension, takeFileName)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@?=))
import YCHR.Embedded qualified as Embedded
import YCHR.Internal.Parsed (Module)
import YCHR.Internal.Resources
  ( Resources (..),
    loadResources,
    loadResourcesAt,
    readChrDir,
    resourceRootFrom,
  )
import YCHR.Internal.StdLib (StdLib (..), parseStdLib)

tests :: TestTree
tests =
  testGroup
    "YCHR.Internal.Resources"
    [ testGroup
        "resourceRootFrom"
        [ testCase "defaults to the current directory" $
            resourceRootFrom Nothing @?= ".",
          testCase "treats an empty variable as unset" $
            resourceRootFrom (Just "") @?= ".",
          testCase "uses a configured directory" $
            resourceRootFrom (Just "some/dir") @?= "some/dir"
        ],
      testGroup
        "readChrDir"
        [ testCase "reads every bundled library, sorted" $ do
            result <- readChrDir "libraries"
            pairs <- either (assertFailure . T.unpack) pure result
            assertBool "paths are sorted" (map fst pairs == sort (map fst pairs))
            assertBool
              "only .chr files"
              (all ((== ".chr") . takeExtension . fst) pairs)
            assertBool "sources are non-empty" (all (not . T.null . snd) pairs)
            sort (map (T.pack . dropExtension . takeFileName . fst) pairs)
              @?= Map.keys (stdlibMap Embedded.stdlib),
          testCase "parses exactly what the embedder baked in" $ do
            result <- readChrDir "libraries"
            pairs <- either (assertFailure . T.unpack) pure result
            case parseStdLib pairs of
              Left err -> assertFailure (show err)
              Right lib -> stdlibMap lib @?= stdlibMap Embedded.stdlib,
          testCase "an existing directory without .chr files is empty" $ do
            result <- readChrDir "app"
            case result of
              Left err -> assertFailure (T.unpack err)
              Right pairs -> length pairs @?= 0,
          testCase "a missing directory is an error" $ do
            result <- readChrDir "no-such-resource-dir"
            case result of
              Left err -> assertBool "names the directory" ("not found" `T.isInfixOf` err)
              Right _ -> assertFailure "expected an error for a missing directory"
        ],
      testGroup
        "loadResourcesAt"
        [ testCase "loads the bundled libraries" $ do
            result <- loadResourcesAt "."
            assertLibraryNames result,
          testCase "the type-checker compiles on first demand" $ do
            result <- loadResourcesAt "."
            resources <- either (assertFailure . T.unpack) pure result
            _ <- evaluate resources.typeCheckerProgram
            pure (),
          testCase "a missing root is an error naming the directory" $ do
            result <- loadResourcesAt "no-such-resource-root"
            case result of
              Left err ->
                assertBool
                  "names the missing directory"
                  ("libraries" `T.isInfixOf` err && "YCHR_LIB_DIR" `T.isInfixOf` err)
              Right _ -> assertFailure "expected an error for a missing root"
        ],
      testGroup
        "loadResources"
        [ -- One case rather than three: 'YCHR_LIB_DIR' is process-global.
          testCase "follows YCHR_LIB_DIR, else the current directory" $ do
            root <- getCurrentDirectory
            configured <- withResourceRoot (Just root) loadResources
            assertLibraryNames configured
            fallback <- withResourceRoot Nothing loadResources
            assertLibraryNames fallback
            -- Discriminating: a bogus value must fail, which it cannot do
            -- if 'loadResources' ignored the variable.
            bogus <- withResourceRoot (Just "no-such-lib-dir") loadResources
            case bogus of
              Left err ->
                assertBool
                  "names the configured root"
                  ("no-such-lib-dir" `T.isInfixOf` err)
              Right _ -> assertFailure "expected an error for a bogus YCHR_LIB_DIR"
        ]
    ]

-- | The parsed standard library as its module map, so two loads can be
-- compared for equality (`StdLib` itself has no 'Eq').
stdlibMap :: StdLib -> Map Text Module
stdlibMap (StdLib modules) = modules

-- | A load through an arbitrary root must at least hold the libraries the
-- embedder has. The parsed modules are not compared: their source
-- locations carry the root they were read from.
assertLibraryNames :: Either Text Resources -> Assertion
assertLibraryNames result = case result of
  Left err -> assertFailure (T.unpack err)
  Right resources ->
    Map.keys (stdlibMap resources.stdlib) @?= Map.keys (stdlibMap Embedded.stdlib)

-- | Run @action@ with @YCHR_LIB_DIR@ set to the given value ('Nothing'
-- unsets it), restoring the previous value afterwards.
withResourceRoot :: Maybe String -> IO a -> IO a
withResourceRoot value action = do
  previous <- lookupEnv "YCHR_LIB_DIR"
  setRoot value
  result <- action
  setRoot previous
  pure result
  where
    setRoot = maybe (unsetEnv "YCHR_LIB_DIR") (setEnv "YCHR_LIB_DIR")
