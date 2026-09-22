{-# LANGUAGE OverloadedStrings #-}

-- | Run-time loading of the bundled resources.
--
-- The @ychr@ library embeds nothing at compile time: the parsed standard
-- library ('StdLib') and the compiled type-checker ('SessionInput') are
-- explicit inputs (see @docs\/how-to\/embed-a-chr-module.md@, §Supplying
-- the resources). This module builds both from the @libraries\/*.chr@ and
-- @typechecker\/*.chr@ sources on disk, which is the path the MicroHs
-- build takes: MicroHs has no Template Haskell
-- (@dev-docs\/MICROHS_GAPS.md@, gap 5), so the @ychr@ executable reads the
-- sources at run time instead of splicing them in.
--
-- The two directories are looked up under the root given by
-- 'resourceRoot' — the @YCHR_LIB_DIR@ environment variable, or the
-- current directory when it is unset or empty. Set it to a YCHR source
-- tree (the directory holding @libraries\/@ and @typechecker\/@).
--
-- 'loadResourcesAt' takes the root as an argument and is what the GHC
-- test suite calls, to compare a run-time load against the values the
-- Template Haskell embedder bakes in. The GHC components themselves do
-- not call it: their binary stays self-contained
-- (@embed\/YCHR\/Embedded.hs@).
module YCHR.Internal.Resources
  ( -- * Types
    Resources (..),

    -- * Locating the sources
    resourceRootFrom,
    resourceRoot,

    -- * Loading
    readChrDir,
    loadResourcesAt,
    loadResources,
  )
where

import Control.Exception.Shim (IOException, try)
import Data.List (sort)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Directory (doesDirectoryExist, listDirectory)
import System.Environment (lookupEnv)
import System.FilePath (takeExtension, (</>))
import YCHR.Internal.Runtime.Session (SessionInput)
import YCHR.Internal.StdLib (StdLib, parseStdLib)
import YCHR.Internal.TypeCheck.Compiled (compileTypeCheckerModules)

-- | The two resources every entry point in this package needs, as one
-- value so a provider can hand them over together.
--
-- 'typeCheckerProgram' is a lazy binding: it is 'error' when the checker
-- fails to compile, exactly like the compile-time embedder's, and an
-- embedder that never type-checks (the @stlc@ example) never forces it.
-- The @ychr@ CLI forces it anyway — every subcommand type-checks the
-- program, and the REPL does so on load (or on the first query in quiet
-- mode) — so the laziness buys the CLI nothing, but it keeps both
-- providers' failure modes identical.
data Resources = Resources
  { -- | The parsed standard library, seeded into every compilation.
    stdlib :: StdLib,
    -- | The compiled type-checker, forced only by the entry points that
    -- type-check a program or a goal.
    typeCheckerProgram :: SessionInput
  }

-- | The directory holding @libraries\/@ and @typechecker\/@. @Nothing@ and
-- the empty string both mean the current directory.
resourceRootFrom :: Maybe String -> FilePath
resourceRootFrom (Just dir) | not (null dir) = dir
resourceRootFrom _ = "."

-- | 'resourceRootFrom' applied to the @YCHR_LIB_DIR@ environment variable.
resourceRoot :: IO FilePath
resourceRoot = resourceRootFrom <$> lookupEnv "YCHR_LIB_DIR"

-- | Every @.chr@ file in @dir@, paired with its path and contents and
-- sorted by path so the result does not depend on directory listing
-- order. @Left@ when @dir@ is not a directory, or when the listing or a
-- source cannot be read; an empty directory is @Right []@, which
-- 'loadResourcesAt' rejects.
readChrDir :: FilePath -> IO (Either Text [(FilePath, Text)])
readChrDir dir = do
  isDir <- doesDirectoryExist dir
  if not isDir
    then pure (Left (notFound dir))
    else do
      names <- try @IOException (listDirectory dir)
      case names of
        Left err -> pure (Left (unlistable dir (T.pack (show err))))
        Right entries ->
          sequence <$> mapM readOne (sort (filter ((== ".chr") . takeExtension) entries))
  where
    readOne f = do
      let path = dir </> f
      contents <- try @IOException (TIO.readFile path)
      pure $ case contents of
        Left err -> Left (unreadable path (T.pack (show err)))
        Right text -> Right (path, text)

-- | Load both resources from a source tree root: @root\/libraries@ and
-- @root\/typechecker@.
--
-- The standard library is parsed here, because every compilation needs
-- it and a bad root should be reported before any work starts. A source
-- tree that parses but whose type-checker does not compile is reported
-- when the checker is first forced, as in the compile-time embedder.
loadResourcesAt :: FilePath -> IO (Either Text Resources)
loadResourcesAt root = do
  libSources <- readChrDir (root </> "libraries")
  checkSources <- readChrDir (root </> "typechecker")
  pure $ do
    libs <- requireSources (root </> "libraries") libSources
    checks <- requireSources (root </> "typechecker") checkSources
    lib <- either (Left . T.pack . show) Right (parseStdLib libs)
    pure
      Resources
        { stdlib = lib,
          typeCheckerProgram = compileChecker lib checks
        }

-- | 'resourceRoot' followed by 'loadResourcesAt'.
loadResources :: IO (Either Text Resources)
loadResources = resourceRoot >>= loadResourcesAt

compileChecker :: StdLib -> [(FilePath, Text)] -> SessionInput
compileChecker lib sources =
  case compileTypeCheckerModules lib sources of
    Right session -> session
    Left err ->
      error
        ( "Failed to compile the bundled type-checker: "
            ++ show err
            ++ " (check that YCHR_LIB_DIR points at a YCHR source tree)"
        )

-- | A missing directory is a configuration error worth naming; an empty
-- one is almost always the same mistake one level down, and an empty
-- standard library would otherwise be accepted silently.
requireSources :: FilePath -> Either Text [(FilePath, Text)] -> Either Text [(FilePath, Text)]
requireSources dir (Right []) = Left (empty dir)
requireSources _ result = result

notFound :: FilePath -> Text
notFound dir =
  "resource directory not found: "
    <> T.pack dir
    <> hint

empty :: FilePath -> Text
empty dir =
  "resource directory has no .chr sources: "
    <> T.pack dir
    <> hint

unreadable :: FilePath -> Text -> Text
unreadable path err = "cannot read resource source: " <> T.pack path <> ": " <> err

unlistable :: FilePath -> Text -> Text
unlistable dir err = "cannot list resource directory: " <> T.pack dir <> ": " <> err

hint :: Text
hint = " (set YCHR_LIB_DIR to the YCHR source tree, or run ychr from it)"
