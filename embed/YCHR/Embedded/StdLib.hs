{-# LANGUAGE TemplateHaskell #-}

-- | Compile-time embedding of the standard library sources.
--
-- The @libraries\/*.chr@ files are read by GHC at build time and
-- spliced into @YCHR.Embedded@ as a list of @(path, source)@ pairs. The
-- resulting binary is self-contained: no runtime directory
-- lookup, no @YCHR_LIB_DIR@ env var, no cwd-relative path.
--
-- This module lives in the shared @embed\/@ source directory, compiled
-- into the components that want that self-containment — the @ychr@
-- executable, the test suite, the benchmark and the @stlc@ example —
-- rather than into the @ychr@ library, which takes the parsed library
-- as an explicit @YCHR.Internal.StdLib.StdLib@ input instead. See
-- @dev-docs\/MICROHS_GAPS.md@, gap 5.
--
-- The library set is spelled out in 'librarySources' rather than
-- discovered by listing the directory. Cabal decides whether to recompile
-- a component from the files it tracks, and it gets that set by expanding
-- @extra-source-files: libraries\/*.chr@ in @ychr.cabal@ at configure
-- time. Editing a library the expansion already names makes Cabal invoke
-- GHC, and 'addDependentFile' makes GHC rerun this splice; a library
-- added after the expansion is in neither set, so nothing reruns and the
-- binary keeps serving the old standard library. Naming the files here
-- puts an addition back under Cabal's eye, as an ordinary source change
-- to this module.
--
-- 'checkSourcesMatch' is a secondary check, not the mechanism: it runs
-- only when the splice is recompiled anyway, and then reports any
-- disagreement between the directory and 'librarySources' instead of
-- letting the splice fail on a missing file or silently omit a new one.
-- @test\/YCHR\/ResourcesTest.hs@ is what catches a stale embed at test
-- time.
--
-- 'addDependentFile' registers each listed file with GHC's recompilation
-- tracking. Cabal compares file /contents/, not modification times, so
-- @touch@ing this module does nothing: during development, edit this
-- module (or @YCHR.Embedded@, which holds the splice) for real, or run
-- @cabal clean@.
module YCHR.Embedded.StdLib (embeddedStdLibSources) where

import Data.List (sort, (\\))
import Data.Text (Text)
import Data.Text.IO qualified as TIO
import Language.Haskell.TH (Exp, Q, reportError)
import Language.Haskell.TH.Syntax (addDependentFile, lift, runIO)
import System.Directory (listDirectory)
import System.FilePath (takeExtension, (</>))

-- | Every bundled library, sorted by filename. Adding or removing a
-- @libraries\/*.chr@ file means editing this list: it is what the splice
-- reads, and the edit to this module is what makes Cabal rebuild the
-- components that embed it.
librarySources :: [FilePath]
librarySources =
  [ "chr.chr",
    "lists.chr",
    "maybe.chr",
    "meta.chr",
    "pairs.chr",
    "prelude.chr",
    "search.chr",
    "strings.chr"
  ]

-- | Splice yielding @[(FilePath, Text)]@: every library named by
-- 'librarySources', paired with its UTF-8 contents.
embeddedStdLibSources :: Q Exp
embeddedStdLibSources = do
  -- Resolved relative to the package root (GHC runs splices with the
  -- cabal package directory as cwd).
  let dir = "libraries"
  checkSourcesMatch dir
  pairs <- mapM (readOne dir) librarySources
  lift (pairs :: [(FilePath, Text)])
  where
    readOne dir f = do
      let path = dir </> f
      addDependentFile path
      contents <- runIO (TIO.readFile path)
      pure (path, contents)

-- | Check that the directory and 'librarySources' name the same files.
-- Called before the splice reads anything, so a list that has fallen
-- behind (or outrun) the tree is reported here rather than surfacing as
-- the raw IO error of a missing read.
checkSourcesMatch :: FilePath -> Q ()
checkSourcesMatch dir = do
  entries <-
    runIO (sort . filter ((== ".chr") . takeExtension) <$> listDirectory dir)
  let strays = entries \\ librarySources
      missing = librarySources \\ entries
  if null strays && null missing
    then pure ()
    else
      reportError $
        dir
          ++ " and librarySources disagree:"
          ++ concatMap (line "on disk, not listed") strays
          ++ concatMap (line "listed, not on disk") missing
  where
    line what f = "\n  " ++ what ++ ": " ++ dir </> f
