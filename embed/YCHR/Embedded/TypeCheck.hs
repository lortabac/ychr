{-# LANGUAGE TemplateHaskell #-}

-- | Compile-time embedding of the type-checker sources.
--
-- The @typechecker\/*.chr@ modules are read by GHC at build time and
-- spliced into @YCHR.Embedded@. The resulting binary is self-contained:
-- no @YCHR_TC_PATH@ env var, no cwd-relative path.
--
-- This module lives in the shared @embed\/@ source directory, compiled
-- into the components that want that self-containment — the @ychr@
-- executable, the test suite, the benchmark and the @stlc@ example —
-- rather than into the @ychr@ library, which takes the compiled checker
-- as an explicit @YCHR.Internal.Runtime.Session.SessionInput@ input
-- instead. See @dev-docs\/MICROHS_GAPS.md@, gap 5.
--
-- 'addDependentFile' registers each embedded file with GHC's
-- recompilation tracking. In practice cabal's higher-level cache may
-- not consult those registrations, and it compares file /contents/
-- rather than modification times, so @touch@ing this module does
-- nothing: during development, edit this module (or @YCHR.Embedded@,
-- which holds the splice) for real, or run @cabal clean@. Adding or
-- removing a @typechecker@ module is the same problem one level up —
-- the directory listing itself is not a dependency, so nothing notices
-- a file that did not exist at the last splice.
module YCHR.Embedded.TypeCheck
  ( embeddedTypeCheckerSources,
  )
where

import Data.List (sort)
import Data.Text (Text)
import Data.Text.IO qualified as TIO
import Language.Haskell.TH (Exp, Q)
import Language.Haskell.TH.Syntax (addDependentFile, lift, runIO)
import System.Directory (listDirectory)
import System.FilePath (takeExtension, (</>))

-- | The directory holding the type-checker's modules, relative to the
-- package root (GHC runs splices with the cabal package directory as
-- cwd). A new module needs no registration here: every @.chr@ in the
-- directory is picked up.
typeCheckerDir :: FilePath
typeCheckerDir = "typechecker"

-- | Splice yielding @[(FilePath, Text)]@: every
-- @typechecker\/*.chr@ file paired with its UTF-8 contents, in
-- filename order so the compiled program does not depend on directory
-- listing order.
embeddedTypeCheckerSources :: Q Exp
embeddedTypeCheckerSources = do
  files <-
    runIO
      (sort . filter ((== ".chr") . takeExtension) <$> listDirectory typeCheckerDir)
  pairs <- mapM readOne files
  lift (pairs :: [(FilePath, Text)])
  where
    readOne f = do
      let path = typeCheckerDir </> f
      addDependentFile path
      contents <- runIO (TIO.readFile path)
      pure (path, contents)
