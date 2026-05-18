{-# LANGUAGE TemplateHaskell #-}

-- | Compile-time embedding of the standard library sources.
--
-- The @libraries/*.chr@ files are read by GHC at build time and
-- spliced into 'YCHR.StdLib' as a list of @(path, source)@ pairs.
-- The resulting binary is self-contained: no runtime directory
-- lookup, no @YCHR_LIB_DIR@ env var, no cwd-relative path.
--
-- 'addDependentFile' registers each embedded file with GHC's
-- recompilation tracking. In practice cabal's higher-level cache
-- may not consult those registrations, so editing or adding a
-- @.chr@ in @libraries\/@ does not reliably trigger a rebuild;
-- @cabal clean@ or touching this module's source is the safe
-- recipe during development.
module YCHR.StdLib.TH (embeddedStdLibSources) where

import Data.Text (Text)
import Data.Text.IO qualified as TIO
import Language.Haskell.TH (Exp, Q)
import Language.Haskell.TH.Syntax (addDependentFile, lift, runIO)
import System.Directory (listDirectory)
import System.FilePath (takeExtension, (</>))

-- | Splice yielding @[(FilePath, Text)]@: every @libraries\/*.chr@
-- file paired with its UTF-8 contents.
embeddedStdLibSources :: Q Exp
embeddedStdLibSources = do
  -- Resolved relative to the package root (GHC runs splices with the
  -- cabal package directory as cwd).
  let dir = "libraries"
  files <- runIO (filter ((== ".chr") . takeExtension) <$> listDirectory dir)
  pairs <- mapM (readOne dir) files
  lift (pairs :: [(FilePath, Text)])
  where
    readOne dir f = do
      let path = dir </> f
      addDependentFile path
      contents <- runIO (TIO.readFile path)
      pure (path, contents)
