{-# LANGUAGE TemplateHaskell #-}

-- | Compile-time embedding of the type-checker sources.
--
-- @typechecker\/typechecker.chr@ and the @typechecker2\/*.chr@ modules
-- are read by GHC at build time and spliced into
-- 'YCHR.Internal.TypeCheck.Compiled'. The resulting binary is
-- self-contained: no @YCHR_TC_PATH@ env var, no cwd-relative path.
--
-- 'addDependentFile' registers each embedded file with GHC's
-- recompilation tracking. In practice cabal's higher-level cache may
-- not consult those registrations, and it compares file /contents/
-- rather than modification times, so @touch@ing this module does
-- nothing: during development, edit this module (or
-- 'YCHR.Internal.TypeCheck.Compiled', which holds the splices) for
-- real, or run @cabal clean@. Adding a /new/ @typechecker2@ module is
-- the same problem one level up — the directory listing itself is not
-- a dependency, so nothing notices a file that did not exist at the
-- last splice.
module YCHR.Internal.TypeCheck.TH
  ( typeCheckerPath,
    embeddedTypeCheckerSource,
    embeddedTypeChecker2Sources,
  )
where

import Data.List (sort)
import Data.Text (Text)
import Data.Text.IO qualified as TIO
import Language.Haskell.TH (Exp, Q)
import Language.Haskell.TH.Syntax (addDependentFile, lift, runIO)
import System.Directory (listDirectory)
import System.FilePath (takeExtension, (</>))

-- | The path of the type-checker source, relative to the package
-- root. Used both as the read path during the TH splice (GHC runs
-- splices with the cabal package directory as cwd) and as the path
-- string surfaced in error messages.
typeCheckerPath :: FilePath
typeCheckerPath = "typechecker/typechecker.chr"

-- | Splice yielding the type-checker source as 'Text'.
embeddedTypeCheckerSource :: Q Exp
embeddedTypeCheckerSource = do
  addDependentFile typeCheckerPath
  contents <- runIO (TIO.readFile typeCheckerPath)
  lift (contents :: Text)

-- | The directory holding the all-CHR type-checker's modules. Unlike
-- the single-file checker this one is a multi-module program, and a
-- new module needs no registration here: every @.chr@ in the
-- directory is picked up.
typeChecker2Dir :: FilePath
typeChecker2Dir = "typechecker2"

-- | Splice yielding @[(FilePath, Text)]@: every
-- @typechecker2\/*.chr@ file paired with its UTF-8 contents, in
-- filename order so the compiled program does not depend on directory
-- listing order.
embeddedTypeChecker2Sources :: Q Exp
embeddedTypeChecker2Sources = do
  files <-
    runIO
      (sort . filter ((== ".chr") . takeExtension) <$> listDirectory typeChecker2Dir)
  pairs <- mapM readOne files
  lift (pairs :: [(FilePath, Text)])
  where
    readOne f = do
      let path = typeChecker2Dir </> f
      addDependentFile path
      contents <- runIO (TIO.readFile path)
      pure (path, contents)
