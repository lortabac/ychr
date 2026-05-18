{-# LANGUAGE TemplateHaskell #-}

-- | Compile-time embedding of the type-checker source.
--
-- @typechecker\/typechecker.chr@ is read by GHC at build time and
-- spliced into 'YCHR.TypeCheck.Compiled'. The resulting binary is
-- self-contained: no @YCHR_TC_PATH@ env var, no cwd-relative path.
--
-- 'addDependentFile' makes GHC recompile when the embedded file
-- changes.
module YCHR.TypeCheck.TH
  ( typeCheckerPath,
    embeddedTypeCheckerSource,
  )
where

import Data.Text (Text)
import Data.Text.IO qualified as TIO
import Language.Haskell.TH (Exp, Q)
import Language.Haskell.TH.Syntax (addDependentFile, lift, runIO)

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
