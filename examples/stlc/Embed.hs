{-# LANGUAGE TemplateHaskell #-}

-- | Compile-time embedding of the inferencer source, so the example
-- binary is self-contained (no cwd-relative @.chr@ path at run time).
-- Mirrors the pattern used by the built-in type checker in
-- "YCHR.TypeCheck.TH".
module Embed
  ( stlcPath,
    stlcSource,
  )
where

import Data.Text (Text)
import Data.Text.IO qualified as TIO
import Language.Haskell.TH (Exp, Q)
import Language.Haskell.TH.Syntax (addDependentFile, lift, runIO)

-- | Path of the inferencer source, relative to the package root (GHC runs
-- splices with the cabal package directory as cwd). Also surfaced in
-- compile diagnostics.
stlcPath :: FilePath
stlcPath = "examples/stlc/stlc.chr"

-- | Splice yielding the inferencer source as 'Text'. 'addDependentFile'
-- makes GHC recompile the example when the @.chr@ changes.
stlcSource :: Q Exp
stlcSource = do
  addDependentFile stlcPath
  contents <- runIO (TIO.readFile stlcPath)
  lift (contents :: Text)
