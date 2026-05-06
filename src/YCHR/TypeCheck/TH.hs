{-# LANGUAGE TemplateHaskell #-}

-- | Template Haskell splice for compiling the type-checker CHR program.
--
-- The type-checker is itself a CHR program (@typechecker\/typechecker.chr@).
-- This module compiles it at Haskell compile time so that the type-checker
-- is available as a pre-compiled program at runtime, with no compilation
-- overhead.
--
-- Type checking is not yet wired into the pipeline, so the bootstrap
-- issue (type-checking the type-checker) does not arise. When type
-- checking is enabled in the pipeline, the compilation here must use
-- a flag to disable it.
module YCHR.TypeCheck.TH (compileTypeChecker) where

import Data.Text qualified as T
import Language.Haskell.TH (Code, Q, runIO)
import Language.Haskell.TH.Syntax (Lift (..), addDependentFile, unsafeCodeCoerce)
import YCHR.Compile.Pipeline (compileModules)
import YCHR.Runtime.Session (SessionInput, toSessionInput)

-- | Compile @typechecker\/typechecker.chr@ at Template Haskell time. The
-- resulting 'SessionInput' is what 'YCHR.Runtime.Session.withCHR' needs
-- to start a CHR session running the type-checker.
compileTypeChecker :: Code Q SessionInput
compileTypeChecker = unsafeCodeCoerce $ do
  let path = "typechecker/typechecker.chr"
  addDependentFile path
  contents <- runIO (readFile path)
  case compileModules True [(path, T.pack contents)] of
    Left err -> fail ("Failed to compile type-checker CHR: " ++ show err)
    Right (cp, _warnings) -> lift (toSessionInput cp)
