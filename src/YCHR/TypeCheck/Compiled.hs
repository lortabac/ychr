{-# LANGUAGE OverloadedStrings #-}

-- | The pre-compiled YCHR type-checker as a runtime-loaded
-- 'SessionInput'.
--
-- The type-checker is itself a CHR program. Compiling it on every
-- @ychr check@ invocation would mean re-parsing and re-compiling the
-- same file each time, so we cache the compiled result behind a CAF:
-- the first reader of 'typeCheckerProgram' pays the compile cost,
-- everyone after gets the memoized 'SessionInput'.
--
-- 'compileTypeChecker' is the underlying pure function; embedders
-- that want explicit control over when (or whether) the type-checker
-- is compiled can call it directly with their own source.
module YCHR.TypeCheck.Compiled
  ( -- * Pure API
    compileTypeChecker,

    -- * IO API
    loadTypeCheckerFromFile,
    defaultTypeCheckerPath,
    defaultTypeChecker,

    -- * Default value (loaded lazily on first demand)
    typeCheckerProgram,
  )
where

import Data.Text (Text)
import Data.Text.IO qualified as TIO
import System.Environment (lookupEnv)
import System.IO.Unsafe (unsafePerformIO)
import YCHR.Compile.Pipeline (Error, compileModules)
import YCHR.Runtime.Session (SessionInput, toSessionInput)

-- | Compile the YCHR type-checker from its CHR source. Pure; the
-- @True@ flag passed to 'compileModules' disables type-checking the
-- type-checker itself (the bootstrap issue).
compileTypeChecker :: FilePath -> Text -> Either Error SessionInput
compileTypeChecker path src =
  case compileModules True [(path, src)] of
    Left err -> Left err
    Right (cp, _warnings) -> Right (toSessionInput cp)

-- | Read and compile the type-checker from a @.chr@ file on disk.
loadTypeCheckerFromFile :: FilePath -> IO (Either Error SessionInput)
loadTypeCheckerFromFile path = do
  src <- TIO.readFile path
  pure (compileTypeChecker path src)

-- | The default path to the type-checker source: the
-- @YCHR_TC_PATH@ environment variable, or
-- @typechecker\/typechecker.chr@ relative to the current working
-- directory if unset.
defaultTypeCheckerPath :: IO FilePath
defaultTypeCheckerPath = do
  mv <- lookupEnv "YCHR_TC_PATH"
  pure (maybe "typechecker/typechecker.chr" id mv)

-- | Load and compile the type-checker from 'defaultTypeCheckerPath'.
-- Calls 'error' on failure: a missing or malformed type-checker
-- indicates a broken installation, not a user-facing condition.
defaultTypeChecker :: IO SessionInput
defaultTypeChecker = do
  path <- defaultTypeCheckerPath
  result <- loadTypeCheckerFromFile path
  case result of
    Left err ->
      error ("Failed to load type checker from " ++ path ++ ": " ++ show err)
    Right si -> pure si

-- | The default compiled type-checker, evaluated once on first
-- demand. See "YCHR.StdLib" for the analogous arrangement for the
-- standard library.
{-# NOINLINE typeCheckerProgram #-}
typeCheckerProgram :: SessionInput
typeCheckerProgram = unsafePerformIO defaultTypeChecker
