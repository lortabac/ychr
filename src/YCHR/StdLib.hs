{-# LANGUAGE OverloadedStrings #-}

-- | Standard library loading.
--
-- The @libraries\/@ directory ships a small set of @.chr@ files
-- (@prelude@, @lists@, @strings@, @meta@, @test@) that every user
-- program may import via @:- use_module(library(...))@. This module
-- loads them at runtime: the pure 'parseStdLib' parses in-memory
-- sources, and 'loadStdLibFromDir' reads them from disk.
--
-- The 'stdlib' value is a backward-compatibility CAF: callers that
-- need the default stdlib without doing their own IO can use it
-- directly. It is evaluated once, on first demand, by reading the
-- directory named by the @YCHR_LIB_DIR@ environment variable (or
-- @libraries@ relative to the current working directory if unset).
module YCHR.StdLib
  ( -- * Pure API
    StdLibError (..),
    parseStdLib,

    -- * IO API
    loadStdLibFromDir,
    defaultStdLibDir,
    defaultStdLib,

    -- * Default value (loaded lazily on first demand)
    stdlib,
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Directory (listDirectory)
import System.Environment (lookupEnv)
import System.FilePath (dropExtension, takeExtension, takeFileName, (</>))
import System.IO.Unsafe (unsafePerformIO)
import YCHR.Parsed (Module)
import YCHR.Parser
  ( ModuleHeader (..),
    OpTable,
    builtinOps,
    collectModuleHeader,
    mergeOps,
    parseModuleWith,
  )

-- | Errors that can arise while loading the standard library.
data StdLibError
  = -- | A library source failed to parse. Carries the file path and
    -- the rendered parser error.
    StdLibParseError FilePath String
  | -- | A library header could not be collected (first-pass parse).
    StdLibHeaderError FilePath String
  | -- | Two libraries declared conflicting operators.
    StdLibOpConflict Text
  | -- | A library produced post-parse validation errors.
    StdLibValidationError FilePath String
  deriving (Show)

-- | Parse a list of @(path, source)@ pairs as the standard library.
-- Pure: any IO required to get the sources is the caller's problem.
parseStdLib :: [(FilePath, Text)] -> Either StdLibError (Map Text Module)
parseStdLib sources = do
  hdrs <-
    traverse
      ( \(fp, src) -> case collectModuleHeader fp src of
          Left e -> Left (StdLibHeaderError fp (show e))
          Right h -> Right h
      )
      sources
  let allOps = concatMap (.exportOps) hdrs
  table <- case mergeOps builtinOps allOps of
    Left conflict -> Left (StdLibOpConflict conflict)
    Right t -> Right t
  entries <- mapM (parseLib table) sources
  pure (Map.fromList entries)

parseLib :: OpTable -> (FilePath, Text) -> Either StdLibError (Text, Module)
parseLib table (path, src) =
  let name = T.pack (dropExtension (takeFileName path))
   in case parseModuleWith table path src of
        Left e -> Left (StdLibParseError path (show e))
        Right (m, errs)
          | not (null errs) -> Left (StdLibValidationError path (show errs))
          | otherwise -> Right (name, m)

-- | Read all @.chr@ files from @dir@ and parse them as the standard
-- library.
loadStdLibFromDir :: FilePath -> IO (Either StdLibError (Map Text Module))
loadStdLibFromDir dir = do
  files <- filter ((== ".chr") . takeExtension) <$> listDirectory dir
  sources <-
    mapM
      ( \f -> do
          let path = dir </> f
          src <- TIO.readFile path
          pure (path, src)
      )
      files
  pure (parseStdLib sources)

-- | The default stdlib directory. The @YCHR_LIB_DIR@ environment
-- variable wins; if unset, falls back to @libraries@ relative to the
-- current working directory.
defaultStdLibDir :: IO FilePath
defaultStdLibDir = do
  mv <- lookupEnv "YCHR_LIB_DIR"
  pure (maybe "libraries" id mv)

-- | Load the standard library from 'defaultStdLibDir'. Calls 'error'
-- on failure: a missing or malformed stdlib indicates a broken
-- installation, not a user-facing condition the compiler should try
-- to recover from.
defaultStdLib :: IO (Map Text Module)
defaultStdLib = do
  dir <- defaultStdLibDir
  result <- loadStdLibFromDir dir
  case result of
    Left err ->
      error ("Failed to load standard library from " ++ dir ++ ": " ++ show err)
    Right m -> pure m

-- | The default standard library, evaluated once on first demand.
--
-- Implemented as an 'unsafePerformIO' CAF so that callers that used
-- to depend on the (compile-time, TH-spliced) @stdlib@ map continue
-- to work without threading an extra parameter. The IO is a single
-- read of the @libraries@ directory (or @YCHR_LIB_DIR@); subsequent
-- accesses are pure.
{-# NOINLINE stdlib #-}
stdlib :: Map Text Module
stdlib = unsafePerformIO defaultStdLib
