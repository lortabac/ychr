{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Standard library loading.
--
-- The @libraries\/@ directory ships a small set of @.chr@ files
-- (@prelude@, @lists@, @strings@, @meta@, @test@) that every user
-- program may import via @:- use_module(library(...))@. The sources
-- are embedded into the binary at compile time via
-- 'YCHR.StdLib.TH.embeddedStdLibSources'; 'stdlib' parses them on
-- first demand.
module YCHR.StdLib
  ( -- * Pure API
    StdLibError (..),
    parseStdLib,

    -- * Default value (parsed lazily on first demand)
    stdlib,
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import System.FilePath (dropExtension, takeFileName)
import YCHR.Parsed (Module)
import YCHR.Parser
  ( ModuleHeader (..),
    OpTable,
    builtinOps,
    collectModuleHeader,
    mergeOps,
    parseModuleWith,
  )
import YCHR.StdLib.TH (embeddedStdLibSources)

-- | Errors that can arise while parsing the standard library.
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

-- | The default standard library, parsed once on first demand from
-- the sources embedded at compile time by 'embeddedStdLibSources'.
stdlib :: Map Text Module
stdlib = case parseStdLib $(embeddedStdLibSources) of
  Right m -> m
  Left err -> error ("Failed to parse embedded standard library: " ++ show err)
