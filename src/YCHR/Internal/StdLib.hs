{-# LANGUAGE OverloadedStrings #-}

-- | Standard library loading.
--
-- The @libraries\/@ directory ships a small set of @.chr@ files
-- (@prelude@, @lists@, @pairs@, @maybe@, @strings@, @meta@, @search@,
-- @state@, @chr@) that every user program may import via
-- @:- use_module(library(...))@.
-- 'parseStdLib' turns their sources into the 'StdLib' value the compiler
-- takes as an explicit input. Where the sources come from is the
-- caller's business: the @ychr@ executable embeds them at compile time
-- (see @embed\/YCHR\/Embedded.hs@ under GHC, and the modules @make
-- resources@ writes under MicroHs), while a library embedder reads them
-- from disk. See
-- @docs\/how-to\/embed-a-chr-module.md@.
module YCHR.Internal.StdLib
  ( -- * Types
    StdLib (..),
    StdLibError (..),

    -- * Pure API
    parseStdLib,
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import System.FilePath (dropExtension, takeFileName)
import YCHR.Internal.DeclMacro
  ( ExpandedModule (..),
    buildDeclMacroEnv,
    expandAndConvert,
    scopeFromTerms,
  )
import YCHR.Internal.Parsed (Module)
import YCHR.Internal.Parser
  ( ModuleHeader (..),
    builtinOps,
    collectModuleHeader,
    defaultModuleNameForSource,
    mergeOps,
    parseModuleTermsWith,
  )

-- | The parsed standard library: every bundled library, keyed by its
-- bare library name (the name a @:- use_module(library(name))@ import
-- spells). Produced by 'parseStdLib' and passed explicitly to every
-- entry point that compiles or type-checks, so the library itself
-- carries no compile-time embedding.
newtype StdLib = StdLib (Map Text Module)

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
  | -- | Expanding a library's declaration-macro uses failed.
    StdLibExpansionError FilePath String
  deriving (Show)

-- | Parse a list of @(path, source)@ pairs as the standard library.
-- Pure: any IO required to get the sources is the caller's problem.
--
-- All libraries share one merged operator table. Declaration macros
-- are expanded here, using what each library imports (plus the
-- prelude). Macro definitions stay on the 'Module' so user code can use
-- the exported ones.
parseStdLib :: [(FilePath, Text)] -> Either StdLibError StdLib
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
  termsOf <-
    traverse
      ( \(path, src) -> case parseModuleTermsWith table path src of
          Left e -> Left (StdLibParseError path (show e))
          Right ts -> Right (path, ts)
      )
      sources
  let scopes =
        [scopeFromTerms (defaultModuleNameForSource path) ts | (path, ts) <- termsOf]
      env = buildDeclMacroEnv scopes
  entries <- traverse (convertLib env) (zip scopes termsOf)
  pure (StdLib (Map.fromList entries))
  where
    libName path = T.pack (dropExtension (takeFileName path))
    convertLib env (scope, (path, ts)) =
      let em = expandAndConvert env scope ts
       in case (em.expansionErrors, em.parseErrors) of
            (errs@(_ : _), _) -> Left (StdLibExpansionError path (show errs))
            ([], errs@(_ : _)) -> Left (StdLibValidationError path (show errs))
            ([], []) -> Right (libName path, em.converted)
