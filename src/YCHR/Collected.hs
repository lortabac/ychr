{-# LANGUAGE DuplicateRecordFields #-}

-- | Collected AST: the module representation produced by the collect
-- phase ('YCHR.Collect.rewriteImports') and consumed by 'YCHR.Rename'
-- and 'YCHR.Resolve'.
--
-- It is structurally identical to 'YCHR.Parsed.Module' except for one
-- field: imports. The parser's 'YCHR.Parsed.Import' distinguishes a
-- @use_module(M)@ ('ModuleImport') from a @use_module(library(L))@
-- ('LibraryImport'). That distinction matters only inside the collect
-- phase, which resolves the library closure and then rewrites every
-- library import to a plain module import. Once collection is done the
-- two are indistinguishable, so 'CollectedModule' carries a single
-- 'CollectedImport' with no library/module tag — making a stray
-- 'LibraryImport' unrepresentable in everything downstream of
-- 'rewriteImports' rather than relying on convention.
--
-- The shared field names (matched against 'YCHR.Parsed.Module') let the
-- rename and resolve passes access fields with 'OverloadedRecordDot'
-- without caring which record they hold.
module YCHR.Collected
  ( CollectedModule (..),
    CollectedImport (..),
    collectedFromParsed,
  )
where

import Data.Text (Text)
import YCHR.Parsed
  ( Ann,
    AnnP (..),
    Declaration,
    FunctionEquation,
    Import (..),
    Module (..),
    Rule,
    SourceLoc,
    TypeDefinition,
  )

-- | An import after collection: just the source module name and an
-- optional import list. The library-vs-module distinction is gone.
data CollectedImport = CollectedImport
  { importModule :: Text,
    importItems :: Maybe [Declaration]
  }
  deriving (Show, Eq)

-- | A module after the collect phase. Mirrors 'YCHR.Parsed.Module'
-- field-for-field, differing only in the element type of 'imports'.
data CollectedModule = CollectedModule
  { name :: Text,
    nameLoc :: SourceLoc,
    imports :: [AnnP CollectedImport],
    decls :: [Ann Declaration],
    extensionTypes :: [Ann Declaration],
    typeDecls :: [Ann TypeDefinition],
    rules :: [Rule],
    equations :: [AnnP FunctionEquation],
    extensions :: [AnnP FunctionEquation],
    classExtensions :: [AnnP FunctionEquation],
    exports :: Maybe (AnnP [Declaration])
  }
  deriving (Show, Eq)

-- | Convert a parsed 'Module' to a 'CollectedModule', collapsing both
-- import kinds into 'CollectedImport'. This is the single boundary at
-- which the library-vs-module distinction is erased; everything
-- downstream sees only 'CollectedImport'. Defined here (rather than in
-- 'YCHR.Collect') so that callers need not bring 'CollectedModule''s
-- field names into scope: doing so would make their own parsed-'Module'
-- record updates ambiguous (the two records share field names).
collectedFromParsed :: Module -> CollectedModule
collectedFromParsed m =
  CollectedModule
    { name = m.name,
      nameLoc = m.nameLoc,
      imports = map (fmap collectedImport) m.imports,
      decls = m.decls,
      extensionTypes = m.extensionTypes,
      typeDecls = m.typeDecls,
      rules = m.rules,
      equations = m.equations,
      extensions = m.extensions,
      classExtensions = m.classExtensions,
      exports = m.exports
    }
  where
    collectedImport (ModuleImport n il) = CollectedImport n il
    collectedImport (LibraryImport n il) = CollectedImport n il
