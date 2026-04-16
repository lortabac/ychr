{-# LANGUAGE OverloadedStrings #-}

-- | Library import collector.
--
-- Resolves @use_module(library(name))@ imports against the standard
-- library map. The two responsibilities are now exposed as separate
-- functions so the pipeline can build per-module operator tables before
-- the full parse:
--
--   * 'resolveLibraryClosure' walks the dependency graph from a set of
--     seed library names, returns the reachable libraries in topological
--     order, and reports unknown or circularly-imported libraries.
--
--   * 'rewriteImports' rewrites every 'LibraryImport' to a 'ModuleImport'
--     so the renamer sees only one kind of import.
--
--   * 'addLibraryPrelude' prepends a @prelude@ import to each library
--     module (except the prelude itself).
module YCHR.Collect
  ( CollectError (..),
    resolveLibraryClosure,
    rewriteImports,
    addLibraryPrelude,
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import YCHR.Diagnostic (Diagnostic, noDiag)
import YCHR.Parsed

data CollectError
  = UnknownLibrary Text
  | CircularLibraryImport [Text]
  deriving (Show, Eq)

-- | Walk the transitive closure of library imports.
--
-- Seeds are the user-supplied library import names (typically extracted
-- from each user module's header). When @includeStdlib@ is 'True', every
-- library in the standard library map is also seeded so the full standard
-- library is available regardless of which libraries the user imports
-- explicitly.
--
-- Returns the reachable libraries in topological order (dependencies
-- first), or a list of 'CollectError' diagnostics if any seed names an
-- unknown library or a cycle is detected.
resolveLibraryClosure ::
  Bool ->
  Map Text Module ->
  [AnnP Text] ->
  Either [Diagnostic CollectError] [Module]
resolveLibraryClosure includeStdlib stdlibMap userSeeds =
  let seeds =
        (if includeStdlib then map noAnnP (Map.keys stdlibMap) else [])
          ++ userSeeds
   in case resolveAll stdlibMap Set.empty Set.empty seeds of
        (_, libs, []) -> Right libs
        (_, _, errs) -> Left errs

-- | DFS resolution of library dependencies.
--
-- Processes a worklist of library names. For each name:
--   - If already visited (fully processed), skip.
--   - If on the current path (gray), report a cycle.
--   - Look up in the stdlib map.
--   - Recursively resolve its own library imports.
--   - Append to the result list (post-order ensures dependencies come first).
--
-- The visited set is threaded through so that a library resolved by one
-- sibling is not re-resolved by the next.
resolveAll ::
  Map Text Module ->
  Set Text ->
  Set Text ->
  [AnnP Text] ->
  (Set Text, [Module], [Diagnostic CollectError])
resolveAll _ visited _ [] = (visited, [], [])
resolveAll stdlibMap visited path (ann : rest)
  | Set.member name visited = resolveAll stdlibMap visited path rest
  | Set.member name path =
      let (visited', restMods, restErrs) = resolveAll stdlibMap visited path rest
       in (visited', restMods, noDiag (AnnP (CircularLibraryImport (Set.toList path ++ [name])) ann.sourceLoc ann.parsed) : restErrs)
  | otherwise =
      case Map.lookup name stdlibMap of
        Nothing ->
          let (visited', restMods, restErrs) = resolveAll stdlibMap visited path rest
           in (visited', restMods, noDiag (AnnP (UnknownLibrary name) ann.sourceLoc ann.parsed) : restErrs)
        Just m ->
          let deps = libraryImports m
              path' = Set.insert name path
              (visited1, depMods, depErrs) = resolveAll stdlibMap visited path' deps
              visited2 = Set.insert name visited1
              (visited3, restMods, restErrs) = resolveAll stdlibMap visited2 path rest
           in (visited3, depMods ++ [m] ++ restMods, depErrs ++ restErrs)
  where
    name = ann.node

-- | Extract library import names from a module.
libraryImports :: Module -> [AnnP Text]
libraryImports m = [AnnP n loc p | AnnP (LibraryImport n _) loc p <- m.imports]

-- | Add a prelude import to every library module that does not already
-- declare itself to be the prelude.
addLibraryPrelude :: [Module] -> [Module]
addLibraryPrelude = map go
  where
    go m
      | m.name == "prelude" = m
      | otherwise = m {imports = noAnnP (LibraryImport "prelude" Nothing) : m.imports}

-- | Rewrite every 'LibraryImport' to a 'ModuleImport'.
rewriteImports :: [Module] -> [Module]
rewriteImports = map rewriteOne
  where
    rewriteOne m = m {imports = map rewrite m.imports}
    rewrite (AnnP (LibraryImport n il) loc p) = AnnP (ModuleImport n il) loc p
    rewrite imp = imp
