{-# LANGUAGE OverloadedStrings #-}

-- | Library import collector.
--
-- Runs after parsing and before renaming. Resolves @use_module(library(name))@
-- imports by looking up library modules in the standard library, collecting
-- transitive dependencies, and prepending them to the module list. All
-- 'LibraryImport' entries are rewritten to 'ModuleImport' so the renamer
-- sees only regular imports.
module YCHR.Collect (collectLibraries, CollectError (..)) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import YCHR.Parsed

data CollectError
  = UnknownLibrary Text
  | CircularLibraryImport [Text]
  deriving (Show, Eq)

-- | Resolve library imports and prepend library modules.
--
-- 1. Scans all modules for 'LibraryImport' entries.
-- 2. Looks up each in the stdlib map (reporting 'UnknownLibrary' if missing).
-- 3. Recursively collects transitive library dependencies via DFS.
-- 4. Detects circular imports.
-- 5. Prepends library modules in topological order (dependencies first).
-- 6. Rewrites all 'LibraryImport' to 'ModuleImport' in every module.
collectLibraries :: Bool -> Map Text Module -> [Module] -> Either [AnnP CollectError] [Module]
collectLibraries includeStdlib stdlibMap userMods =
  let seeds =
        (if includeStdlib then map noAnnP (Map.keys stdlibMap) else [])
          ++ concatMap libraryImports userMods
   in case resolveAll stdlibMap Set.empty Set.empty seeds of
        (_, libs, []) ->
          let withPrelude = map addPreludeImport libs
              rewritten = map rewriteImports (withPrelude ++ userMods)
           in Right rewritten
        (_, _, errs) -> Left errs

-- | Extract library import names from a module.
libraryImports :: Module -> [AnnP Text]
libraryImports m = [AnnP n loc p | AnnP (LibraryImport n _) loc p <- m.imports]

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
  (Set Text, [Module], [AnnP CollectError])
resolveAll _ visited _ [] = (visited, [], [])
resolveAll stdlibMap visited path (ann : rest)
  | Set.member name visited = resolveAll stdlibMap visited path rest
  | Set.member name path =
      let (visited', restMods, restErrs) = resolveAll stdlibMap visited path rest
       in (visited', restMods, AnnP (CircularLibraryImport (Set.toList path ++ [name])) ann.sourceLoc ann.parsed : restErrs)
  | otherwise =
      case Map.lookup name stdlibMap of
        Nothing ->
          let (visited', restMods, restErrs) = resolveAll stdlibMap visited path rest
           in (visited', restMods, AnnP (UnknownLibrary name) ann.sourceLoc ann.parsed : restErrs)
        Just m ->
          let deps = libraryImports m
              path' = Set.insert name path
              (visited1, depMods, depErrs) = resolveAll stdlibMap visited path' deps
              visited2 = Set.insert name visited1
              (visited3, restMods, restErrs) = resolveAll stdlibMap visited2 path rest
           in (visited3, depMods ++ [m] ++ restMods, depErrs ++ restErrs)
  where
    name = ann.node

-- | Add a prelude import to a library module (unless it is the prelude itself).
addPreludeImport :: Module -> Module
addPreludeImport m
  | m.name == "prelude" = m
  | otherwise = m {imports = noAnnP (LibraryImport "prelude" Nothing) : m.imports}

-- | Rewrite all 'LibraryImport' entries to 'ModuleImport'.
rewriteImports :: Module -> Module
rewriteImports m = m {imports = map rewrite m.imports}
  where
    rewrite (AnnP (LibraryImport n il) loc p) = AnnP (ModuleImport n il) loc p
    rewrite imp = imp
