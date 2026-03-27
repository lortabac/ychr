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
collectLibraries :: Map Text Module -> [Module] -> Either [CollectError] [Module]
collectLibraries stdlibMap userMods =
  let builtinSeeds = ["builtins" | Map.member "builtins" stdlibMap]
      seeds = builtinSeeds ++ concatMap libraryImports userMods
   in case resolveAll stdlibMap Set.empty Set.empty seeds of
        (_, libs, []) ->
          let rewritten = map rewriteImports (libs ++ userMods)
           in Right rewritten
        (_, _, errs) -> Left errs

-- | Extract library import names from a module.
libraryImports :: Module -> [Text]
libraryImports m = [n | Ann (LibraryImport n) _ <- modImports m]

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
  [Text] ->
  (Set Text, [Module], [CollectError])
resolveAll _ visited _ [] = (visited, [], [])
resolveAll stdlibMap visited path (name : rest)
  | Set.member name visited = resolveAll stdlibMap visited path rest
  | Set.member name path =
      let (visited', restMods, restErrs) = resolveAll stdlibMap visited path rest
       in (visited', restMods, CircularLibraryImport (Set.toList path ++ [name]) : restErrs)
  | otherwise =
      case Map.lookup name stdlibMap of
        Nothing ->
          let (visited', restMods, restErrs) = resolveAll stdlibMap visited path rest
           in (visited', restMods, UnknownLibrary name : restErrs)
        Just m ->
          let deps = libraryImports m
              path' = Set.insert name path
              (visited1, depMods, depErrs) = resolveAll stdlibMap visited path' deps
              visited2 = Set.insert name visited1
              (visited3, restMods, restErrs) = resolveAll stdlibMap visited2 path rest
           in (visited3, depMods ++ [m] ++ restMods, depErrs ++ restErrs)

-- | Rewrite all 'LibraryImport' entries to 'ModuleImport'.
rewriteImports :: Module -> Module
rewriteImports m = m {modImports = map rewrite (modImports m)}
  where
    rewrite (Ann (LibraryImport n) loc) = Ann (ModuleImport n) loc
    rewrite imp = imp
