{-# LANGUAGE OverloadedStrings #-}

-- | Library import collector.
--
-- Resolves @use_module(library(name))@ imports against the standard
-- library map. The work is split across separate functions so the
-- pipeline can build per-module operator tables before the full parse:
--
--   * 'resolveLibraryClosure' walks the dependency graph from a set of
--     seed library names, returns the reachable libraries in topological
--     order, and reports unknown or circularly-imported libraries.
--
--   * 'rewriteImports' converts each parsed 'Module' to a
--     'CollectedModule', collapsing 'LibraryImport' and 'ModuleImport'
--     into the single 'CollectedImport' so everything downstream sees
--     only one kind of import.
--
--   * 'selfNamedLibraryImports' reports a module that imports the
--     library of its own name.
--
--   * 'unknownModuleImports' reports a bare @use_module(M)@ naming
--     neither a supplied module nor @prelude@.
--
--   * 'addLibraryPrelude' prepends a @prelude@ import to each library
--     module (except the prelude itself).
module YCHR.Internal.Collect
  ( CollectError (..),
    BareImportHint (..),
    ModuleImportScope (..),
    resolveLibraryClosure,
    selfNamedLibraryImports,
    unknownModuleImports,
    rewriteImports,
    addLibraryPrelude,
  )
where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, modify')
import Control.Monad.Trans.Writer.CPS (Writer, runWriter, tell)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import YCHR.Internal.Collected (CollectedModule, collectedFromParsed)
import YCHR.Internal.Diagnostic (Diagnostic, noDiag)
import YCHR.Internal.Parsed

-- | Why import collection failed.
data CollectError
  = -- | No bundled library has this name.
    UnknownLibrary Text
  | -- | Library import cycle: the libraries on the current path, in
    -- sorted order (not import order), then the one that closes it.
    CircularLibraryImport [Text]
  | -- | A module imports the library of its own name.
    SelfNamedLibraryImport Text
  | -- | Two user modules declare the same name. Carries the name and
    -- the file paths that declare it, in input order.
    DuplicateModuleName Text [FilePath]
  | -- | A bare @use_module(M)@ names a module that is neither a
    -- supplied module nor @prelude@. Carries the name and a hint
    -- about why, if a likely cause is known.
    UnknownModuleImport Text BareImportHint
  deriving (Show, Eq)

-- | Why a bare 'ModuleImport' name went unmatched, used to pick a hint
-- for 'UnknownModuleImport'.
data BareImportHint
  = -- | The name is a bundled library, importable only via
    -- @use_module(library(M))@.
    BundledLibraryName
  | -- | @host@ is a built-in qualifier, not a module.
    HostQualifier
  | -- | A module named @\<M\>@ exists, which is what a header-less
    -- file named @M.chr@ is called.
    HeaderlessModule
  | -- | No likely cause found.
    NoBareImportHint
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
   in case runWriter (evalStateT (resolveAll stdlibMap Set.empty seeds) Set.empty) of
        (libs, []) -> Right libs
        (_, errs) -> Left errs

-- | The library walk: the set of fully processed libraries as state,
-- errors as output.
type Walk = StateT (Set Text) (Writer [Diagnostic CollectError])

-- | DFS resolution of library dependencies.
--
-- Processes a worklist of library names. For each name:
--   - If already visited (fully processed), skip.
--   - If on the current path (gray), report a cycle.
--   - Look up in the stdlib map.
--   - Recursively resolve its own library imports.
--   - Append to the result list (post-order ensures dependencies come first).
--
-- The visited set is the state, so a library resolved by one sibling is
-- not re-resolved by the next.
resolveAll :: Map Text Module -> Set Text -> [AnnP Text] -> Walk [Module]
resolveAll stdlibMap path = fmap concat . traverse resolveOne
  where
    resolveOne ann = do
      visited <- get
      step visited ann
    step visited ann
      | Set.member name visited = pure []
      | Set.member name path =
          report (CircularLibraryImport (Set.toList path ++ [name]))
      | otherwise = case Map.lookup name stdlibMap of
          Nothing -> report (UnknownLibrary name)
          Just m -> do
            depMods <- resolveAll stdlibMap (Set.insert name path) (libraryImports m)
            modify' (Set.insert name)
            pure (depMods ++ [m])
      where
        name = ann.node
        report e = [] <$ lift (tell [noDiag (AnnP e ann.sourceLoc ann.parsed)])

-- | Extract library import names from a module.
libraryImports :: Module -> [AnnP Text]
libraryImports m = [AnnP n loc p | AnnP (LibraryImport n _) loc p <- m.imports]

-- | Report every @use_module(library(N))@ written by a module that is
-- itself named @N@.
--
-- Module identity is the name alone, so such a module /is/ the library
-- as far as everything downstream is concerned: the bundled copy is
-- dropped by
-- @YCHR.Internal.Compile.Pipeline.finalizeCompilation@ and the import
-- can never bring anything into scope. Left unreported it looks like a
-- library that silently exports nothing.
--
-- Call this only once the library closure has resolved, so that a name
-- that is not a bundled library at all has already been reported as
-- 'UnknownLibrary'.
selfNamedLibraryImports :: [Module] -> [Diagnostic CollectError]
selfNamedLibraryImports mods =
  [ noDiag (AnnP (SelfNamedLibraryImport n) loc p)
  | m <- mods,
    AnnP (LibraryImport n _) loc p <- m.imports,
    n == m.name
  ]

-- | The two name sets 'unknownModuleImports' checks a bare import
-- against.
data ModuleImportScope = ModuleImportScope
  { -- | Every name a bare @use_module@ may legally give: every
    -- supplied module, plus @prelude@.
    importable :: Set Text,
    -- | Bundled library names. Only consulted for the hint, since a
    -- bundled library is never itself importable.
    bundledLibraries :: Set Text
  }

-- | Report each bare @use_module(M)@ whose @M@ is not in
-- 'importable'. The header-less check comes first, since a file can
-- share its name with a library.
unknownModuleImports :: ModuleImportScope -> [Module] -> [Diagnostic CollectError]
unknownModuleImports scope mods =
  [ noDiag (AnnP (UnknownModuleImport n (bareImportHint n)) loc p)
  | m <- mods,
    AnnP (ModuleImport n _) loc p <- m.imports,
    Set.notMember n scope.importable
  ]
  where
    bareImportHint n
      | n == "host" = HostQualifier
      | Set.member ("<" <> n <> ">") scope.importable = HeaderlessModule
      | Set.member n scope.bundledLibraries = BundledLibraryName
      | otherwise = NoBareImportHint

-- | Add a prelude import to every library module that does not already
-- declare itself to be the prelude.
--
-- The library-side counterpart of
-- @YCHR.Internal.Compile.Pipeline.addPreludeImport@, and unconditional
-- for the same reason: the prelude is imported in full, always. A
-- library that writes a /narrowed/ prelude import is rejected by
-- @YCHR.Internal.Rename.validateImportLists@ (YCHR-20019).
addLibraryPrelude :: [Module] -> [Module]
addLibraryPrelude = map go
  where
    go :: Module -> Module
    go m
      | m.name == "prelude" = m
      | otherwise = m {imports = noAnnP (LibraryImport "prelude" Nothing) : m.imports}

-- | Convert each parsed 'Module' to a 'CollectedModule', collapsing both
-- import kinds into 'CollectedImport'. After this point the types carry
-- no library-vs-module distinction. The per-module conversion lives in
-- "YCHR.Internal.Collected" ('collectedFromParsed').
rewriteImports :: [Module] -> [CollectedModule]
rewriteImports = map collectedFromParsed
