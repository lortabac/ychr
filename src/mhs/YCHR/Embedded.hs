-- | Resources provider for the MicroHs build.
--
-- MicroHs has no Template Haskell (@dev-docs\/MICROHS_GAPS.md@, gap 5),
-- so this twin of @embed\/YCHR\/Embedded.hs@ cannot splice the bundled
-- sources into the binary. It does not parse them at run time either:
-- the build step in @codegen\/@ (@make resources@) decodes the standard
-- library and the type-checker once and writes them as literal Haskell
-- modules, which MicroHs compiles cheaply
-- (@dev-docs\/MICROHS_PERFORMANCE.md@, option B).
--
-- The generated modules live under @generated\/@, which the executable's
-- @if impl(mhs)@ stanza adds to its @hs-source-dirs@; they are built
-- from this checkout's @libraries\/*.chr@ and @typechecker\/*.chr@ and
-- are not committed, so @make resources@ must have run since those
-- sources last changed.
--
-- This provider reads nothing at run time and ignores @YCHR_LIB_DIR@:
-- the bundled resources are always the ones the binary was built with.
-- "YCHR.Internal.Resources" provides the on-disk loader for library
-- embedders and for the GHC test suite.
--
-- The two modules are switched by the @if impl(...)@ blocks in
-- @ychr.cabal@: @embed\/@ under GHC, @src\/mhs\/@ under MicroHs.
module YCHR.Embedded
  ( stdlib,
    typeCheckerProgram,
    loadResources,
  )
where

import Data.Text (Text)
import YCHR.Embedded.Generated.StdLib qualified as GeneratedStdLib
import YCHR.Embedded.Generated.TypeCheck qualified as GeneratedTypeCheck
import YCHR.Internal.Resources (Resources (Resources))
import YCHR.Internal.Runtime.Session (SessionInput)
import YCHR.Internal.StdLib (StdLib)

-- | The bundled standard library, decoded at build time.
stdlib :: StdLib
stdlib = GeneratedStdLib.stdlib

-- | The compiled type-checker, decoded at build time.
typeCheckerProgram :: SessionInput
typeCheckerProgram = GeneratedTypeCheck.typeCheckerProgram

-- | Both resources as an IO action, so the @ychr@ executable can share
-- one code path with the GHC build, whose provider also only returns
-- already-embedded values. It cannot fail: nothing is read at run time.
loadResources :: IO (Either Text Resources)
loadResources = pure (Right (Resources stdlib typeCheckerProgram))
