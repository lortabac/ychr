-- | Resources provider for the MicroHs build.
--
-- MicroHs has no Template Haskell (@dev-docs\/MICROHS_GAPS.md@, gap 5),
-- so this twin of @embed\/YCHR\/Embedded.hs@ cannot splice the bundled
-- sources into the binary. It reads them at run time instead, from
-- @$YCHR_LIB_DIR@ or the current directory when that variable is unset
-- (see "YCHR.Internal.Resources"), which the GHC test suite exercises.
--
-- The two modules are switched by the @if impl(...)@ blocks in
-- @ychr.cabal@: @embed\/@ under GHC, @src\/mhs\/@ under MicroHs.
module YCHR.Embedded (loadResources) where

import YCHR.Internal.Resources (loadResources)
