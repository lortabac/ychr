{-# LANGUAGE TemplateHaskell #-}

-- | The resources the @ychr@ library takes as explicit inputs.
--
-- The library itself embeds nothing (@dev-docs\/MICROHS_GAPS.md@,
-- gap 5): the standard library and the compiled type-checker are
-- explicit arguments of every entry point that needs them. This module
-- is where the components that /do/ want a self-contained binary get
-- them — a Template Haskell splice of @libraries\/*.chr@ and
-- @typechecker\/*.chr@.
--
-- It lives in the shared @embed\/@ source directory, so the @ychr@
-- executable, the test suite, the benchmark and the @stlc@ example each
-- compile it into their own component. The cost is one extra compile of
-- the two generator modules per component.
--
-- The MicroHs build cannot splice, so it compiles
-- @src\/mhs\/YCHR\/Embedded.hs@ instead: the same 'loadResources' entry
-- point, backed by "YCHR.Internal.Resources" reading @$YCHR_LIB_DIR@ (or
-- the current directory) at run time. The @ychr@ executable imports only
-- 'loadResources', so it has one code path on both compilers; the pure
-- 'stdlib' and 'typeCheckerProgram' below are this component's
-- compile-time-embedded values.
--
-- An embedder outside this repository writes the same few lines: splice
-- (or read) its own source lists and hand them to @parseStdLib@ /
-- @compileTypeCheckerModules@. See
-- @docs\/how-to\/embed-a-chr-module.md@.
module YCHR.Embedded
  ( stdlib,
    typeCheckerProgram,
    loadResources,
  )
where

import Data.Text (Text)
import YCHR.Embedded.StdLib qualified as StdLib
import YCHR.Embedded.TypeCheck qualified as TypeCheck
import YCHR.Internal.Resources (Resources (Resources))
import YCHR.Internal.Runtime.Session (SessionInput)
import YCHR.Internal.StdLib (StdLib, parseStdLib)
import YCHR.Internal.TypeCheck.Compiled (compileTypeCheckerModules)

-- | The bundled standard library, parsed once on first demand.
stdlib :: StdLib
stdlib = case parseStdLib $(StdLib.embeddedStdLibSources) of
  Right m -> m
  Left err -> error ("Failed to parse embedded standard library: " ++ show err)

-- | The compiled type-checker, built once on first demand. Lazy: a
-- component that never type-checks a program or a goal (the @stlc@
-- example) never pays for it, and a failure keeps the 'error' the
-- MicroHs provider's lazy binding also has.
typeCheckerProgram :: SessionInput
typeCheckerProgram =
  case compileTypeCheckerModules stdlib $(TypeCheck.embeddedTypeCheckerSources) of
    Right si -> si
    Left err -> error ("Failed to compile embedded typechecker: " ++ show err)

-- | Both resources as an IO action, so the @ychr@ executable can share
-- one code path with the MicroHs build, which loads them from disk.
-- Under GHC nothing is read at run time: the values above are baked into
-- the binary, and this can only return 'Right'.
loadResources :: IO (Either Text Resources)
loadResources = pure (Right (Resources stdlib typeCheckerProgram))
