{-# LANGUAGE TemplateHaskell #-}

-- | The compile-time resources the @ychr@ library takes as explicit
-- inputs.
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
-- An embedder outside this repository writes the same few lines: splice
-- (or read) its own source lists and hand them to @parseStdLib@ /
-- @compileTypeCheckerModules@. See
-- @docs\/how-to\/embed-a-chr-module.md@.
module YCHR.Embedded
  ( stdlib,
    typeCheckerProgram,
  )
where

import YCHR.Embedded.StdLib qualified as StdLib
import YCHR.Embedded.TypeCheck qualified as TypeCheck
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
-- example, a compile-only run) never pays for it.
typeCheckerProgram :: SessionInput
typeCheckerProgram =
  case compileTypeCheckerModules stdlib $(TypeCheck.embeddedTypeCheckerSources) of
    Right si -> si
    Left err -> error ("Failed to compile embedded typechecker: " ++ show err)
