{-# LANGUAGE OverloadedStrings #-}

-- | Compiling the YCHR type-checker into a 'SessionInput'.
--
-- The type-checker is itself a CHR program. Its sources, and the
-- standard library it imports, are explicit arguments: the @ychr@
-- library embeds nothing at compile time. The @ychr@ executable's
-- embedding component (@embed\/YCHR\/Embedded.hs@) splices the two
-- source lists in and compiles once, lazily, on first demand.
--
-- 'compileTypeCheckerModules' is the underlying pure function;
-- embedders that want explicit control over when (or whether) the
-- type-checker is compiled can call it directly with their own
-- sources.
module YCHR.Internal.TypeCheck.Compiled
  ( -- * Pure API
    compileTypeCheckerModules,
  )
where

import Data.Text (Text)
import YCHR.Internal.Compile.Pipeline (Error, compileModules)
import YCHR.Internal.Runtime.Session (SessionInput, toSessionInput)
import YCHR.Internal.StdLib (StdLib)

-- | Compile the YCHR type-checker from its CHR sources — all of them
-- compiled together as one program. Pure; the @True@ flag passed to
-- 'compileModules' bundles the standard library (the checker imports
-- @library(lists)@ and friends), so the 'StdLib' is required too.
compileTypeCheckerModules :: StdLib -> [(FilePath, Text)] -> Either Error SessionInput
compileTypeCheckerModules stdlib inputs =
  case compileModules stdlib True inputs of
    Left err -> Left err
    Right (cp, _warnings) -> Right (toSessionInput cp)
