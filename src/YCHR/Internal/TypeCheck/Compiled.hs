{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

-- | The pre-compiled YCHR type-checker as a 'SessionInput'.
--
-- The type-checker is itself a CHR program. Its sources are embedded
-- into the binary at compile time via
-- 'YCHR.Internal.TypeCheck.TH.embeddedTypeCheckerSources'; the first
-- reader of 'typeCheckerProgram' pays the compile cost, everyone
-- after gets the memoized 'SessionInput'.
--
-- 'compileTypeCheckerModules' is the underlying pure function;
-- embedders that want explicit control over when (or whether) the
-- type-checker is compiled can call it directly with their own
-- sources.
module YCHR.Internal.TypeCheck.Compiled
  ( -- * Pure API
    compileTypeCheckerModules,

    -- * Default value (compiled lazily on first demand)
    typeCheckerProgram,
  )
where

import Data.Text (Text)
import YCHR.Internal.Compile.Pipeline (Error, compileModules)
import YCHR.Internal.Runtime.Session (SessionInput, toSessionInput)
import YCHR.Internal.TypeCheck.TH (embeddedTypeCheckerSources)

-- | Compile the YCHR type-checker from its CHR sources — all of them
-- compiled together as one program. Pure; the @True@ flag passed to
-- 'compileModules' bundles the standard library (the checker imports
-- @library(lists)@ and friends).
compileTypeCheckerModules :: [(FilePath, Text)] -> Either Error SessionInput
compileTypeCheckerModules inputs =
  case compileModules True inputs of
    Left err -> Left err
    Right (cp, _warnings) -> Right (toSessionInput cp)

-- | The default compiled type-checker (@typechecker\/@). The sources
-- are embedded at compile time; compilation runs once on first demand.
typeCheckerProgram :: SessionInput
typeCheckerProgram =
  case compileTypeCheckerModules $(embeddedTypeCheckerSources) of
    Left err ->
      error ("Failed to compile embedded typechecker: " ++ show err)
    Right si -> si
