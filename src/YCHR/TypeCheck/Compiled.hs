{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

-- | The pre-compiled YCHR type-checker as a 'SessionInput'.
--
-- The type-checker is itself a CHR program. Its source is embedded
-- into the binary at compile time via
-- 'YCHR.TypeCheck.TH.embeddedTypeCheckerSource'; the first reader of
-- 'typeCheckerProgram' pays the compile cost, everyone after gets
-- the memoized 'SessionInput'.
--
-- 'compileTypeChecker' is the underlying pure function; embedders
-- that want explicit control over when (or whether) the type-checker
-- is compiled can call it directly with their own source.
module YCHR.TypeCheck.Compiled
  ( -- * Pure API
    compileTypeChecker,

    -- * Default value (compiled lazily on first demand)
    typeCheckerProgram,
  )
where

import Data.Text (Text)
import YCHR.Compile.Pipeline (Error, compileModules)
import YCHR.Runtime.Session (SessionInput, toSessionInput)
import YCHR.TypeCheck.TH (embeddedTypeCheckerSource, typeCheckerPath)

-- | Compile the YCHR type-checker from its CHR source. Pure; the
-- @True@ flag passed to 'compileModules' disables type-checking the
-- type-checker itself (the bootstrap issue).
compileTypeChecker :: FilePath -> Text -> Either Error SessionInput
compileTypeChecker path src =
  case compileModules True [(path, src)] of
    Left err -> Left err
    Right (cp, _warnings) -> Right (toSessionInput cp)

-- | The default compiled type-checker. The source is embedded at
-- compile time; compilation runs once on first demand.
typeCheckerProgram :: SessionInput
typeCheckerProgram =
  case compileTypeChecker typeCheckerPath $(embeddedTypeCheckerSource) of
    Left err ->
      error ("Failed to compile embedded type checker: " ++ show err)
    Right si -> si
