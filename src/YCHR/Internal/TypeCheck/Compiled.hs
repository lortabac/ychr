{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

-- | The pre-compiled YCHR type-checker as a 'SessionInput'.
--
-- The type-checker is itself a CHR program. Its source is embedded
-- into the binary at compile time via
-- 'YCHR.Internal.TypeCheck.TH.embeddedTypeCheckerSource'; the first reader of
-- 'typeCheckerProgram' pays the compile cost, everyone after gets
-- the memoized 'SessionInput'.
--
-- 'compileTypeChecker' is the underlying pure function; embedders
-- that want explicit control over when (or whether) the type-checker
-- is compiled can call it directly with their own source.
module YCHR.Internal.TypeCheck.Compiled
  ( -- * Pure API
    compileTypeChecker,
    compileTypeCheckerModules,

    -- * Default values (compiled lazily on first demand)
    typeCheckerProgram,
    typeChecker2Program,
  )
where

import Data.Text (Text)
import YCHR.Internal.Compile.Pipeline (Error, compileModules)
import YCHR.Internal.Runtime.Session (SessionInput, toSessionInput)
import YCHR.Internal.TypeCheck.TH
  ( embeddedTypeChecker2Sources,
    embeddedTypeCheckerSource,
    typeCheckerPath,
  )

-- | Compile the YCHR type-checker from its CHR source. Pure; the
-- @True@ flag passed to 'compileModules' bundles the standard library
-- (the checker imports @library(lists)@ and friends).
compileTypeChecker :: FilePath -> Text -> Either Error SessionInput
compileTypeChecker path src = compileTypeCheckerModules [(path, src)]

-- | 'compileTypeChecker' for a checker that spans several modules —
-- all of them compiled together as one program.
compileTypeCheckerModules :: [(FilePath, Text)] -> Either Error SessionInput
compileTypeCheckerModules inputs =
  case compileModules True inputs of
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

-- | The all-CHR type-checker (@typechecker2\/@), which does the whole
-- job in CHR rather than driving a solver from Haskell. Built
-- alongside the one above while it is ported; see
-- 'YCHR.Internal.TypeCheck.V2'.
typeChecker2Program :: SessionInput
typeChecker2Program =
  case compileTypeCheckerModules $(embeddedTypeChecker2Sources) of
    Left err ->
      error ("Failed to compile embedded typechecker2: " ++ show err)
    Right si -> si
