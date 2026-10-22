-- | Compile parsed modules, throwing on failure. Shared by "YCHR.DSL"
-- and "YCHR.Convert".
module YCHR.Internal.CompileOrThrow (compileOrThrow) where

import Control.Exception (throwIO)
import YCHR.Internal.Compile.Pipeline (CompiledProgram, compileParsedModules)
import YCHR.Internal.Parsed (Module)
import YCHR.Internal.StdLib (StdLib)

-- | Compile with the whole standard library and drop the warnings.
-- Throws the 'YCHR.Internal.Compile.Pipeline.Error'.
compileOrThrow :: StdLib -> [Module] -> IO CompiledProgram
compileOrThrow stdlib modules = case compileParsedModules stdlib True modules of
  Left err -> throwIO err
  Right (cp, _warnings) -> pure cp
