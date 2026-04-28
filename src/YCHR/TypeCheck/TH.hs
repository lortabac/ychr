{-# LANGUAGE TemplateHaskell #-}

-- | Template Haskell splice for compiling the type-checker CHR program.
--
-- The type-checker is itself a CHR program (@typechecker\/typechecker.chr@).
-- This module compiles it at Haskell compile time so that the type-checker
-- is available as a pre-compiled program at runtime, with no compilation
-- overhead.
--
-- Type checking is not yet wired into the pipeline, so the bootstrap
-- issue (type-checking the type-checker) does not arise. When type
-- checking is enabled in the pipeline, the compilation here must use
-- a flag to disable it.
module YCHR.TypeCheck.TH (TypeCheckerProgram (..), compileTypeChecker) where

import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.Text qualified as T
import Language.Haskell.TH (Code, Q, runIO)
import Language.Haskell.TH.Syntax (Lift (..), addDependentFile, unsafeCodeCoerce)
import YCHR.Compile.Pipeline (CompiledProgram (..), ExportResolution (..), compileModules)
import YCHR.Types (QualifiedIdentifier, SymbolTable, UnqualifiedIdentifier)
import YCHR.VM (Program)

-- | A stripped-down compilation result holding only what the type-checker
-- CHR session needs at runtime. This avoids requiring @Lift@ instances
-- for 'OpTable', @[D.Function]@, @[Module]@, etc.
data TypeCheckerProgram = TypeCheckerProgram
  { program :: Program,
    exportMap :: Map UnqualifiedIdentifier ExportResolution,
    exportedSet :: Set QualifiedIdentifier,
    symbolTable :: SymbolTable
  }
  deriving (Lift)

-- | Compile @typechecker\/typechecker.chr@ at Template Haskell time.
compileTypeChecker :: Code Q TypeCheckerProgram
compileTypeChecker = unsafeCodeCoerce $ do
  let path = "typechecker/typechecker.chr"
  addDependentFile path
  contents <- runIO (readFile path)
  case compileModules True [(path, T.pack contents)] of
    Left err -> fail ("Failed to compile type-checker CHR: " ++ show err)
    Right (cp, _warnings) ->
      lift
        TypeCheckerProgram
          { program = cp.program,
            exportMap = cp.exportMap,
            exportedSet = cp.exportedSet,
            symbolTable = cp.symbolTable
          }
