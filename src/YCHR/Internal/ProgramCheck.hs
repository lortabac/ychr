-- | The program checks the CLI, the REPL, the playground and the golden
-- tests run together: the type checker, the @:- constraint_use@ check
-- and the exhaustiveness check. @--no-check@ skips all three.
module YCHR.Internal.ProgramCheck
  ( ProgramCheck (..),
    checkProgram,
    constraintUseErrors,
    exhaustivenessReport,
    typeCheckReport,
  )
where

import YCHR.Internal.Compile.Pipeline (CompiledProgram (..), Warning (..))
import YCHR.Internal.ConstraintUse (checkConstraintUse)
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Display (displayMsg)
import YCHR.Internal.Runtime.Session (SessionInput)
import YCHR.Internal.TypeCheck (TypeCheckResult (..), typeCheckProgram)

-- | What a check reports.
data ProgramCheck = ProgramCheck
  { -- | The errors, already rendered to text with 'displayMsg'.
    errors :: [String],
    -- | The exhaustiveness warnings, then the type checker's warnings.
    -- Each kind is one 'Warning', left out when empty.
    warnings :: [Warning]
  }

-- | 'constraintUseErrors', 'exhaustivenessReport' and 'typeCheckReport'
-- together.
checkProgram :: SessionInput -> CompiledProgram -> IO ProgramCheck
checkProgram typeChecker prog = do
  report <- typeCheckReport typeChecker prog.desugaredProgram
  pure
    ProgramCheck
      { errors = constraintUseErrors prog.desugaredProgram ++ report.errors,
        warnings = exhaustivenessReport prog ++ report.warnings
      }

-- | The @:- constraint_use@ violations of a program, rendered.
constraintUseErrors :: D.Program -> [String]
constraintUseErrors prog = map displayMsg (checkConstraintUse prog)

-- | The program's non-exhaustive functions, as one
-- 'ExhaustivenessWarnings', or nothing when there are none.
exhaustivenessReport :: CompiledProgram -> [Warning]
exhaustivenessReport prog =
  [ExhaustivenessWarnings ws | let ws = prog.exhaustivenessWarnings, not (null ws)]

-- | Type-check a program. The errors are the type errors only.
typeCheckReport :: SessionInput -> D.Program -> IO ProgramCheck
typeCheckReport typeChecker prog = do
  result <- typeCheckProgram typeChecker prog
  pure
    ProgramCheck
      { errors = map displayMsg result.errors,
        warnings = [TypeCheckWarnings result.warnings | not (null result.warnings)]
      }
