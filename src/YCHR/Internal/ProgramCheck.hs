-- | The program checks the CLI, the REPL, the playground and the golden
-- tests run together: the type checker and the @:- constraint_use@
-- check. @--no-check@ skips both.
module YCHR.Internal.ProgramCheck
  ( ProgramCheck (..),
    checkProgram,
    constraintUseErrors,
    typeCheckReport,
  )
where

import YCHR.Internal.Compile.Pipeline (Warning (..))
import YCHR.Internal.ConstraintUse (checkConstraintUse)
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Display (displayMsg)
import YCHR.Internal.Runtime.Session (SessionInput)
import YCHR.Internal.TypeCheck (TypeCheckResult (..), typeCheckProgram)

-- | What a check reports.
data ProgramCheck = ProgramCheck
  { -- | The errors, already rendered to text with 'displayMsg'.
    errors :: [String],
    -- | The type checker's warnings as one 'TypeCheckWarnings', or
    -- nothing when there are none.
    warnings :: [Warning]
  }

-- | 'constraintUseErrors' followed by 'typeCheckReport'.
checkProgram :: SessionInput -> D.Program -> IO ProgramCheck
checkProgram typeChecker prog = do
  report <- typeCheckReport typeChecker prog
  pure
    ProgramCheck
      { errors = constraintUseErrors prog ++ report.errors,
        warnings = report.warnings
      }

-- | The @:- constraint_use@ violations of a program, rendered.
constraintUseErrors :: D.Program -> [String]
constraintUseErrors prog = map displayMsg (checkConstraintUse prog)

-- | Type-check a program. The errors are the type errors only.
typeCheckReport :: SessionInput -> D.Program -> IO ProgramCheck
typeCheckReport typeChecker prog = do
  result <- typeCheckProgram typeChecker prog
  pure
    ProgramCheck
      { errors = map displayMsg result.errors,
        warnings = [TypeCheckWarnings result.warnings | not (null result.warnings)]
      }
