-- | The program checks the CLI, the REPL, the playground and the golden
-- tests run together: the type checker and the @:- constraint_use@
-- check. @--no-check@ skips both.
module YCHR.Internal.ProgramCheck
  ( ProgramCheck (..),
    checkProgram,
  )
where

import YCHR.Internal.Compile.Pipeline (Warning (..))
import YCHR.Internal.ConstraintUse (checkConstraintUse)
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Display (displayMsg)
import YCHR.Internal.Runtime.Session (SessionInput)
import YCHR.Internal.TypeCheck (TypeCheckResult (..), typeCheckProgram)

-- | What 'checkProgram' reports.
data ProgramCheck = ProgramCheck
  { -- | Rendered with 'displayMsg': the @:- constraint_use@ violations,
    -- then the type errors.
    errors :: [String],
    -- | The type checker's warnings as one 'TypeCheckWarnings', or
    -- nothing when there are none.
    warnings :: [Warning]
  }

-- | Type-check a program and check its rule heads against their
-- @:- constraint_use@ declarations.
checkProgram :: SessionInput -> D.Program -> IO ProgramCheck
checkProgram typeChecker prog = do
  result <- typeCheckProgram typeChecker prog
  pure
    ProgramCheck
      { errors =
          map displayMsg (checkConstraintUse prog)
            ++ map displayMsg result.errors,
        warnings = [TypeCheckWarnings result.warnings | not (null result.warnings)]
      }
