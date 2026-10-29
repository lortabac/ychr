-- | MicroHs stand-in for the GHC-only Chez backend.
--
-- The MicroHs base library has no @createProcess@ or pipe handles, so the
-- REPL's Scheme backend is not available in that build. The option parses
-- and fails cleanly at startup.
module YCHR.Internal.Repl.Chez
  ( Chez,
    ChezFailure (..),
    startChez,
    restartChez,
    stopChez,
    prepareChezCode,
    runChezCode,
    startChezLive,
    endChezLive,
  )
where

import Data.Text (Text)
import YCHR.Internal.Compile.Pipeline (CompiledProgram, Error (..))
import YCHR.Run (PreparedQuery)

data Chez = Chez

data ChezFailure
  = ChezRuntime String
  | ChezBackend String
  deriving (Show, Eq)

startChez :: CompiledProgram -> IO (Either String Chez)
startChez _ =
  pure
    ( Left
        "the Chez REPL backend is not available in the MicroHs build"
    )

restartChez :: Chez -> CompiledProgram -> IO (Either String Chez)
restartChez _ _ =
  pure
    ( Left
        "the Chez REPL backend is not available in the MicroHs build"
    )

stopChez :: Chez -> IO ()
stopChez _ = pure ()

prepareChezCode ::
  Bool ->
  Bool ->
  PreparedQuery ->
  Either Error Text
prepareChezCode _ _ _ =
  Left
    ( RuntimeError
        "the Chez REPL backend is not available in the MicroHs build"
        []
    )

runChezCode :: Chez -> Text -> IO (Either ChezFailure ())
runChezCode _ _ =
  pure (Left (ChezBackend "the Chez REPL backend is not available in the MicroHs build"))

startChezLive :: Chez -> IO (Either ChezFailure ())
startChezLive _ =
  pure (Left (ChezBackend "the Chez REPL backend is not available in the MicroHs build"))

endChezLive :: Chez -> IO (Either ChezFailure ())
endChezLive _ =
  pure (Left (ChezBackend "the Chez REPL backend is not available in the MicroHs build"))
