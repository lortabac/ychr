-- | Line-input backend for the REPL, GHC build.
--
-- Wraps @haskeline@: prompt + history file + tab completion. The
-- twin module under @src\/mhs\/YCHR\/LineInput.hs@ provides a
-- bare-'getLine' implementation for MicroHS; the two are switched by
-- @if impl(...)@ blocks in @ychr.cabal@.
module YCHR.LineInput
  ( LineInputSettings (..),
    LineInput (..),
    mkLineInput,
  )
where

import Data.List (isPrefixOf)
import System.Console.Haskeline
  ( Completion (isFinished),
    Settings (complete, historyFile),
    completeWord,
    defaultSettings,
    getInputLine,
    runInputT,
    simpleCompletion,
  )
import System.Console.Haskeline qualified as H
import System.Console.Haskeline.Completion (CompletionFunc)
import System.Directory (XdgDirectory (..), createDirectoryIfMissing, getXdgDirectory)
import System.FilePath (takeDirectory)

-- | Configuration for a line-input session.
--
-- The 'historyFile' field is interpreted as an XDG-data-relative
-- subpath (e.g. @\"ychr\/history\"@); the GHC backend resolves it via
-- 'getXdgDirectory' and creates the parent directory on demand. The
-- MicroHS backend ignores both fields.
data LineInputSettings = LineInputSettings
  { historyFile :: Maybe FilePath,
    completionCandidates :: [String]
  }

-- | Read one line of input. 'Nothing' signals EOF (e.g. Ctrl-D).
newtype LineInput = LineInput
  { readLine :: String -> IO (Maybe String)
  }

-- | Build a 'LineInput' from settings. Under haskeline @runInputT@ is
-- entered per 'readLine' call; the per-call cost (history file
-- re-read, signal handler re-install) is imperceptible at human
-- typing speed and keeps the API plain 'IO'.
mkLineInput :: LineInputSettings -> IO LineInput
mkLineInput s = do
  resolved <- traverse resolveHistoryPath s.historyFile
  let hSettings =
        (defaultSettings :: H.Settings IO)
          { historyFile = resolved,
            complete = matchAgainst s.completionCandidates
          }
  pure (LineInput {readLine = \prompt -> runInputT hSettings (getInputLine prompt)})

resolveHistoryPath :: FilePath -> IO FilePath
resolveHistoryPath sub = do
  path <- getXdgDirectory XdgData sub
  createDirectoryIfMissing True (takeDirectory path)
  pure path

-- | Build a haskeline completion function that prefix-matches against
-- a fixed list of candidates. Word boundaries are space and comma,
-- matching how a constraint conjunction is written. The
-- @isFinished = False@ flag suppresses the auto-appended space after
-- a completion, which matters when the user is part-way through a
-- conjunction.
matchAgainst :: [String] -> CompletionFunc IO
matchAgainst candidates =
  completeWord Nothing " ," $ \prefix ->
    pure
      [ (simpleCompletion n) {isFinished = False}
      | n <- candidates,
        prefix `isPrefixOf` n
      ]
