-- | Line-input backend for the REPL, GHC build.
--
-- Wraps @haskeline@: prompt + history file + tab completion. The
-- twin module under @src\/mhs\/YCHR\/LineInput.hs@ provides a
-- bare-'getLine' implementation for MicroHS; the two are switched by
-- @if impl(...)@ blocks in @ychr.cabal@.
module YCHR.Internal.LineInput
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
import System.IO (IOMode (AppendMode, ReadMode), withFile)

-- | Configuration for a line-input session.
--
-- The 'historyFile' field is interpreted as an XDG-data-relative
-- subpath (e.g. @\"ychr\/history\"@); the GHC backend resolves it via
-- 'getXdgDirectory', creates the parent directory on demand, and checks
-- that the file is usable (writable and readable). The MicroHS backend
-- ignores both fields.
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
--
-- Throws an 'IOException' when a requested history file cannot be made
-- usable: its parent directory is not creatable, the file is read-only
-- or unreadable, or the path is a directory. Callers that want a
-- history-less session in that case should catch it and rebuild the
-- settings with 'historyFile' set to 'Nothing'.
mkLineInput :: LineInputSettings -> IO LineInput
mkLineInput s = do
  resolved <- traverse resolveHistoryPath s.historyFile
  mapM_ ensureUsable resolved
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

-- | Check that the history file can be both written and read, so an
-- unusable path surfaces as an 'IOException' at startup rather than as
-- a silent failure inside haskeline, which ignores history read and
-- write errors. The append open creates the file when it is absent — the
-- same file haskeline would create on its first history write — and
-- never truncates an existing one.
ensureUsable :: FilePath -> IO ()
ensureUsable path = do
  withFile path AppendMode (const (pure ()))
  withFile path ReadMode (const (pure ()))

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
