-- | Line-input backend for the REPL, MicroHS build.
--
-- Bare-'getLine' fallback: no history, no tab completion. The twin
-- module under @src\/ghc\/YCHR\/LineInput.hs@ provides the
-- haskeline-backed implementation for GHC; the two are switched by
-- @if impl(...)@ blocks in @ychr.cabal@.
module YCHR.LineInput
  ( LineInputSettings (..),
    LineInput (..),
    mkLineInput,
  )
where

import Control.Exception (IOException, try)
import System.IO (hFlush, stdout)

-- | Configuration for a line-input session. Both fields are ignored
-- by this backend; they exist for source compatibility with the GHC
-- backend.
data LineInputSettings = LineInputSettings
  { historyFile :: Maybe FilePath,
    completionCandidates :: [String]
  }

-- | Read one line of input. 'Nothing' signals EOF (e.g. Ctrl-D).
newtype LineInput = LineInput
  { readLine :: String -> IO (Maybe String)
  }

mkLineInput :: LineInputSettings -> IO LineInput
mkLineInput _ = pure (LineInput {readLine = readOneLine})
  where
    readOneLine prompt = do
      putStr prompt
      hFlush stdout
      r <- try @IOException getLine
      pure $ case r of
        Left _ -> Nothing
        Right s -> Just s
