module Main where

import Control.Exception (IOException, try)
import Control.Monad.IO.Class (liftIO)
import Data.Text qualified as T
import System.Console.Haskeline
import System.Directory (XdgDirectory (..), createDirectoryIfMissing, getXdgDirectory)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath (takeDirectory)
import YCHR.EndToEnd (CompiledProgram, compileFiles, compileModules, runProgramWithQuery)
import YCHR.Pretty (prettyQueryResult)
import YCHR.Meta (metaHostCallRegistry)
import YCHR.Runtime.Interpreter (baseHostCallRegistry)

main :: IO ()
main = do
  paths <- getArgs
  result <- case paths of
    [] -> pure (compileModules [])
    _ -> compileFiles paths
  case result of
    Left err -> do
      print err
      exitFailure
    Right prog -> do
      histFile <- getXdgDirectory XdgData "ychr/history"
      createDirectoryIfMissing True (takeDirectory histFile)
      let settings = defaultSettings {historyFile = Just histFile}
      runInputT settings (repl prog)

repl :: CompiledProgram -> InputT IO ()
repl prog = loop
  where
    loop = do
      minput <- getInputLine "?- "
      case minput of
        Nothing -> return ()
        Just ":quit" -> return ()
        Just ":q" -> return ()
        Just "" -> loop
        Just line -> do
          outcome <-
            liftIO $
              try @IOException $
                runProgramWithQuery prog (baseHostCallRegistry <> metaHostCallRegistry) (T.pack line)
          case outcome of
            Left err -> outputStrLn ("Error: " ++ show err)
            Right bindings -> do
              outputStr (prettyQueryResult bindings)
          loop
