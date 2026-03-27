module Main where

import Control.Exception (SomeException, displayException, try)
import Control.Monad.IO.Class (liftIO)
import Data.List (isPrefixOf, nub)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import System.Console.Haskeline
import System.Directory (XdgDirectory (..), createDirectoryIfMissing, getXdgDirectory)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath (takeDirectory)
import YCHR.Display (displayMsg)
import YCHR.EndToEnd (CompiledProgram (..), compileFiles, compileModules, runProgramWithQuery)
import YCHR.Pretty (prettyQueryResult)
import YCHR.Meta (metaHostCallRegistry)
import YCHR.Runtime.Interpreter (baseHostCallRegistry)

main :: IO ()
main = do
  rawArgs <- getArgs
  let autoload = "--autoload" `elem` rawArgs
      paths = filter (/= "--autoload") rawArgs
  result <- case paths of
    [] -> pure (compileModules autoload [])
    _ -> compileFiles autoload paths
  case result of
    Left err -> do
      putStr (displayMsg err)
      exitFailure
    Right prog -> do
      histFile <- getXdgDirectory XdgData "ychr/history"
      createDirectoryIfMissing True (takeDirectory histFile)
      let CompiledProgram {exportMap = em} = prog
          constraintNames = nub [T.unpack n | (n, _) <- Map.keys em]
          completions = [":quit", ":q"] ++ constraintNames
          completeFunc = completeWord Nothing " ," $ \prefix ->
            return $ map (\n -> (simpleCompletion n) {isFinished = False}) $ filter (isPrefixOf prefix) completions
          settings = (defaultSettings :: Settings IO) {historyFile = Just histFile, complete = completeFunc}
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
              try @SomeException $
                runProgramWithQuery prog (baseHostCallRegistry <> metaHostCallRegistry) (T.pack line)
          case outcome of
            Left err -> outputStrLn ("Error: " ++ displayException err)
            Right bindings -> do
              outputStr (prettyQueryResult bindings)
          loop
