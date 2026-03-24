module Main where

import Control.Exception (IOException, try)
import Control.Monad.IO.Class (liftIO)
import Data.List (intercalate)
import Data.Text qualified as T
import System.Console.Haskeline
import System.Directory (XdgDirectory (..), createDirectoryIfMissing, getXdgDirectory)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath (takeDirectory)
import YCHR.EndToEnd (CompiledProgram, compileFiles, runQuery)
import YCHR.Pretty (prettyBindings)
import YCHR.Runtime.Interpreter (defaultHostCallRegistry)
import YCHR.Runtime.Types (RuntimeVal (..), SuspensionId (..), Value (..))

main :: IO ()
main = do
  paths <- getArgs
  case paths of
    [] -> do
      putStrLn "Usage: ychr <file.chr> [<file.chr> ...]"
      exitFailure
    _ -> do
      result <- compileFiles paths
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
                runQuery prog defaultHostCallRegistry (T.pack line)
          case outcome of
            Left err -> outputStrLn ("Error: " ++ show err)
            Right (_, bindings) -> do
              outputStr (prettyBindings bindings)
          loop

prettyRuntimeVal :: RuntimeVal -> String
prettyRuntimeVal (RVal v) = prettyValue v
prettyRuntimeVal (RConstraint (SuspensionId n)) = "#" ++ show n

prettyValue :: Value -> String
prettyValue (VBool True) = "true"
prettyValue (VBool False) = "false"
prettyValue (VInt n) = show n
prettyValue (VAtom s) = s
prettyValue (VVar _) = "_"
prettyValue VWildcard = "_"
prettyValue (VTerm f args) =
  f ++ "(" ++ intercalate ", " (map prettyValue args) ++ ")"
