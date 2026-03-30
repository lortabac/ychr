module Main where

import Control.Exception (SomeException, displayException, fromException, try)
import Control.Monad.IO.Class (liftIO)
import Data.List (isPrefixOf, nub)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Options.Applicative
import System.Console.Haskeline
import System.Directory (XdgDirectory (..), createDirectoryIfMissing, getXdgDirectory)
import System.Exit (exitFailure)
import System.FilePath (takeDirectory)
import YCHR.Display (displayMsg)
import YCHR.Parsed qualified as Parsed
import YCHR.EndToEnd (CompiledProgram (..), Error, compileFiles, compileModules, runProgramWithGoal, runProgramWithQuery)
import YCHR.Meta (metaHostCallRegistry)
import YCHR.Pretty (prettyBindings, prettyQueryResult)
import YCHR.Runtime.Interpreter (HostCallRegistry, baseHostCallRegistry)

data RunOpts = RunOpts
  { goal :: T.Text,
    showBindings :: Bool
  }

data Command
  = Repl [FilePath]
  | Run RunOpts [FilePath]

filesArg :: Parser [FilePath]
filesArg = many (argument str (metavar "FILES..."))

replParser :: Parser Command
replParser = Repl <$> filesArg

runParser :: Parser Command
runParser =
  Run
    <$> ( RunOpts
            <$> fmap T.pack (strOption (short 'g' <> metavar "GOAL" <> help "Goal to execute"))
            <*> switch (long "show-bindings" <> help "Print variable bindings")
        )
    <*> filesArg

commandParser :: Parser Command
commandParser =
  subparser
    ( command "repl" (info (replParser <**> helper) (progDesc "Start the interactive REPL (default)"))
        <> command "run" (info (runParser <**> helper) (progDesc "Compile and run a goal"))
    )
    <|> replParser

main :: IO ()
main = do
  cmd <- execParser (info (commandParser <**> helper) (fullDesc <> progDesc "CHR compiler"))
  case cmd of
    Repl files -> runRepl files
    Run opts files -> runGoal opts files

runRepl :: [FilePath] -> IO ()
runRepl files = do
  result <- case files of
    [] -> pure (compileModules True [])
    _ -> compileFiles True files
  case result of
    Left err -> do
      putStr (displayMsg err)
      exitFailure
    Right prog -> do
      histFile <- getXdgDirectory XdgData "ychr/history"
      createDirectoryIfMissing True (takeDirectory histFile)
      let CompiledProgram {exportMap = em} = prog
          constraintNames = nub [T.unpack n | (n, _) <- Map.keys em]
          completions = [":quit", ":recompile", ":help", ":list_files", ":list_modules", ":list_declarations"] ++ constraintNames
          completeFunc = completeWord Nothing " ," $ \prefix ->
            return $ map (\n -> (simpleCompletion n) {isFinished = False}) $ filter (isPrefixOf prefix) completions
          settings = (defaultSettings :: Settings IO) {historyFile = Just histFile, complete = completeFunc}
      runInputT settings (repl files prog)

repl :: [FilePath] -> CompiledProgram -> InputT IO ()
repl files prog = loop
  where
    showHelp = do
      outputStrLn "Commands:"
      outputStrLn "  :help, :h              Show this help message"
      outputStrLn "  :recompile, :r         Recompile the loaded files"
      outputStrLn "  :list_files            List the compiled files"
      outputStrLn "  :list_modules          List the compiled modules"
      outputStrLn "  :list_declarations     List visible declarations"
      outputStrLn "  :quit, :q              Exit the REPL"
      loop
    showFiles = do
      mapM_ outputStrLn files
      loop
    showDeclarations = do
      let decls = nub [(n, a) | (n, a) <- Map.keys prog.exportMap]
      mapM_ (\(n, a) -> outputStrLn (T.unpack n ++ "/" ++ show a)) decls
      loop
    showModules = do
      mapM_ (\(Parsed.Module {name = n}) -> outputStrLn (T.unpack n)) prog.allModules
      loop
    recompile = do
      result <- liftIO $ case files of
        [] -> pure (compileModules True [])
        _ -> compileFiles True files
      case result of
        Left err -> do
          outputStr (displayMsg err)
          loop
        Right prog' -> repl files prog'
    loop = do
      minput <- getInputLine "ychr> "
      case minput of
        Nothing -> return ()
        Just ":quit" -> return ()
        Just ":q" -> return ()
        Just ":recompile" -> recompile
        Just ":r" -> recompile
        Just ":help" -> showHelp
        Just ":h" -> showHelp
        Just ":list_files" -> showFiles
        Just ":list_modules" -> showModules
        Just ":list_declarations" -> showDeclarations
        Just "" -> loop
        Just line -> do
          outcome <-
            liftIO $
              try @SomeException $
                runProgramWithQuery prog hostCalls (T.pack line)
          case outcome of
            Left exc -> case fromException exc of
              Just err -> outputStr (displayMsg (err :: Error))
              Nothing -> outputStrLn ("Error: " ++ displayException exc)
            Right bindings -> do
              outputStr (prettyQueryResult bindings)
          loop

runGoal :: RunOpts -> [FilePath] -> IO ()
runGoal opts files = do
  result <- case files of
    [] -> pure (compileModules True [])
    _ -> compileFiles True files
  case result of
    Left err -> do
      putStr (displayMsg err)
      exitFailure
    Right prog -> do
      outcome <- try @SomeException $ runProgramWithGoal prog hostCalls opts.goal
      case outcome of
        Left exc -> do
          case fromException exc of
            Just err -> putStr (displayMsg (err :: Error))
            Nothing -> putStrLn ("Error: " ++ displayException exc)
          exitFailure
        Right (_, bindings) ->
          if opts.showBindings
            then putStr (prettyBindings bindings)
            else return ()

hostCalls :: HostCallRegistry
hostCalls = baseHostCallRegistry <> metaHostCallRegistry
