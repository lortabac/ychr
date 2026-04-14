module Main where

import Control.Exception (SomeException, displayException, fromException, try)
import Control.Monad (unless)
import Control.Monad.IO.Class (liftIO)
import Data.List (isPrefixOf, nub)
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Options.Applicative
import System.Console.Haskeline
import System.Directory (XdgDirectory (..), createDirectoryIfMissing, getXdgDirectory)
import System.Exit (exitFailure)
import System.FilePath (takeDirectory, (</>))
import System.IO (hPutStr, stderr)
import YCHR.Backend.Scheme (generateScheme)
import YCHR.Backend.SchemeDriver (generateDriver)
import YCHR.Display (Display (..), displayMsg)
import YCHR.Run (CompiledProgram (..), Error, Warning, compileFiles, compileModules, resolveQueryConstraint, runProgramWithGoal, runProgramWithQuery)
import YCHR.Meta (metaHostCallRegistry)
import YCHR.PExpr qualified as P
import YCHR.Parsed qualified as Parsed
import YCHR.Parser (opTableEntries, parseConstraint)
import YCHR.Pretty (prettyBindings, prettyQueryResult, renderAtom)
import YCHR.Runtime.Interpreter (HostCallRegistry, baseHostCallRegistry)
import YCHR.VM.SExpr (VMProgram (..), serialize)

data RunOpts = RunOpts
  { goal :: T.Text,
    showBindings :: Bool
  }

data Target = TargetVM | TargetScheme

data CompileOpts = CompileOpts
  { outputDir :: FilePath,
    baseName :: Maybe String,
    target :: Target
  }

data GenDriverOpts = GenDriverOpts
  { gdGoal :: T.Text
  }

data ReplOpts = ReplOpts
  { quiet :: Bool
  }

data Command
  = Repl ReplOpts [FilePath]
  | Run RunOpts [FilePath]
  | Compile CompileOpts [FilePath]
  | GenDriver GenDriverOpts [FilePath]

filesArg :: Parser [FilePath]
filesArg = many (argument str (metavar "FILES..."))

replParser :: Parser Command
replParser =
  Repl
    <$> (ReplOpts <$> switch (long "quiet" <> help "Suppress prompt and warnings"))
    <*> filesArg

runParser :: Parser Command
runParser =
  Run
    <$> ( RunOpts
            <$> fmap T.pack (strOption (short 'g' <> metavar "GOAL" <> help "Goal to execute"))
            <*> switch (long "show-bindings" <> help "Print variable bindings")
        )
    <*> filesArg

targetReader :: ReadM Target
targetReader = eitherReader $ \t -> case t of
  "vm" -> Right TargetVM
  "scheme" -> Right TargetScheme
  _ -> Left ("Unknown target: " ++ t ++ " (valid targets: vm, scheme)")

compileParser :: Parser Command
compileParser =
  Compile
    <$> ( CompileOpts
            <$> strOption (long "output-dir" <> short 'd' <> metavar "DIR" <> help "Output directory" <> value ".")
            <*> optional (strOption (short 'n' <> long "base-name" <> metavar "NAME" <> help "Base name for generated files (default: derived from module name)"))
            <*> option targetReader (short 't' <> metavar "TARGET" <> help "Target (vm, scheme)" <> value TargetVM)
        )
    <*> filesArg

genDriverParser :: Parser Command
genDriverParser =
  GenDriver
    <$> ( GenDriverOpts
            <$> fmap T.pack (strOption (short 'g' <> metavar "GOAL" <> help "Goal to execute"))
        )
    <*> filesArg

commandParser :: Parser Command
commandParser =
  subparser
    ( command "repl" (info (replParser <**> helper) (progDesc "Start the interactive REPL (default)"))
        <> command "run" (info (runParser <**> helper) (progDesc "Compile and run a goal"))
        <> command "compile" (info (compileParser <**> helper) (progDesc "Compile to a target format"))
        <> command "gen-driver" (info (genDriverParser <**> helper) (progDesc "Generate a Scheme driver script for a goal"))
    )
    <|> replParser

main :: IO ()
main = do
  cmd <- execParser (info (commandParser <**> helper) (fullDesc <> progDesc "CHR compiler"))
  case cmd of
    Repl opts files -> runRepl opts files
    Run opts files -> runGoal opts files
    Compile opts files -> runCompile opts files
    GenDriver opts files -> runGenDriver opts files

printWarnings :: [Warning] -> IO ()
printWarnings = mapM_ (\w -> hPutStr stderr (displayMsg w))

runRepl :: ReplOpts -> [FilePath] -> IO ()
runRepl opts files = do
  result <- case files of
    [] -> pure (compileModules True [])
    _ -> compileFiles True files
  case result of
    Left err -> do
      putStr (displayMsg err)
      exitFailure
    Right (prog, warnings) -> do
      unless opts.quiet $ printWarnings warnings
      histFile <- getXdgDirectory XdgData "ychr/history"
      createDirectoryIfMissing True (takeDirectory histFile)
      let CompiledProgram {exportMap = em} = prog
          constraintNames = nub [T.unpack n | (n, _) <- Map.keys em]
          completions = [":quit", ":recompile", ":help", ":list_files", ":list_modules", ":list_declarations", ":list_operators", "call"] ++ constraintNames
          completeFunc = completeWord Nothing " ," $ \prefix ->
            return $ map (\n -> (simpleCompletion n) {isFinished = False}) $ filter (isPrefixOf prefix) completions
          settings = (defaultSettings :: Settings IO) {historyFile = Just histFile, complete = completeFunc}
      runInputT settings (repl opts.quiet files prog)

repl :: Bool -> [FilePath] -> CompiledProgram -> InputT IO ()
repl quietMode files prog = loop
  where
    showHelp = do
      outputStrLn "Commands:"
      outputStrLn "  :help, :h              Show this help message"
      outputStrLn "  :recompile, :r         Recompile the loaded files"
      outputStrLn "  :list_files            List the compiled files"
      outputStrLn "  :list_modules          List the compiled modules"
      outputStrLn "  :list_declarations     List visible declarations"
      outputStrLn "  :list_operators        List defined operators"
      outputStrLn "  :quit, :q              Exit the REPL"
      loop
    showFiles = do
      mapM_ outputStrLn files
      loop
    showDeclarations = do
      let renderDecl kw modName name arity =
            ":- " ++ kw ++ " " ++ renderAtom modName ++ ":" ++ renderAtom name ++ "/" ++ show arity ++ "."
          declLines =
            [ renderDecl kw m.name n a
            | m <- prog.allModules,
              Parsed.Ann d _ <- m.decls,
              (kw, n, a) <- case d of
                Parsed.ConstraintDecl {name = n, arity = a} -> [("chr_constraint", n, a)]
                Parsed.FunctionDecl {name = n, arity = a} -> [("function", n, a)]
                _ -> []
            ]
      mapM_ outputStrLn declLines
      loop
    showOperators = do
      let opTypeStr P.Xfx = "xfx"
          opTypeStr P.Xfy = "xfy"
          opTypeStr P.Yfx = "yfx"
          opTypeStr P.Fx = "fx"
          opTypeStr P.Fy = "fy"
          opTypeStr P.Xf = "xf"
          opTypeStr P.Yf = "yf"
          entries = List.sort [(fix, opTypeStr ty, name) | (fix, ty, name) <- opTableEntries prog.opTable]
          renderOp (fix, ty, name) =
            "op(" ++ show fix ++ ", " ++ ty ++ ", " ++ renderAtom name ++ ")"
      mapM_ (outputStrLn . renderOp) entries
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
        Right (prog', warnings) -> do
          liftIO (printWarnings warnings)
          repl quietMode files prog'
    loop = do
      minput <- getInputLine (if quietMode then "" else "ychr> ")
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
        Just ":list_operators" -> showOperators
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
    Right (prog, warnings) -> do
      printWarnings warnings
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

runCompile :: CompileOpts -> [FilePath] -> IO ()
runCompile opts files = do
  let includeStdlib = case opts.target of
        TargetVM -> True
        TargetScheme -> False
  result <- case files of
    [] -> pure (compileModules includeStdlib [])
    _ -> compileFiles includeStdlib files
  case result of
    Left err -> do
      putStr (displayMsg err)
      exitFailure
    Right (prog, warnings) -> do
      printWarnings warnings
      let vmp = VMProgram {program = prog.program, exportedSet = prog.exportedSet, symbolTable = prog.symbolTable}
          -- Derive the base name from the first user module if not given
          stdlibNames = map T.pack ["builtins", "lists", "strings", "meta", "test"]
          userModules = [n | Parsed.Module {name = n} <- prog.allModules, n `notElem` stdlibNames]
          name = case opts.baseName of
            Just n -> T.pack n
            Nothing -> case userModules of
              (n : _) -> n
              [] -> T.pack "program"
      case opts.target of
        TargetVM -> do
          let outPath = opts.outputDir </> T.unpack name ++ ".vm"
          TIO.writeFile outPath (serialize vmp)
          putStrLn outPath
        TargetScheme -> do
          let libName = [T.pack "ychr", T.pack "generated", name]
              outPath = opts.outputDir </> "ychr" </> "generated" </> T.unpack name ++ ".sls"
          createDirectoryIfMissing True (takeDirectory outPath)
          TIO.writeFile outPath (generateScheme libName vmp)
          putStrLn outPath

runGenDriver :: GenDriverOpts -> [FilePath] -> IO ()
runGenDriver opts files = do
  result <- case files of
    [] -> pure (compileModules False [])
    _ -> compileFiles False files
  case result of
    Left err -> do
      putStr (displayMsg err)
      exitFailure
    Right (prog, warnings) -> do
      printWarnings warnings
      constraint <- case parseConstraint "<query>" opts.gdGoal of
        Left err -> do
          putStrLn (show err)
          exitFailure
        Right c -> pure c
      resolved <- case resolveQueryConstraint prog constraint of
        Left err -> do
          putStrLn err
          exitFailure
        Right c -> pure c
      let stdlibNames = map T.pack ["builtins", "lists", "strings", "meta", "test"]
          userModules = [n | Parsed.Module {name = n} <- prog.allModules, n `notElem` stdlibNames]
          name = case userModules of
            (n : _) -> n
            [] -> T.pack "program"
      TIO.putStr (generateDriver name resolved)

hostCalls :: HostCallRegistry
hostCalls = baseHostCallRegistry <> metaHostCallRegistry
