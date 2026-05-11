module Main where

import Control.Exception (SomeException, displayException, fromException, try)
import Control.Monad (unless, when)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Options.Applicative
import System.Directory (createDirectoryIfMissing)
import System.Exit (exitFailure)
import System.FilePath (takeDirectory, (</>))
import System.IO (hPutStr, stderr)
import YCHR.Backend.Scheme (generateScheme)
import YCHR.Backend.SchemeDriver (generateDriver)
import YCHR.Display (displayMsg)
import YCHR.Meta (metaHostCallRegistry)
import YCHR.Parser (parseConstraint)
import YCHR.Pretty (prettyBindings)
import YCHR.Rename (renameQueryArgs)
import YCHR.Repl qualified as Repl
import YCHR.Run
  ( CompiledProgram (..),
    Error (..),
    Warning (..),
    compileFiles,
    prepareGoal,
    resolveQueryConstraint,
    runPreparedGoal,
  )
import YCHR.Runtime.Interpreter (HostCallRegistry, baseHostCallRegistry)
import YCHR.TypeCheck (typeCheckProgram)
import YCHR.Types (Constraint (..))
import YCHR.VM.SExpr (VMProgram (..), serialize)

-- ---------------------------------------------------------------------------
-- Command-line options
-- ---------------------------------------------------------------------------

data RunOpts = RunOpts
  { goal :: T.Text,
    showBindings :: Bool,
    werror :: Bool
  }

data Target = TargetVM | TargetScheme

data CompileOpts = CompileOpts
  { outputDir :: FilePath,
    baseName :: Maybe String,
    target :: Target,
    werror :: Bool
  }

data GenDriverOpts = GenDriverOpts
  { gdGoal :: T.Text,
    werror :: Bool
  }

data ReplOpts = ReplOpts
  { quiet :: Bool,
    werror :: Bool
  }

data CheckOpts = CheckOpts
  { werror :: Bool
  }

data Command
  = Repl ReplOpts [FilePath]
  | Run RunOpts [FilePath]
  | Compile CompileOpts [FilePath]
  | GenDriver GenDriverOpts [FilePath]
  | Check CheckOpts [FilePath]

filesArg :: Parser [FilePath]
filesArg = many (argument str (metavar "FILES..."))

werrorFlag :: Parser Bool
werrorFlag = switch (long "Werror" <> help "Treat warnings as errors")

replParser :: Parser Command
replParser =
  Repl
    <$> ( ReplOpts
            <$> switch (long "quiet" <> help "Suppress prompt and warnings")
            <*> werrorFlag
        )
    <*> filesArg

runParser :: Parser Command
runParser =
  Run
    <$> ( RunOpts
            <$> fmap T.pack (strOption (short 'g' <> metavar "GOAL" <> help "Goal to execute"))
            <*> switch (long "show-bindings" <> help "Print variable bindings")
            <*> werrorFlag
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
            <$> strOption
              ( long "output-dir"
                  <> short 'd'
                  <> metavar "DIR"
                  <> help "Output directory"
                  <> value "."
              )
            <*> optional
              ( strOption
                  ( short 'n'
                      <> long "base-name"
                      <> metavar "NAME"
                      <> help "Base name for generated files (default: program)"
                  )
              )
            <*> option
              targetReader
              ( short 't'
                  <> metavar "TARGET"
                  <> help "Target (vm, scheme)"
                  <> value TargetVM
              )
            <*> werrorFlag
        )
    <*> filesArg

genDriverParser :: Parser Command
genDriverParser =
  GenDriver
    <$> ( GenDriverOpts
            <$> fmap T.pack (strOption (short 'g' <> metavar "GOAL" <> help "Goal to execute"))
            <*> werrorFlag
        )
    <*> filesArg

checkParser :: Parser Command
checkParser = Check <$> (CheckOpts <$> werrorFlag) <*> filesArg

commandParser :: Parser Command
commandParser =
  subparser
    ( command
        "repl"
        ( info
            (replParser <**> helper)
            ( progDesc
                "Start the interactive REPL (default)"
            )
        )
        <> command "run" (info (runParser <**> helper) (progDesc "Compile and run a goal"))
        <> command
          "compile"
          ( info
              (compileParser <**> helper)
              ( progDesc
                  "Compile to a target format"
              )
          )
        <> command
          "gen-driver"
          ( info
              (genDriverParser <**> helper)
              ( progDesc
                  "Generate a Scheme driver script for a goal"
              )
          )
        <> command "check" (info (checkParser <**> helper) (progDesc "Type-check the program"))
    )
    <|> replParser

main :: IO ()
main = do
  cmd <- execParser (info (commandParser <**> helper) (fullDesc <> progDesc "CHR compiler"))
  case cmd of
    Repl opts files -> Repl.runRepl hostCalls opts.quiet opts.werror files
    Run opts files -> runGoal opts files
    Compile opts files -> runCompile opts files
    GenDriver opts files -> runGenDriver opts files
    Check opts files -> runCheck opts files

-- ---------------------------------------------------------------------------
-- Subcommands
-- ---------------------------------------------------------------------------

runGoal :: RunOpts -> [FilePath] -> IO ()
runGoal opts files = withCompiled False files $ \prog warnings -> do
  printWarnings warnings
  typeCheckOrExit prog
  prepResult <- try @SomeException (prepareGoal prog opts.goal)
  case prepResult of
    Left exc -> reportErrorAndExit exc
    Right (constraint, goalWarnings) -> do
      printWarnings goalWarnings
      exitOnWerror opts.werror (warnings ++ goalWarnings)
      outcome <- try @SomeException (runPreparedGoal prog hostCalls constraint)
      case outcome of
        Left exc -> reportErrorAndExit exc
        Right (_, bindings) ->
          when opts.showBindings (putStr (prettyBindings bindings))
  where
    reportErrorAndExit exc = do
      case fromException exc of
        Just err -> putStr (displayMsg (err :: Error))
        Nothing -> putStrLn ("Error: " ++ displayException exc)
      exitFailure

runCompile :: CompileOpts -> [FilePath] -> IO ()
runCompile opts files = withCompiled False files $ \prog warnings -> do
  printWarnings warnings
  typeCheckOrExit prog
  exitOnWerror opts.werror warnings
  let vmp =
        VMProgram
          { program = prog.program,
            exportedSet = prog.exportedSet,
            symbolTable = prog.symbolTable
          }
      name = maybe (T.pack "program") T.pack opts.baseName
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
runGenDriver opts files = withCompiled False files $ \prog warnings -> do
  printWarnings warnings
  typeCheckOrExit prog
  Constraint cname cargs <- case parseConstraint "<query>" opts.gdGoal of
    Left err -> do
      putStr (displayMsg (ParseError "<query>" err))
      exitFailure
    Right (Left validErr) -> do
      putStr (displayMsg (ParseValidationErrors [validErr]))
      exitFailure
    Right (Right c) -> pure c
  -- Canonicalize bare data-constructor references in the goal's
  -- arguments so they reach the runtime in the same flat-functor
  -- form the compiled head patterns expect.
  (renamedArgs, goalWarnings) <- case renameQueryArgs prog.allModules cargs of
    Left errs -> do
      putStr (displayMsg (RenameErrors errs))
      exitFailure
    Right (rs, ws) -> do
      let gws = [RenameWarnings ws | not (null ws)]
      printWarnings gws
      pure (rs, gws)
  resolved <- case resolveQueryConstraint prog (Constraint cname renamedArgs) of
    Left err -> do
      putStrLn err
      exitFailure
    Right c -> pure c
  -- Combine file-level and goal-level warnings into a single Werror
  -- decision so a single run reports every warning before exiting.
  exitOnWerror opts.werror (warnings ++ goalWarnings)
  TIO.putStr (generateDriver (T.pack "program") resolved)

runCheck :: CheckOpts -> [FilePath] -> IO ()
runCheck opts files = withCompiled False files $ \prog warnings -> do
  printWarnings warnings
  typeCheckOrExit prog
  exitOnWerror opts.werror warnings

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

-- | Compile @files@ (or an empty program if @files@ is empty) and
-- pass the resulting 'CompiledProgram' and warnings to the
-- continuation. On compilation failure, print the diagnostic to
-- stdout and exit non-zero — the continuation does not run.
withCompiled :: Bool -> [FilePath] -> (CompiledProgram -> [Warning] -> IO ()) -> IO ()
withCompiled stdlib files k = do
  result <- compileFiles stdlib files
  case result of
    Left err -> do
      putStr (displayMsg err)
      exitFailure
    Right (prog, warnings) -> k prog warnings

-- | Type-check the compiled program. If errors are found, print them
-- to stderr and exit non-zero; otherwise return cleanly.
typeCheckOrExit :: CompiledProgram -> IO ()
typeCheckOrExit prog = do
  errs <- typeCheckProgram prog.desugaredProgram
  unless (null errs) $ do
    mapM_ (hPutStr stderr . displayMsg) errs
    exitFailure

printWarnings :: [Warning] -> IO ()
printWarnings = mapM_ (hPutStr stderr . displayMsg)

exitOnWerror :: Bool -> [Warning] -> IO ()
exitOnWerror enabled ws = when (enabled && not (null ws)) exitFailure

hostCalls :: HostCallRegistry
hostCalls = baseHostCallRegistry <> metaHostCallRegistry
