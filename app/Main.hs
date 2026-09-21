module Main where

-- 'try' comes from the shim so its type variables keep GHC's order
-- (dev-docs/MICROHS_GAPS.md, gap 7).
import Control.Exception.Shim (SomeException, displayException, fromException, try)
import Control.Monad (unless, when)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Options.Applicative
import System.Directory (createDirectoryIfMissing)
import System.Exit (exitFailure)
import System.FilePath (takeDirectory, (</>))
import System.IO (hPutStr, stderr)
import YCHR.Embedded (stdlib, typeCheckerProgram)
import YCHR.Internal.Backend.Scheme (generateScheme, isValidSchemeIdentifier)
import YCHR.Internal.Backend.SchemeDriver (generateDriver)
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..))
import YCHR.Internal.Display (displayMsg)
import YCHR.Internal.Pretty (prettyBindings)
import YCHR.Internal.Repl qualified as Repl
import YCHR.Internal.Runtime.Interpreter (HostCallRegistry)
import YCHR.Internal.Runtime.Search (defaultHostCallRegistry)
import YCHR.Internal.TypeCheck (TypeCheckResult (..), typeCheckProgram)
import YCHR.Internal.VM.SExpr (VMProgram (..), serialize)
import YCHR.Run
  ( Error (..),
    Warning (..),
    compileFiles,
    prepareGoal,
    resolveQueryTellOrThrow,
    runPreparedGoal,
  )

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
    Repl opts files ->
      Repl.runRepl stdlib typeCheckerProgram hostCalls opts.quiet opts.werror files
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
  typeWarnings <- typeCheckOrExit prog
  prepResult <- try @SomeException (prepareGoal prog opts.goal)
  case prepResult of
    Left exc -> reportErrorAndExit exc
    Right (constraint, goalWarnings) -> do
      printWarnings goalWarnings
      exitOnWerror opts.werror (warnings ++ typeWarnings ++ goalWarnings)
      outcome <-
        try @SomeException (runPreparedGoal typeCheckerProgram prog hostCalls constraint)
      case outcome of
        Left exc -> reportErrorAndExit exc
        Right bindings ->
          when opts.showBindings (putStr (prettyBindings bindings))
  where
    reportErrorAndExit exc = do
      case fromException exc of
        Just err -> hPutStr stderr (displayMsg (err :: Error))
        Nothing -> hPutStr stderr ("Error: " ++ displayException exc ++ "\n")
      exitFailure

runCompile :: CompileOpts -> [FilePath] -> IO ()
runCompile opts files = withCompiled False files $ \prog warnings -> do
  printWarnings warnings
  typeWarnings <- typeCheckOrExit prog
  exitOnWerror opts.werror (warnings ++ typeWarnings)
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
      unless (isValidSchemeIdentifier name) $ do
        hPutStr
          stderr
          ( "Error: --base-name "
              ++ show (T.unpack name)
              ++ " is not a valid Scheme identifier; the Scheme target uses\n"
              ++ "       it as the library's final segment and as the exported\n"
              ++ "       program-info binding name.\n"
          )
        exitFailure
      let libName = [T.pack "ychr", T.pack "generated", name]
          outPath = opts.outputDir </> "ychr" </> "generated" </> T.unpack name ++ ".sls"
      createDirectoryIfMissing True (takeDirectory outPath)
      TIO.writeFile outPath (generateScheme libName vmp)
      putStrLn outPath
      schemeRuntimeNote

runGenDriver :: GenDriverOpts -> [FilePath] -> IO ()
runGenDriver opts files = withCompiled False files $ \prog warnings -> do
  printWarnings warnings
  typeWarnings <- typeCheckOrExit prog
  -- 'prepareGoal' parses the goal and canonicalizes bare
  -- data-constructor references in its arguments, so they reach the
  -- runtime in the same flat-functor form the compiled head patterns
  -- expect.
  prepResult <- try @SomeException (prepareGoal prog opts.gdGoal)
  (constraint, goalWarnings) <- case prepResult of
    Left e -> reportGenErrorAndExit e
    Right pair -> pure pair
  printWarnings goalWarnings
  outcome <- try @SomeException (resolveQueryTellOrThrow prog constraint)
  (qn, exprs) <- case outcome of
    Left e -> reportGenErrorAndExit e
    Right pair -> pure pair
  -- Combine file-level, type-check, and goal-level warnings into a
  -- single Werror decision so a single run reports every warning
  -- before exiting.
  exitOnWerror opts.werror (warnings ++ typeWarnings ++ goalWarnings)
  case generateDriver (T.pack "program") qn exprs of
    Left err -> do
      putStr (displayMsg err)
      exitFailure
    Right driver -> do
      TIO.putStr driver
      schemeRuntimeNote
  where
    reportGenErrorAndExit exc = do
      case fromException exc of
        Just err -> putStr (displayMsg (err :: Error))
        Nothing -> hPutStr stderr ("Error: " ++ displayException exc ++ "\n")
      exitFailure

runCheck :: CheckOpts -> [FilePath] -> IO ()
runCheck opts files = withCompiled False files $ \prog warnings -> do
  printWarnings warnings
  typeWarnings <- typeCheckOrExit prog
  exitOnWerror opts.werror (warnings ++ typeWarnings)

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

-- | Point at the Scheme runtime after emitting Scheme.
--
-- Generated code imports @(ychr runtime)@ and friends, which live in
-- @scheme\/@ in the YCHR source tree rather than in the installed
-- package — so an installed @ychr@ can emit Scheme it cannot itself run.
-- Written to stderr to keep stdout a clean list of generated paths (or,
-- for @gen-driver@, the driver source).
schemeRuntimeNote :: IO ()
schemeRuntimeNote =
  hPutStr stderr $
    "Note: the generated code imports the YCHR Scheme runtime\n"
      ++ "      ((ychr runtime) and friends). That runtime is not installed\n"
      ++ "      with this program; it lives in scheme/ in the YCHR source\n"
      ++ "      tree. Add that directory to your Scheme library path to run\n"
      ++ "      the output. See docs/how-to/scheme-repl.md.\n"

-- | Compile @files@ (or an empty program if @files@ is empty) and
-- pass the resulting 'CompiledProgram' and warnings to the
-- continuation. On compilation failure, print the diagnostic to
-- stdout and exit non-zero — the continuation does not run.
--
-- The 'Bool' is @includeStdlib@; 'stdlib' is the embedded standard
-- library supplied to every compile (see "YCHR.Embedded").
withCompiled :: Bool -> [FilePath] -> (CompiledProgram -> [Warning] -> IO ()) -> IO ()
withCompiled includeStdlib files k = do
  result <- compileFiles stdlib includeStdlib files
  case result of
    Left err -> do
      putStr (displayMsg err)
      exitFailure
    Right (prog, warnings) -> k prog warnings

-- | Type-check the compiled program with the embedded type-checker. If
-- errors are found, print them to stderr and exit non-zero. Otherwise
-- print the type-check warnings and return them, so the caller can
-- fold them into its @--Werror@ decision together with the compile-time
-- warnings.
typeCheckOrExit :: CompiledProgram -> IO [Warning]
typeCheckOrExit prog = do
  result <- typeCheckProgram typeCheckerProgram prog.desugaredProgram
  unless (null result.errors) $ do
    mapM_ (hPutStr stderr . displayMsg) result.errors
    exitFailure
  let ws = [TypeCheckWarnings result.warnings | not (null result.warnings)]
  printWarnings ws
  pure ws

printWarnings :: [Warning] -> IO ()
printWarnings = mapM_ (hPutStr stderr . displayMsg)

exitOnWerror :: Bool -> [Warning] -> IO ()
exitOnWerror enabled ws = when (enabled && not (null ws)) exitFailure

hostCalls :: HostCallRegistry
hostCalls = defaultHostCallRegistry
