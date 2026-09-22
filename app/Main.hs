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
import YCHR.Embedded (loadResources)
import YCHR.Internal.Backend.Scheme (generateScheme, isValidSchemeIdentifier)
import YCHR.Internal.Backend.SchemeDriver (generateDriver)
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..))
import YCHR.Internal.Display (displayMsg)
import YCHR.Internal.Pretty (prettyBindings)
import YCHR.Internal.Repl qualified as Repl
import YCHR.Internal.Resources (Resources (..))
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
    runGoalConstraint,
    runPreparedGoal,
  )

-- ---------------------------------------------------------------------------
-- Command-line options
-- ---------------------------------------------------------------------------

data RunOpts = RunOpts
  { goal :: T.Text,
    showBindings :: Bool,
    werror :: Bool,
    noCheck :: Bool
  }

data Target = TargetVM | TargetScheme

data CompileOpts = CompileOpts
  { outputDir :: FilePath,
    baseName :: Maybe String,
    target :: Target,
    werror :: Bool,
    noCheck :: Bool
  }

data GenDriverOpts = GenDriverOpts
  { gdGoal :: T.Text,
    werror :: Bool,
    noCheck :: Bool
  }

data ReplOpts = ReplOpts
  { quiet :: Bool,
    werror :: Bool,
    noCheck :: Bool
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

-- | @--no-check@: skip the optional type checker entirely, both the
-- whole-program check and the per-goal \/ per-query check. Compilation
-- itself is unchanged — parse, rename, resolve and compile errors still
-- fail — and so is @--Werror@ over the warnings that remain.
noCheckFlag :: Parser Bool
noCheckFlag = switch (long "no-check" <> help "Skip type checking (program and goal checks)")

replParser :: Parser Command
replParser =
  Repl
    <$> ( ReplOpts
            <$> switch (long "quiet" <> help "Suppress prompt and warnings")
            <*> werrorFlag
            <*> noCheckFlag
        )
    <*> filesArg

runParser :: Parser Command
runParser =
  Run
    <$> ( RunOpts
            <$> fmap T.pack (strOption (short 'g' <> metavar "GOAL" <> help "Goal to execute"))
            <*> switch (long "show-bindings" <> help "Print variable bindings")
            <*> werrorFlag
            <*> noCheckFlag
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
            <*> noCheckFlag
        )
    <*> filesArg

genDriverParser :: Parser Command
genDriverParser =
  GenDriver
    <$> ( GenDriverOpts
            <$> fmap T.pack (strOption (short 'g' <> metavar "GOAL" <> help "Goal to execute"))
            <*> werrorFlag
            <*> noCheckFlag
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
  -- Parse before loading: '--help' and usage errors must not need a
  -- resource tree, which under MicroHs would otherwise fail a bare
  -- @ychr --help@ run from outside a YCHR source tree
  -- (dev-docs/MICROHS_GAPS.md, gap 5).
  --
  -- No 'fullDesc' modifier: it has been an effect-free modifier since
  -- optparse-applicative 0.8, and the post-0.19 source MicroHs builds
  -- from has dropped it (dev-docs/MICROHS_GAPS.md, gap 9).
  cmd <- execParser (info (commandParser <**> helper) (progDesc "CHR compiler"))
  resources <- loadResourcesOrExit
  case cmd of
    Repl opts files ->
      Repl.runRepl
        resources.stdlib
        (if opts.noCheck then Nothing else Just resources.typeCheckerProgram)
        hostCalls
        opts.quiet
        opts.werror
        files
    Run opts files -> runGoal resources opts files
    Compile opts files -> runCompile resources opts files
    GenDriver opts files -> runGenDriver resources opts files
    Check opts files -> runCheck resources opts files

-- | Load the two resources the CLI runs on. Under GHC they are the
-- values embedded at build time and this cannot fail; under MicroHs they
-- are read from disk once the command line has been parsed
-- (@dev-docs\/MICROHS_GAPS.md@, gap 5), so a misconfigured
-- 'YCHR_LIB_DIR' is reported here, before the command runs.
loadResourcesOrExit :: IO Resources
loadResourcesOrExit = do
  result <- loadResources
  case result of
    Left err -> do
      hPutStr stderr ("Error: " ++ T.unpack err ++ "\n")
      exitFailure
    Right resources -> pure resources

-- ---------------------------------------------------------------------------
-- Subcommands
-- ---------------------------------------------------------------------------

runGoal :: Resources -> RunOpts -> [FilePath] -> IO ()
runGoal resources opts files = withCompiled resources False files $ \prog warnings -> do
  printWarnings warnings
  typeWarnings <- typeCheckUnless opts.noCheck resources prog
  prepResult <- try @SomeException (prepareGoal prog opts.goal)
  case prepResult of
    Left exc -> reportErrorAndExit exc
    Right (constraint, goalWarnings) -> do
      printWarnings goalWarnings
      exitOnWerror opts.werror (warnings ++ typeWarnings ++ goalWarnings)
      -- Without the checker the goal runs through 'runGoalConstraint',
      -- the same unchecked entry point the library exposes; with it,
      -- 'runPreparedGoal' type-checks the goal first.
      outcome <-
        try @SomeException $
          if opts.noCheck
            then runGoalConstraint prog hostCalls constraint
            else runPreparedGoal resources.typeCheckerProgram prog hostCalls constraint
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

runCompile :: Resources -> CompileOpts -> [FilePath] -> IO ()
runCompile resources opts files = withCompiled resources False files $ \prog warnings -> do
  printWarnings warnings
  typeWarnings <- typeCheckUnless opts.noCheck resources prog
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

runGenDriver :: Resources -> GenDriverOpts -> [FilePath] -> IO ()
runGenDriver resources opts files = withCompiled resources False files $ \prog warnings -> do
  printWarnings warnings
  typeWarnings <- typeCheckUnless opts.noCheck resources prog
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

runCheck :: Resources -> CheckOpts -> [FilePath] -> IO ()
runCheck resources opts files = withCompiled resources False files $ \prog warnings -> do
  printWarnings warnings
  typeWarnings <- typeCheckOrExit resources prog
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
-- The 'Bool' is @includeStdlib@; 'resources' supplies the standard
-- library and the type-checker (see "YCHR.Embedded").
withCompiled ::
  Resources ->
  Bool ->
  [FilePath] ->
  (CompiledProgram -> [Warning] -> IO ()) ->
  IO ()
withCompiled resources includeStdlib files k = do
  result <- compileFiles resources.stdlib includeStdlib files
  case result of
    Left err -> do
      putStr (displayMsg err)
      exitFailure
    Right (prog, warnings) -> k prog warnings

-- | Type-check @prog@ and return the warnings to fold into the caller's
-- @--Werror@ decision, unless @--no-check@ was given — in which case the
-- checker does not run at all and there are no type warnings. The
-- @--no-check@ case still compiles and still reports compile warnings.
typeCheckUnless :: Bool -> Resources -> CompiledProgram -> IO [Warning]
typeCheckUnless noCheck resources prog
  | noCheck = pure []
  | otherwise = typeCheckOrExit resources prog

-- | Type-check the compiled program with the loaded type-checker. If
-- errors are found, print them to stderr and exit non-zero. Otherwise
-- print the type-check warnings and return them, so the caller can
-- fold them into its @--Werror@ decision together with the compile-time
-- warnings.
typeCheckOrExit :: Resources -> CompiledProgram -> IO [Warning]
typeCheckOrExit resources prog = do
  result <- typeCheckProgram resources.typeCheckerProgram prog.desugaredProgram
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
