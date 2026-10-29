{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Interactive REPL for compiled CHR programs.
--
-- Owns all REPL UI: outer command loop (one-off queries plus colon
-- commands like @:list_declarations@), live-session loop (persistent
-- constraint store between queries, exit with @:end@), prompts, and
-- the help text. Line input (history, tab completion, EOF handling)
-- is delegated to 'YCHR.Internal.LineInput', whose implementation differs
-- between GHC (haskeline) and MicroHs (bare 'getLine').
--
-- 'runRepl' is the entry point; 'modulesText', 'declarationsText' and
-- 'infoText' are the pure renderings behind @:list_modules@,
-- @:list_declarations@ and @:info@. They are exported so the web
-- playground ('YCHR.Playground') prints the same output into its REPL
-- pane instead of growing a second, drifting implementation; the
-- terminal REPL is just @putStr@ of them.
module YCHR.Internal.Repl
  ( ReplBackend (..),
    ReplOptions (..),
    runRepl,
    modulesText,
    declarationsText,
    infoText,
  )
where

import Control.Exception
  ( IOException,
    SomeException,
    displayException,
    finally,
    fromException,
    try,
  )
import Control.Monad (unless, void, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask, runReaderT)
import Data.Char (isSpace)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.List (intercalate, sort, stripPrefix)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Numeric (showFFloat)
import System.CPUTime (getCPUTime)
import System.Exit (exitFailure)
import System.IO (hPutStr, hPutStrLn, stderr, stdout)
import YCHR.Internal.Collected (CollectedModule (..))
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..), ExportResolution (..))
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Display (Display (..), displayMsg, renderSplices)
import YCHR.Internal.LineInput (LineInput (..), LineInputSettings (..), mkLineInput)
import YCHR.Internal.PExpr qualified as P
import YCHR.Internal.Parsed qualified as Parsed
import YCHR.Internal.Parser (opTableEntries, parseTermWith)
import YCHR.Internal.Pretty
  ( DeclKind (..),
    declKindKeyword,
    prettyConstraintDecl,
    prettyFunctionDecl,
    prettyQualifiedName,
    prettyQueryResult,
    prettyTypeDecl,
    renderAtom,
  )
import YCHR.Internal.ProgramCheck
  ( ProgramCheck (..),
    constraintUseErrors,
    typeCheckReport,
  )
import YCHR.Internal.Repl.Chez
  ( Chez,
    ChezFailure (..),
    endChezLive,
    prepareChezCode,
    restartChez,
    runChezCode,
    startChez,
    startChezLive,
    stopChez,
  )
import YCHR.Internal.Runtime.Interpreter (HostCallRegistry)
import YCHR.Internal.Runtime.Monad (Chr)
import YCHR.Internal.Runtime.Session
  ( SessionInput,
    toSessionInput,
    withCHR,
    withCHRExtra,
    withCHRExtraTraced,
    withTraceHandler,
  )
import YCHR.Internal.Runtime.Trace (defaultTraceHandler)
import YCHR.Internal.StdLib (StdLib)
import YCHR.Internal.TypeCheck.Render (typeModule)
import YCHR.Internal.Types
  ( BoundSig,
    DataConstructor (..),
    Name (..),
    QualifiedName (..),
    Term (..),
    TypeDefinition (..),
    TypeExpr,
    typeConstructors,
  )
import YCHR.Internal.Types qualified as Types
import YCHR.Run
  ( Error (..),
    PreparedQuery (..),
    Warning (..),
    compileFiles,
    executePreparedQuery,
    prepareQuery,
    prepareQueryUnchecked,
  )

-- ---------------------------------------------------------------------------
-- Entry point
-- ---------------------------------------------------------------------------

-- | Which backend executes queries.
data ReplBackend
  = ReplBackendInterpreter
  | ReplBackendChez
  deriving (Eq, Show)

-- | What the REPL runs on, and the CLI flags it honours.
--
-- The 'StdLib' and the compiled type-checker are explicit inputs: the
-- @ychr@ library embeds nothing at compile time. The CLI passes the two
-- values its embedding component provides.
data ReplOptions = ReplOptions
  { stdlib :: StdLib,
    -- | The compiled type-checker. 'Nothing' under @--no-check@: the
    -- REPL then prints no type-check report, and prepares every query
    -- unchecked.
    typeChecker :: Maybe SessionInput,
    hostCalls :: HostCallRegistry,
    -- | @--quiet@: no prompts; skip warnings (unless fatal), the
    -- startup type-check report and the history notice.
    quiet :: Bool,
    -- | @--Werror@: warnings during the initial load abort startup;
    -- during @:recompile@ they keep the previous program loaded.
    werror :: Bool,
    -- | @--dump-splices@: print the declaration-macro splices to stderr
    -- on load and on @:recompile@.
    dumpSplices :: Bool,
    -- | The files to compile; empty means an empty program.
    files :: [FilePath],
    -- | @--repl-backend@: where queries execute.
    replBackend :: ReplBackend
  }

-- | Run the interactive REPL. Compiles the inputs, prints any warnings
-- and type errors to stderr, then enters the outer command loop. The
-- session continues until the user types @:quit@ or hits EOF.
runRepl :: ReplOptions -> IO ()
runRepl opts = do
  result <- compileFiles opts.stdlib True opts.files
  case result of
    Left err -> do
      putStr (displayMsg err)
      exitFailure
    Right (prog, warnings) -> do
      when opts.dumpSplices (hPutStr stderr (renderSplices prog.splices))
      let warnsFatal = opts.werror && not (null warnings)
      when (warnsFatal || not opts.quiet) (printWarnings warnings)
      when warnsFatal exitFailure
      unless opts.quiet (printTypeDiagnosticsWhen opts.typeChecker prog)
      let exported = exportedNames prog
      inputs <- mkReplInputs opts.quiet exported
      backend <- case opts.replBackend of
        ReplBackendInterpreter -> pure Nothing
        ReplBackendChez -> do
          started <- startChez prog
          case started of
            Left err -> do
              hPutStrLn stderr ("Error: " ++ err)
              exitFailure
            Right chez -> pure (Just chez)
      backendRef <- newIORef backend
      outerLoop opts inputs backendRef prog
        `finally` (readIORef backendRef >>= maybe (pure ()) stopChez)

-- | The line inputs of the outer loop and of a live session.
data ReplInputs = ReplInputs
  { outer :: LineInput,
    live :: LineInput
  }

-- | Build the outer and live line inputs, which share one history file.
-- If that file cannot be used — its parent directory is not creatable,
-- or the file itself is read-only, unreadable, or a directory — the
-- REPL starts in degraded mode with history disabled and says so once
-- on stderr instead of aborting startup. @--quiet@ drops the notice,
-- matching how it drops compile warnings. Tab completion, prompts and
-- the rest of the session are unaffected.
mkReplInputs :: Bool -> [String] -> IO ReplInputs
mkReplInputs quietMode exported = do
  attempt <-
    try @IOException $
      ReplInputs
        <$> withHistory (commandNames ++ exported)
        <*> withHistory (":end" : exported)
  case attempt of
    Right inputs -> pure inputs
    Left _ -> do
      unless quietMode (hPutStrLn stderr "REPL history not available")
      ReplInputs
        <$> withoutHistory (commandNames ++ exported)
        <*> withoutHistory (":end" : exported)
  where
    settings mhist cands =
      LineInputSettings {historyFile = mhist, completionCandidates = cands}
    withHistory = mkLineInput . settings (Just "ychr/history")
    withoutHistory = mkLineInput . settings Nothing

-- ---------------------------------------------------------------------------
-- Input normalization
-- ---------------------------------------------------------------------------

-- | Normalize one raw line of REPL input: drop a trailing @%@ line
-- comment, then trim trailing whitespace — the @\\r@ of a CRLF line
-- ending included.
--
-- The language lexer treats @%@ as a comment to end of line
-- (docs\/reference\/language.md), so files and the REPL must agree on
-- what a line means. The REPL reads raw lines and hands them straight
-- to the query parser, so normalizing here — in front of both the outer
-- loop and the live session — keeps the two in step. A comment-only
-- line collapses to @""@, which both dispatch paths already treat as a
-- no-op, and the trim turns CRLF into plain LF (a stray @\\r@ would
-- otherwise ride along into colon-command matching, so @:quit\\r@ would
-- miss @:quit@).
stripCommentAndCR :: String -> String
stripCommentAndCR = reverse . dropWhile isSpace . reverse . stripComment

-- | Drop everything from the first @%@ that starts a line comment.
-- A @%@ inside a double-quoted string or a quoted atom is literal and
-- kept, so 'stripComment' tracks those regions with the lexer's escape
-- rules: a backslash escapes the following character in both, and @''@
-- is a literal quote inside a quoted atom. An unterminated literal
-- stays in its region to the end of the line: the parser rejects that
-- line anyway, and keeping the @%@ is the less surprising failure.
stripComment :: String -> String
stripComment = go
  where
    go [] = []
    go ('%' : _) = []
    go ('"' : rest) = '"' : inDoubleQuoted rest
    go ('\'' : rest) = '\'' : inQuotedAtom rest
    go (c : rest) = c : go rest

    inDoubleQuoted [] = []
    inDoubleQuoted ('\\' : c : rest) = '\\' : c : inDoubleQuoted rest
    inDoubleQuoted ('"' : rest) = '"' : go rest
    inDoubleQuoted (c : rest) = c : inDoubleQuoted rest

    inQuotedAtom [] = []
    inQuotedAtom ('\'' : '\'' : rest) = '\'' : '\'' : inQuotedAtom rest
    inQuotedAtom ('\\' : c : rest) = '\\' : c : inQuotedAtom rest
    inQuotedAtom ('\'' : rest) = '\'' : go rest
    inQuotedAtom (c : rest) = c : inQuotedAtom rest

-- ---------------------------------------------------------------------------
-- Outer REPL loop
-- ---------------------------------------------------------------------------

outerLoop ::
  ReplOptions ->
  ReplInputs ->
  IORef (Maybe Chez) ->
  CompiledProgram ->
  IO ()
outerLoop opts inputs backendRef = go
  where
    prompt = if opts.quiet then "" else "ychr> "
    go prog = do
      minput <- inputs.outer.readLine prompt
      case minput of
        Nothing -> pure ()
        Just input -> dispatch prog input
    dispatch prog input = case stripCommentAndCR input of
      ":quit" -> pure ()
      ":q" -> pure ()
      ":help" -> showHelp *> go prog
      ":h" -> showHelp *> go prog
      ":recompile" -> recompile prog
      ":r" -> recompile prog
      ":list_files" -> showFiles opts.files *> go prog
      ":list_modules" -> showModules prog *> go prog
      ":list_declarations" -> showDeclarations prog *> go prog
      ":list_operators" -> showOperators prog *> go prog
      ":info" -> showInfoUsage *> go prog
      ":i" -> showInfoUsage *> go prog
      ":trace" -> showTraceUsage *> go prog
      ":time" -> showTimeUsage *> go prog
      ":begin" -> do
        backend <- readIORef backendRef
        runLiveSession opts inputs.live backend prog
        go prog
      "" -> go prog
      line
        | Just rest <- stripPrefix ":info " line -> showInfo prog rest *> go prog
        | Just rest <- stripPrefix ":i " line -> showInfo prog rest *> go prog
        | Just rest <- stripPrefix ":trace " line -> do
            backend <- readIORef backendRef
            runTracedQuery opts backend prog rest
            go prog
        | Just rest <- stripPrefix ":time " line -> do
            backend <- readIORef backendRef
            runTimedOuterQuery opts backend prog rest
            go prog
        | otherwise -> do
            backend <- readIORef backendRef
            runOuterQuery opts backend prog line
            go prog
    recompile prog = do
      result <- compileFiles opts.stdlib True opts.files
      case result of
        Left err -> putStr (displayMsg err) *> go prog
        Right (prog', warnings) -> do
          when opts.dumpSplices (hPutStr stderr (renderSplices prog'.splices))
          if opts.werror && not (null warnings)
            then do
              printWarnings warnings
              -- Surface type errors of the rejected program too, so the
              -- user sees the full diagnostic picture before deciding
              -- what to fix; the previous program stays loaded.
              printTypeDiagnosticsWhen opts.typeChecker prog'
              go prog
            else do
              printWarnings warnings
              printTypeDiagnosticsWhen opts.typeChecker prog'
              backend <- readIORef backendRef
              case backend of
                Nothing -> go prog'
                Just old -> do
                  restarted <- restartChez old prog'
                  case restarted of
                    Left err -> do
                      hPutStrLn
                        stderr
                        ("Error: cannot restart the Chez backend: " ++ err)
                      go prog
                    Right new -> do
                      writeIORef backendRef (Just new)
                      go prog'

-- | Run a one-off query in the outer REPL: parse, typecheck, execute
-- in a fresh CHR session. Distinct exception classes are surfaced
-- differently — 'Error' values via 'displayMsg', everything else as
-- @"Error: " ++ displayException@. Under @--Werror@, query-rename
-- warnings short-circuit before execution; the constraint store is
-- untouched (one-shot queries get a fresh store anyway).
runOuterQuery :: ReplOptions -> Maybe Chez -> CompiledProgram -> String -> IO ()
runOuterQuery = runOuterQueryWith False

-- | Like 'runOuterQuery', but as @:time@: print the query's execution
-- time before its result. With the interpreter backend the span is CPU
-- time spent running it, including the fresh session a one-shot query
-- builds, and excludes preparation (parse, rename, resolve, desugar,
-- type-check), so a query rejected before execution prints no timing
-- line. With the Chez backend the Chez process prints the line itself.
-- A runtime error still prints one, since execution started.
runTimedOuterQuery :: ReplOptions -> Maybe Chez -> CompiledProgram -> String -> IO ()
runTimedOuterQuery = runOuterQueryWith True

-- | 'runOuterQuery' or, when the 'Bool' is set, 'runTimedOuterQuery'.
runOuterQueryWith ::
  Bool ->
  ReplOptions ->
  Maybe Chez ->
  CompiledProgram ->
  String ->
  IO ()
runOuterQueryWith timed opts backend prog line = do
  prepResult <-
    try @SomeException $
      prepareQueryWith opts.typeChecker prog (T.pack line)
  case prepResult of
    Left exc -> reportQueryException exc
    Right prep -> do
      printWarnings prep.warnings
      unless (opts.werror && not (null prep.warnings)) $
        case backend of
          Nothing -> runInterpreter prep
          Just chez -> case prepareChezCode True timed prep of
            Left err -> putStr (displayMsg err)
            Right code ->
              runChezCode chez code >>= either reportChezFailure pure
  where
    runInterpreter prep = do
      start <- getCPUTime
      execResult <-
        try @SomeException $
          withCHRExtra
            (toSessionInput prog)
            opts.hostCalls
            prep.extraProcs
            prep.extraCallables
            (executePreparedQuery prep.liftedGoals)
      end <- getCPUTime
      when timed (putStrLn (formatElapsed (end - start)))
      case execResult of
        Left exc -> reportQueryException exc
        Right bindings -> putStr (prettyQueryResult bindings)

-- | Print a Chez backend failure. A runtime error goes to stdout like
-- the interpreter's; a transport or startup error is a CLI error.
reportChezFailure :: ChezFailure -> IO ()
reportChezFailure (ChezRuntime msg) = putStr (displayMsg (RuntimeError msg []))
reportChezFailure (ChezBackend msg) = hPutStrLn stderr ("Error: " ++ msg)

-- | Render a backend failure. Runtime errors use the same YCHR-60001
-- envelope as the interpreter; transport and startup errors are plain
-- CLI errors.
chezFailureText :: ChezFailure -> String
chezFailureText (ChezRuntime msg) = displayMsg (RuntimeError msg [])
chezFailureText (ChezBackend msg) = "Error: " ++ msg ++ "\n"

-- | Print an outer-loop query failure: an 'Error' through 'displayMsg',
-- anything else as @"Error: " ++ displayException@.
reportQueryException :: SomeException -> IO ()
reportQueryException exc = case fromException exc of
  Just err -> putStr (displayMsg (err :: Error))
  Nothing -> putStrLn ("Error: " ++ displayException exc)

-- | Render an elapsed CPU time, in picoseconds, as seconds with
-- microsecond resolution: @0.000123s@. Six decimals is the resolution
-- the REPL reports; a platform whose clock is finer has the extra
-- digits rounded away rather than shown.
formatElapsed :: Integer -> String
formatElapsed ps = "Time: " ++ showFFloat (Just 6) seconds "s"
  where
    seconds = fromIntegral ps / 1e12 :: Double

-- | Run a one-off query in the outer REPL with refined-operational-
-- semantics tracing enabled. Output is the trace stream only —
-- bindings are intentionally not printed, matching the documented
-- @:trace@ behaviour. To see bindings, re-run the goal without
-- @:trace@.
runTracedQuery :: ReplOptions -> Maybe Chez -> CompiledProgram -> String -> IO ()
runTracedQuery opts backend prog line = case backend of
  Just _ ->
    hPutStrLn stderr ":trace is not available with --repl-backend=chez"
  Nothing -> do
    prepResult <-
      try @SomeException $
        prepareQueryWith opts.typeChecker prog (T.pack line)
    case prepResult of
      Left exc -> reportQueryException exc
      Right prep -> do
        printWarnings prep.warnings
        unless (opts.werror && not (null prep.warnings)) $ do
          execResult <-
            try @SomeException $
              withCHRExtraTraced
                (toSessionInput prog)
                opts.hostCalls
                prep.extraProcs
                prep.extraCallables
                (defaultTraceHandler stdout)
                (executePreparedQuery prep.liftedGoals)
          case execResult of
            Left exc -> reportQueryException exc
            Right _ -> pure ()

showTraceUsage :: IO ()
showTraceUsage =
  putStrLn ":trace GOAL  -- run GOAL with refined-operational-semantics tracing"

showTimeUsage :: IO ()
showTimeUsage =
  putStrLn ":time GOAL  -- run GOAL and print its execution time in seconds"

-- ---------------------------------------------------------------------------
-- Live REPL session
-- ---------------------------------------------------------------------------

-- | Run an interactive live session. A single 'withCHR' call wraps
-- the whole session, so the constraint store, propagation history,
-- and reactivation queue persist across queries entered at the
-- @ychr live>@ prompt. The session ends when the user types @:end@,
-- hits EOF, or a runtime error aborts execution.
runLiveSession ::
  ReplOptions ->
  LineInput ->
  Maybe Chez ->
  CompiledProgram ->
  IO ()
runLiveSession opts liveInput backend cp = case backend of
  Nothing -> withCHR (toSessionInput cp) opts.hostCalls liveLoop
  Just chez -> runLiveSessionChez opts liveInput chez cp
  where
    prompt = if opts.quiet then "" else "ychr live> "
    liveLoop :: Chr ()
    liveLoop = do
      mline <- liftIO (liveInput.readLine prompt)
      case mline of
        Nothing -> pure ()
        Just line -> dispatch line
    dispatch line
      | stripped == ":end" = pure ()
      | T.null stripped = liveLoop
      | Just rest <- T.stripPrefix ":trace " stripped = do
          outcome <-
            withTraceHandler (defaultTraceHandler stdout) $
              handleLiveQuery opts cp False rest
          case outcome of
            QueryOk -> liveLoop
            QueryRecoverable msg -> do
              liftIO (hPutStr stderr msg)
              liveLoop
            QueryFatal msg -> liftIO $ do
              hPutStr stderr msg
              hPutStrLn stderr "live session aborted due to runtime error."
      | stripped == ":trace" = do
          liftIO showTraceUsage
          liveLoop
      | otherwise = do
          outcome <- handleLiveQuery opts cp True (T.pack line')
          case outcome of
            QueryOk -> liveLoop
            QueryRecoverable msg -> do
              liftIO (hPutStr stderr msg)
              liveLoop
            QueryFatal msg -> liftIO $ do
              hPutStr stderr msg
              hPutStrLn stderr "live session aborted due to runtime error."
      where
        line' = stripCommentAndCR line
        stripped = T.strip (T.pack line')

-- | The Chez live-session loop. The store lives in the child process, so
-- this loop is plain 'IO'; a single generated query runs per prompt line.
runLiveSessionChez ::
  ReplOptions ->
  LineInput ->
  Chez ->
  CompiledProgram ->
  IO ()
runLiveSessionChez opts liveInput chez cp = do
  started <- startChezLive chez
  case started of
    Left failure -> hPutStr stderr (chezFailureText failure)
    Right () -> liveLoop `finally` void (endChezLive chez)
  where
    prompt = if opts.quiet then "" else "ychr live> "
    liveLoop = do
      mline <- liveInput.readLine prompt
      case mline of
        Nothing -> pure ()
        Just line -> dispatch line
    dispatch line
      | stripped == ":end" = pure ()
      | T.null stripped = liveLoop
      | Just _ <- T.stripPrefix ":trace " stripped = do
          hPutStrLn stderr unsupportedTrace
          liveLoop
      | stripped == ":trace" = do
          hPutStrLn stderr unsupportedTrace
          liveLoop
      | otherwise = do
          outcome <- handleLiveQueryChez opts cp chez (T.pack line')
          case outcome of
            QueryOk -> liveLoop
            QueryRecoverable msg -> do
              hPutStr stderr msg
              liveLoop
            QueryFatal msg -> do
              hPutStr stderr msg
              hPutStrLn stderr "live session aborted due to runtime error."
      where
        line' = stripCommentAndCR line
        stripped = T.strip (T.pack line')
    unsupportedTrace = ":trace is not available with --repl-backend=chez"

-- | Outcome of executing a single live-session query.
data QueryOutcome
  = -- | Query ran to completion. The backend has printed the bindings
    -- that should be shown.
    QueryOk
  | -- | A pre-execution problem (parse, type, lambdas-rejected) that
    -- left the constraint store untouched. The session can continue.
    QueryRecoverable String
  | -- | A runtime exception thrown during goal execution. The store
    -- and bindings may be inconsistent; the live session must abort.
    QueryFatal String

-- | Classify a live-session exception: an 'Error' was raised before or
-- during preparation and is recoverable; anything else is fatal.
classifyLiveException :: SomeException -> QueryOutcome
classifyLiveException exc = case fromException exc :: Maybe Error of
  Just err -> QueryRecoverable (displayMsg err)
  Nothing -> QueryFatal (renderLiveFatal exc)

-- | A fatal exception is most often an 'Error' (e.g. a runtime error
-- escaping 'executePreparedQuery'); rendering through 'displayMsg'
-- gives the same nicely-formatted output the outer REPL produces.
-- Anything else falls back to 'displayException'.
renderLiveFatal :: SomeException -> String
renderLiveFatal exc = case fromException exc :: Maybe Error of
  Just err -> displayMsg err
  Nothing -> displayException exc ++ "\n"

-- | The diagnostic for a query that introduces a lambda into a live
-- session. Live sessions cannot grow the procedure map.
lambdaInLiveQuery :: D.Function -> String
lambdaInLiveQuery lam =
  let lamEqs = lam.equations :: [Parsed.AnnP D.Equation]
      -- One location/origin for the lambda: its first equation's
      -- annotation.
      (loc, origin) = case lamEqs of
        (Parsed.AnnP _ l o : _) -> (l, o)
        [] -> (Parsed.dummyLoc, P.Atom "")
   in displayMsg (LambdasInLiveQuery loc origin)

-- | Handle one query inside an existing interpreter live session. The
-- final 'Bool' says whether visible bindings should be printed; the
-- @:trace@ form passes 'False'.
handleLiveQuery ::
  ReplOptions ->
  CompiledProgram ->
  Bool ->
  Text ->
  Chr QueryOutcome
handleLiveQuery opts cp printResult src = do
  prepResult <-
    liftIO (try @SomeException (prepareQueryWith opts.typeChecker cp src))
  case prepResult of
    Left exc -> pure (classifyLiveException exc)
    Right prep -> do
      liftIO (printWarnings prep.warnings)
      if opts.werror && not (null prep.warnings)
        then pure (QueryRecoverable "")
        else case prep.queryLambdas of
          (lam : _) -> pure (QueryRecoverable (lambdaInLiveQuery lam))
          [] -> do
            env <- ask
            execResult <-
              liftIO $
                try @SomeException $
                  runReaderT (executePreparedQuery prep.liftedGoals) env
            case execResult of
              Left exc -> pure (QueryFatal (renderLiveFatal exc))
              Right bindings -> do
                when
                  printResult
                  (liftIO (putStr (prettyQueryResult bindings)))
                pure QueryOk

-- | 'handleLiveQuery' for a query that runs in the Chez process.
handleLiveQueryChez ::
  ReplOptions ->
  CompiledProgram ->
  Chez ->
  Text ->
  IO QueryOutcome
handleLiveQueryChez opts cp chez src = do
  prepResult <-
    try @SomeException (prepareQueryWith opts.typeChecker cp src)
  case prepResult of
    Left exc -> pure (classifyLiveException exc)
    Right prep -> do
      printWarnings prep.warnings
      if opts.werror && not (null prep.warnings)
        then pure (QueryRecoverable "")
        else case prep.queryLambdas of
          (lam : _) -> pure (QueryRecoverable (lambdaInLiveQuery lam))
          [] -> case prepareChezCode False False prep of
            Left err -> pure (QueryRecoverable (displayMsg err))
            Right code -> do
              result <- runChezCode chez code
              pure $ case result of
                Right () -> QueryOk
                Left (ChezRuntime msg) ->
                  QueryFatal (displayMsg (RuntimeError msg []))
                Left (ChezBackend msg) ->
                  QueryFatal ("Error: " ++ msg ++ "\n")

-- ---------------------------------------------------------------------------
-- Commands
-- ---------------------------------------------------------------------------

-- | A REPL colon-command. The names list is the command plus its
-- aliases; @description@ is the help text. This list is the single
-- source of truth for tab-completion and the @:help@ output.
data Command = Command
  { names :: [String],
    description :: String
  }

commands :: [Command]
commands =
  [ Command [":help", ":h"] "Show this help message",
    Command [":recompile", ":r"] "Recompile the loaded files",
    Command [":list_files"] "List the compiled files",
    Command [":list_modules"] "List the compiled modules",
    Command [":list_declarations"] "List visible declarations",
    Command [":list_operators"] "List defined operators",
    Command [":info", ":i"] "Show information about an identifier",
    Command [":trace"] "Run a goal with tracing (interpreter backend only)",
    Command [":time"] "Run a goal and print its execution time",
    Command [":begin"] "Start a live CHR session (end with :end)",
    Command [":quit", ":q"] "Exit the REPL"
  ]

commandNames :: [String]
commandNames = concatMap (\c -> c.names) commands

-- ---------------------------------------------------------------------------
-- Command handlers
-- ---------------------------------------------------------------------------

showHelp :: IO ()
showHelp = do
  putStrLn "Commands:"
  mapM_ (putStrLn . renderCommand) commands
  where
    -- Align descriptions at column 25.
    renderCommand c =
      let label = intercalate ", " c.names
          padding = replicate (max 1 (23 - length label)) ' '
       in "  " ++ label ++ padding ++ c.description

showFiles :: [FilePath] -> IO ()
showFiles = mapM_ putStrLn

showModules :: CompiledProgram -> IO ()
showModules prog = putStr (modulesText prog)

-- | @:list_modules@: one line per compiled module. Pure so the web
-- playground can render it into its REPL pane ('YCHR.Playground').
modulesText :: CompiledProgram -> String
modulesText prog =
  concatMap (\(CollectedModule {name = n}) -> T.unpack n ++ "\n") prog.allModules

showDeclarations :: CompiledProgram -> IO ()
showDeclarations prog = putStr (declarationsText prog)

-- | @:list_declarations@: one line per declaration, deduplicated. Pure
-- for the same reason as 'modulesText'.
declarationsText :: CompiledProgram -> String
declarationsText prog = concatMap (++ "\n") declLines
  where
    declLines = dedup entries
    entries =
      [ entry
      | m <- prog.allModules,
        Parsed.Ann d _ <- m.decls,
        entry <- case d of
          Parsed.ConstraintDecl
            Parsed.ConstraintDeclBody {name = n, arity = a} ->
              [("chr_constraint", m.name, n, a)]
          Parsed.FunctionDecl
            Parsed.FunctionDeclBody {name = n, arity = a, isOpen = o, kind = k} ->
              [(declKindKeyword (toDeclKind o k), m.name, n, a)]
          -- A qualified target is shown with its own module.
          Parsed.ExtendClassTypeDecl
            Parsed.ExtendClassTypeDeclBody {name = Qualified tm n, arity = a} ->
              [("extend_class_type", tm, n, a)]
          Parsed.ExtendClassTypeDecl
            Parsed.ExtendClassTypeDeclBody {name = Unqualified n, arity = a} ->
              [("extend_class_type", m.name, n, a)]
          _ -> []
      ]
    dedup = go Set.empty
      where
        go _ [] = []
        go seen (e@(kw, modName, n, a) : rest)
          | Set.member e seen = go seen rest
          | otherwise = renderDecl kw modName n a : go (Set.insert e seen) rest
    renderDecl kw modName name arity =
      ":- "
        ++ kw
        ++ " "
        ++ renderAtom modName
        ++ ":"
        ++ renderAtom name
        ++ "/"
        ++ show arity
        ++ "."

showOperators :: CompiledProgram -> IO ()
showOperators prog = mapM_ (putStrLn . renderOp) entries
  where
    entries =
      sort
        [ (fix, opTypeStr ty, name)
        | P.OpDecl fix ty name <- opTableEntries prog.opTable
        ]
    renderOp (fix, ty, name) =
      "op(" ++ show fix ++ ", " ++ ty ++ ", " ++ renderAtom name ++ ")"
    opTypeStr ty = case ty of
      P.Xfx -> "xfx"
      P.Xfy -> "xfy"
      P.Yfx -> "yfx"
      P.Fx -> "fx"
      P.Fy -> "fy"
      P.Xf -> "xf"
      P.Yf -> "yf"

-- ---------------------------------------------------------------------------
-- :info / :i — identifier inspection
-- ---------------------------------------------------------------------------

-- | Hard-coded set of names recognized as the type checker's base
-- types. These are the /source-level/ spellings — what a user types at
-- @:info@ and what @encode_ty@ (@typechecker\/walk.chr@) matches
-- on. The @ty@ constructors backing them carry a @ty_@ prefix that
-- never surfaces here; @displayTypeAtom@
-- ("YCHR.Internal.TypeCheck.Render") strips it on the way out.
builtinTypeNames :: [Text]
builtinTypeNames = ["int", "float", "string", "any"]

-- | The module qualifier @:info@ shows a built-in type under. No
-- module of the /user's/ program is ever spelled this way; the name is
-- the checker's own CHR module, which is where the type
-- representation really lives — hence the reuse of 'typeModule'
-- rather than a second literal. Pinned by @docs\/reference\/repl.md@
-- and @test\/repl\/test_repl.py@.
builtinTypeModule :: Text
builtinTypeModule = typeModule

showInfoUsage :: IO ()
showInfoUsage = putStrLn infoUsageText

-- | The @:info@ usage line, without its newline. Shared with
-- 'infoText', which appends one.
infoUsageText :: String
infoUsageText = "usage: :info <identifier>"

-- | The identifier @:info@ asks about: a bare or qualified name, and
-- an arity when one is given.
data InfoQuery = InfoQuery
  { name :: Either Text QualifiedName,
    arity :: Maybe Int
  }

-- | Parse the argument to @:info@. Accepts @name@, @name/arity@,
-- @mod:name@, or @mod:name/arity@. Returns 'Nothing' if the parse
-- fails or the resulting term is not a recognized identifier shape,
-- in which case 'showInfo' falls back to "unknown identifier".
parseInfoArg :: CompiledProgram -> Text -> Maybe InfoQuery
parseInfoArg prog raw = case parseTermWith prog.opTable "<:info>" raw of
  Left _ -> Nothing
  Right t -> termToInfoArg t

termToInfoArg :: Term -> Maybe InfoQuery
termToInfoArg = \case
  CompoundTerm (Unqualified "/") [headT, IntTerm a] -> do
    q <- termToInfoArg headT
    pure InfoQuery {name = q.name, arity = Just (fromInteger a)}
  CompoundTerm (Unqualified n) [] ->
    Just InfoQuery {name = Left n, arity = Nothing}
  CompoundTerm (Qualified m n) [] ->
    Just InfoQuery {name = Right (QualifiedName m n), arity = Nothing}
  _ -> Nothing

-- | One discovered fact about an identifier. The qualified name is
-- always attached so 'renderInfoEntry' does not need to re-derive it.
data InfoEntry
  = -- | The identifier is a constraint, with its argument types. These
    -- are always 'Just' here: the resolver gives an untyped constraint
    -- an @any@-filled signature.
    IEConstraint QualifiedName Int (Maybe [TypeExpr]) [BoundSig]
  | -- | The identifier is a function or class. The 'DeclKind' comes
    -- from the original 'Parsed.Declaration' in 'allModules'.
    IEFunction D.Function DeclKind
  | -- | The identifier is a user-declared type.
    IEType TypeDefinition
  | -- | The identifier is a data constructor of the carried type.
    IEDataCtor TypeDefinition DataConstructor
  | -- | The identifier is one of the four typechecker-module base
    -- types (@int@, @float@, @string@, @any@).
    IEBuiltinType QualifiedName
  | -- | The identifier exists at this arity but is exported by
    -- multiple modules; the user must qualify to disambiguate. The
    -- list of module names mirrors the @AmbiguousExport@ entry in
    -- 'CompiledProgram.exportMap'.
    IEAmbiguous Text Int [Text]
  deriving (Show)

-- | Look up every fact known about an identifier. Order matters: the
-- caller prints entries in the order returned, so the most specific
-- match is emitted first.
lookupInfo :: CompiledProgram -> Either Text QualifiedName -> Maybe Int -> [InfoEntry]
lookupInfo prog name mArity =
  let arityMatches a = maybe True (== a) mArity
   in case name of
        Right qn -> qualifiedLookup prog qn mArity
        Left n ->
          let builtinEntries =
                [ IEBuiltinType (QualifiedName builtinTypeModule n)
                | n `elem` builtinTypeNames,
                  arityMatches 0
                ]
              exportEntries =
                concatMap (resolveExportArity prog n) (matchingArities prog n mArity)
              typeEntries =
                [ IEType td
                | td <- prog.desugaredProgram.typeDefinitions,
                  typeBaseName td == n,
                  arityMatches (length td.typeVars)
                ]
              ctorEntries =
                [ IEDataCtor td c
                | td <- prog.desugaredProgram.typeDefinitions,
                  c <- typeConstructors td,
                  ctorBaseName c == n,
                  arityMatches (length c.conArgs),
                  isCtorExportedByParent prog td c
                ]
           in builtinEntries ++ exportEntries ++ typeEntries ++ ctorEntries

-- | Arities to inspect for an unqualified name. When the user supplied
-- an arity, only that one is returned; otherwise every arity present
-- in 'exportMap' under this name is returned (in ascending order so
-- output is deterministic).
matchingArities :: CompiledProgram -> Text -> Maybe Int -> [Int]
matchingArities prog n = \case
  Just a -> [a | Map.member (Types.UnqualifiedIdentifier n a) prog.exportMap]
  Nothing ->
    sort
      [ a
      | Types.UnqualifiedIdentifier n' a <- Map.keys prog.exportMap,
        n' == n
      ]

-- | Resolve an unqualified name at a specific arity through 'exportMap'.
-- An unambiguous match dispatches to 'classifyQualified'; an ambiguous
-- one becomes a single 'IEAmbiguous' entry that the user must clear
-- by qualifying.
resolveExportArity :: CompiledProgram -> Text -> Int -> [InfoEntry]
resolveExportArity prog n a =
  case Map.lookup (Types.UnqualifiedIdentifier n a) prog.exportMap of
    Nothing -> []
    Just (UniqueExport qn) -> classifyQualified prog qn a
    Just (AmbiguousExport ms) -> [IEAmbiguous n a ms]

-- | Look up a qualified name directly in the compiled program. No
-- 'exportMap' traversal because the user has already disambiguated.
-- Types and constructors are matched regardless of arity when the user
-- omitted it (matching the behavior of the unqualified path).
qualifiedLookup :: CompiledProgram -> QualifiedName -> Maybe Int -> [InfoEntry]
qualifiedLookup prog qn mArity =
  let arityMatches a = maybe True (== a) mArity
      classifyAt = case mArity of
        Just a -> classifyQualified prog qn a
        Nothing ->
          -- Without an arity, scan every arity the program declares
          -- for this qualified name across constraints/functions.
          let cTyArities =
                [ key.arity
                | key <- Map.keys prog.desugaredProgram.constraintTypes,
                  key.name == qn
                ]
              fArities =
                [f.arity | f <- prog.desugaredProgram.functions, f.name == qn]
              exportArities =
                [ a
                | Types.QualifiedIdentifier m n a <- Set.toAscList prog.exportedSet,
                  m == qn.moduleName && n == qn.baseName
                ]
              allArities =
                sort
                  ( Set.toAscList
                      (Set.fromList (cTyArities ++ fArities ++ exportArities))
                  )
           in concatMap (classifyQualified prog qn) allArities
      typeEntries =
        [ IEType td
        | td <- prog.desugaredProgram.typeDefinitions,
          typeMatchesQN td qn,
          arityMatches (length td.typeVars)
        ]
      ctorEntries =
        [ IEDataCtor td c
        | td <- prog.desugaredProgram.typeDefinitions,
          c <- typeConstructors td,
          ctorMatchesQN c qn,
          arityMatches (length c.conArgs),
          isCtorExportedByParent prog td c
        ]
      builtinEntries =
        [ IEBuiltinType qn
        | qn.moduleName == builtinTypeModule,
          qn.baseName `elem` builtinTypeNames,
          arityMatches 0
        ]
   in builtinEntries ++ classifyAt ++ typeEntries ++ ctorEntries

-- | Decide what kind of declaration a @(qn, arity)@ pair refers to.
-- Priority: function over constraint — an identifier cannot be both
-- at the same arity (the resolver rejects that as
-- @ConstraintFunctionCollision@). Every declared constraint, typed
-- or not, lives in 'constraintTypes' (untyped constraints have an
-- @any@-filled signature synthesized by the resolver), so a single
-- lookup there covers both forms.
classifyQualified :: CompiledProgram -> QualifiedName -> Int -> [InfoEntry]
classifyQualified prog qn arity =
  case [f | f <- prog.desugaredProgram.functions, f.name == qn, f.arity == arity] of
    (f : _) -> [IEFunction f (functionDeclKind prog qn arity)]
    [] ->
      let key = Types.ConstraintKey qn arity
       in case Map.lookup key prog.desugaredProgram.constraintTypes of
            Just args ->
              let bs =
                    Map.findWithDefault
                      []
                      key
                      prog.desugaredProgram.constraintBounds
               in [IEConstraint qn arity (Just args) bs]
            Nothing -> []

-- | Recover the @function@ / @open_function@ / @class@ / @open_class@
-- keyword for a 'D.Function' by scanning every parsed module's
-- declarations. Returns the first matching 'Parsed.FunctionDecl' (in
-- 'allModules' iteration order); defaults to 'DKFunction' if none is
-- found, which only happens for synthetic declarations like lifted
-- lambdas (@__lambda_N@) that users would not normally inspect.
functionDeclKind :: CompiledProgram -> QualifiedName -> Int -> DeclKind
functionDeclKind prog qn arity =
  let matches =
        [ toDeclKind fd.isOpen fd.kind
        | m <- prog.allModules,
          m.name == qn.moduleName,
          Parsed.Ann d _ <- m.decls,
          Parsed.FunctionDecl fd <- [d],
          fd.name == qn.baseName,
          fd.arity == arity
        ]
   in case matches of
        (k : _) -> k
        [] -> DKFunction

-- | The declaration kind of a parsed function declaration, from its
-- open flag and its parsed kind.
toDeclKind :: Bool -> Parsed.FunctionDeclKind -> DeclKind
toDeclKind False Parsed.DKFunction = DKFunction
toDeclKind True Parsed.DKFunction = DKOpenFunction
toDeclKind False Parsed.DKClass = DKClass
toDeclKind True Parsed.DKClass = DKOpenClass

-- The renamer guarantees that 'TypeDefinition.name' and
-- 'DataConstructor.conName' are always 'Qualified' once resolution
-- completes (see 'renameDataConstructor' and 'renameTypeDefinition'
-- in "YCHR.Internal.Rename"). The 'Unqualified' arms below are defensive
-- fallbacks that compare on the base name only; they should never
-- fire in a well-formed compiled program.

typeBaseName :: TypeDefinition -> Text
typeBaseName td = case td.name of
  Unqualified n -> n
  Qualified _ n -> n

ctorBaseName :: DataConstructor -> Text
ctorBaseName c = case c.conName of
  Unqualified n -> n
  Qualified _ n -> n

typeMatchesQN :: TypeDefinition -> QualifiedName -> Bool
typeMatchesQN td qn = case td.name of
  Qualified m n -> m == qn.moduleName && n == qn.baseName
  Unqualified _ -> False

ctorMatchesQN :: DataConstructor -> QualifiedName -> Bool
ctorMatchesQN c qn = case c.conName of
  Qualified m n -> m == qn.moduleName && n == qn.baseName
  Unqualified _ -> False

-- | Is the given data constructor visible through its parent type's
-- module export list? @:info@ uses this to refuse direct queries on
-- hidden constructors while still listing them inside the parent
-- type's declaration body (when the user asks about the type or
-- another visible constructor of the same type).
--
-- The rule mirrors 'YCHR.Internal.Rename.exporterAllowance': a module with no
-- @:- module(_, [...])@ exports everything; an explicit
-- @type(T\/A)@ entry exports every constructor; @type(T\/A, [C1,
-- C2])@ exports only the listed names; and a type missing from the
-- export list exports no constructors at all.
isCtorExportedByParent ::
  CompiledProgram -> TypeDefinition -> DataConstructor -> Bool
isCtorExportedByParent prog td c =
  let tn = typeBaseName td
      ta = length td.typeVars
      cn = ctorBaseName c
      parentModule = case td.name of
        Qualified m _ -> Just m
        Unqualified _ -> Nothing
   in case parentModule >>= findModule prog of
        Nothing -> True
        Just m -> case m.exports of
          Nothing -> True
          Just (Parsed.AnnP exports _ _) ->
            case [ cs
                 | Parsed.TypeExportDecl
                     (Parsed.TypeExportDeclBody tn' ta' cs) <-
                     exports,
                   tn' == tn,
                   ta' == ta
                 ] of
              (Nothing : _) -> True
              (Just xs : _) -> cn `elem` xs
              [] -> False

findModule :: CompiledProgram -> Text -> Maybe CollectedModule
findModule prog modName =
  case [m | m <- prog.allModules, m.name == modName] of
    (m : _) -> Just m
    [] -> Nothing

-- | Print the result of an @:info@ query. The qualified name and the
-- declaration form are printed on consecutive lines for each match;
-- multiple matches are separated by blank lines. An empty result set
-- (no matches in any category) prints "unknown identifier: <raw>".
showInfo :: CompiledProgram -> String -> IO ()
showInfo prog raw = putStr (infoText prog raw)

-- | @:info@ rendered to a 'String'. Pure for the same reason as
-- 'modulesText': the web playground shows exactly what the terminal
-- REPL shows.
infoText :: CompiledProgram -> String -> String
infoText prog raw =
  let trimmed = T.strip (T.pack raw)
   in if T.null trimmed
        then infoUsageText ++ "\n"
        else case parseInfoArg prog trimmed of
          Nothing -> printUnknown (T.unpack trimmed)
          Just q ->
            case lookupInfo prog q.name q.arity of
              [] -> printUnknown (T.unpack trimmed)
              entries -> renderInfo entries
  where
    printUnknown s = "unknown identifier: " ++ s ++ "\n"

renderInfo :: [InfoEntry] -> String
renderInfo = intercalate "\n" . map renderInfoEntry

renderInfoEntry :: InfoEntry -> String
renderInfoEntry = \case
  IEBuiltinType qn ->
    prettyQualifiedName qn ++ "\nbuilt-in type\n"
  IEConstraint qn arity mArgs bounds ->
    prettyQualifiedName qn
      ++ "\n"
      ++ prettyConstraintDecl qn arity mArgs bounds
      ++ "\n"
  IEFunction f kind ->
    prettyQualifiedName f.name
      ++ "\n"
      ++ prettyFunctionDecl f kind
      ++ "\n"
  IEType td ->
    let qn = case td.name of
          Unqualified n -> QualifiedName "" n
          Qualified m n -> QualifiedName m n
     in prettyQualifiedName qn ++ "\n" ++ prettyTypeDecl td ++ "\n"
  IEDataCtor td c ->
    let qn = case c.conName of
          Unqualified n -> QualifiedName "" n
          Qualified m n -> QualifiedName m n
     in prettyQualifiedName qn ++ "\n" ++ prettyTypeDecl td ++ "\n"
  IEAmbiguous n arity ms ->
    "ambiguous identifier: "
      ++ T.unpack n
      ++ "/"
      ++ show arity
      ++ " is exported by "
      ++ intercalate ", " (map T.unpack ms)
      ++ "; qualify with mod:name to disambiguate\n"

-- ---------------------------------------------------------------------------
-- Reporting helpers
-- ---------------------------------------------------------------------------

-- | Sorted list of unqualified exported constraint names from a
-- compiled program. Used as completion candidates in both modes.
exportedNames :: CompiledProgram -> [String]
exportedNames prog =
  Set.toAscList . Set.fromList $
    [T.unpack n | Types.UnqualifiedIdentifier n _ <- Map.keys prog.exportMap]

printWarnings :: [Warning] -> IO ()
printWarnings = mapM_ (hPutStr stderr . displayMsg)

-- | Type-check the loaded program and print both its errors and its
-- warnings, together with any @:- constraint_use@ violations. Neither
-- aborts the REPL: type diagnostics are informational here, so
-- @--Werror@ (which governs the /compile/ warnings deciding whether a
-- program loads at all) does not consult them.
printTypeDiagnostics :: SessionInput -> CompiledProgram -> IO ()
printTypeDiagnostics typeChecker prog = do
  mapM_ (hPutStr stderr) (constraintUseErrors prog.desugaredProgram)
  report <- typeCheckReport typeChecker prog.desugaredProgram
  mapM_ (hPutStr stderr) report.errors
  printWarnings report.warnings

-- | 'printTypeDiagnostics' when a checker is available. The CLI's
-- @--no-check@ passes 'Nothing' and gets no report at all.
printTypeDiagnosticsWhen :: Maybe SessionInput -> CompiledProgram -> IO ()
printTypeDiagnosticsWhen Nothing _ = pure ()
printTypeDiagnosticsWhen (Just typeChecker) prog = printTypeDiagnostics typeChecker prog

-- | Prepare a query, type-checking its goals only when a checker is
-- available. @--no-check@ passes 'Nothing' here, so the query runs
-- through the unchecked preparation in "YCHR.Run" instead.
prepareQueryWith ::
  Maybe SessionInput ->
  CompiledProgram ->
  Text ->
  IO PreparedQuery
prepareQueryWith Nothing = prepareQueryUnchecked
prepareQueryWith (Just typeChecker) = prepareQuery typeChecker
