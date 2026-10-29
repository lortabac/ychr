{-# LANGUAGE OverloadedStrings #-}

-- | The Chez Scheme process behind @--repl-backend=chez@.
--
-- A persistent Chez process runs @scheme\/ychr\/repl-server.scm@. Haskell
-- sends one generated query expression per line on the server's stdin and
-- reads one @YCHR-REPL-OK@ \/ @YCHR-REPL-ERR@ frame from its stderr. The
-- child's stdout is inherited, so query output and bindings go straight to
-- the REPL's stdout.
--
-- The generated library is always @(ychr generated repl)@: the server
-- imports it statically and its session thunk is @repl@.
module YCHR.Internal.Repl.Chez
  ( Chez,
    ChezFailure (..),
    startChez,
    restartChez,
    stopChez,
    prepareChezCode,
    runChezCode,
    startChezLive,
    endChezLive,
  )
where

import Control.Exception
  ( IOException,
    SomeException,
    displayException,
    onException,
    try,
  )
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Directory
  ( createDirectory,
    createDirectoryIfMissing,
    doesFileExist,
    findExecutable,
    getCurrentDirectory,
    getTemporaryDirectory,
    makeAbsolute,
    removeDirectoryRecursive,
    removeFile,
  )
import System.Environment (lookupEnv)
import System.FilePath (searchPathSeparator, (</>))
import System.IO
  ( BufferMode (LineBuffering),
    Handle,
    IOMode (WriteMode),
    hClose,
    hFlush,
    hIsEOF,
    hSetBuffering,
    hSetEncoding,
    openTempFile,
    stderr,
    utf8,
    withFile,
  )
import System.Process
  ( CreateProcess (..),
    ProcessHandle,
    StdStream (CreatePipe, Inherit),
    createProcess,
    proc,
    terminateProcess,
    waitForProcess,
  )
import YCHR.Internal.Backend.Scheme
  ( QueryPlan (..),
    generateQuery,
    generateScheme,
  )
import YCHR.Internal.Compile (compileQueryGoals)
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..), Error (..))
import YCHR.Internal.VM.SExpr (VMProgram (..))
import YCHR.Run (PreparedQuery (..))

-- | A running Chez server and its temporary library directory.
data Chez = Chez
  { chezInput :: Handle,
    chezProtocol :: Handle,
    chezProcess :: ProcessHandle,
    chezTempDir :: FilePath
  }

-- | Why a Chez operation failed.
data ChezFailure
  = -- | The query itself raised a CHR runtime error. Rendered as the
    -- usual @YCHR-60001@ diagnostic.
    ChezRuntime String
  | -- | The backend process could not be started, died, or could not be
    -- talked to. Rendered as a plain @Error:@.
    ChezBackend String
  deriving (Show, Eq)

readyMarker, okMarker, errMarker :: Text
readyMarker = "YCHR-REPL-READY"
okMarker = "YCHR-REPL-OK"
errMarker = "YCHR-REPL-ERR "

-- | The library name the server imports. The final segment is also the
-- exported session thunk the server calls @(repl)@.
libraryName :: [Text]
libraryName = ["ychr", "generated", "repl"]

-- | Start a Chez backend for @cp@, generating and loading its Scheme
-- library in a fresh temporary directory.
startChez :: CompiledProgram -> IO (Either String Chez)
startChez cp = do
  runtime <- findRuntimeDir
  case runtime of
    Left err -> pure (Left err)
    Right runtimeDir -> do
      schemeExe <- findSchemeCommand
      case schemeExe of
        Left err -> pure (Left err)
        Right exe -> do
          tempResult <- try @IOException createTempDir
          case tempResult of
            Left exc ->
              pure (Left ("cannot create a temporary directory: " ++ displayException exc))
            Right tmp -> do
              started <-
                try @IOException
                  ( do
                      writeLibrary tmp cp
                      spawnServer tmp runtimeDir exe
                  )
                  `onException` ignoreIO (removeDirectoryRecursive tmp)
              case started of
                Left exc -> do
                  ignoreIO (removeDirectoryRecursive tmp)
                  pure (Left ("cannot start the Chez backend: " ++ displayException exc))
                Right result -> case result of
                  Left err -> do
                    ignoreIO (removeDirectoryRecursive tmp)
                    pure (Left err)
                  Right chez -> pure (Right chez)

-- | Replace a backend with one for a new program. The new process is
-- started before the old one is stopped, so a failed restart leaves the
-- previous program usable.
restartChez :: Chez -> CompiledProgram -> IO (Either String Chez)
restartChez old cp = do
  result <- startChez cp
  case result of
    Left err -> pure (Left err)
    Right new -> stopChez old >> pure (Right new)

-- | Stop the server and remove its temporary directory. Safe to call on a
-- process that already exited, and never throws.
stopChez :: Chez -> IO ()
stopChez chez = do
  ignoreIO (hClose chez.chezInput)
  ignoreIO (terminateProcess chez.chezProcess)
  ignoreIO (waitForProcess chez.chezProcess)
  ignoreIO (hClose chez.chezProtocol)
  ignoreIO (removeDirectoryRecursive chez.chezTempDir)

-- | Compile a prepared query into the Scheme expression the server
-- evaluates. A compilation failure is a pre-execution error; the REPL
-- reports it like any other @CompileErrors@.
prepareChezCode ::
  Bool ->
  Bool ->
  PreparedQuery ->
  Either Error Text
prepareChezCode freshSession timed prep =
  case compileQueryGoals prep.liftedGoals of
    Left errs -> Left (CompileErrors errs)
    Right (vars, stmts) ->
      Right $
        generateQuery
          QueryPlan
            { queryVariables = vars,
              queryStatements = stmts,
              queryProcedures = prep.extraProcs,
              queryCallables = prep.extraCallables,
              queryTimed = timed,
              queryFreshSession = freshSession
            }

-- | Send one expression and wait for its frame.
runChezCode :: Chez -> Text -> IO (Either ChezFailure ())
runChezCode chez code = do
  written <- try @IOException $ do
    TIO.hPutStr chez.chezInput code
    TIO.hPutStr chez.chezInput "\n"
    hFlush chez.chezInput
  case written of
    Left exc ->
      pure (Left (ChezBackend ("cannot write to the Chez backend: " ++ displayException exc)))
    Right () -> awaitFrame chez

-- | Start a fresh live session in the running process.
startChezLive :: Chez -> IO (Either ChezFailure ())
startChezLive chez = runChezCode chez "(set! %s (fresh-session))"

-- | Discard the live session. Failures are ignored by the REPL: the
-- process may already be gone, and there is nothing useful to do about it
-- while leaving a live session.
endChezLive :: Chez -> IO (Either ChezFailure ())
endChezLive chez = runChezCode chez "(set! %s #f)"

-- ---------------------------------------------------------------------------
-- Startup
-- ---------------------------------------------------------------------------

-- | Locate the YCHR Scheme runtime. @YCHR_SCHEME_LIB_DIR@ wins; otherwise
-- @.\/scheme@ is used, which is the source-checkout layout.
findRuntimeDir :: IO (Either String FilePath)
findRuntimeDir = do
  result <- try @IOException findRuntimeDirRaw
  pure $ case result of
    Left exc ->
      Left ("cannot locate the YCHR Scheme runtime: " ++ displayException exc)
    Right runtime -> runtime

findRuntimeDirRaw :: IO (Either String FilePath)
findRuntimeDirRaw = do
  override <- lookupEnv "YCHR_SCHEME_LIB_DIR"
  case override of
    Just dir -> validateRuntime dir
    Nothing -> do
      cwd <- getCurrentDirectory
      let dir = cwd </> "scheme"
      ok <- validRuntime dir
      if ok
        then Right <$> makeAbsolute dir
        else
          pure $
            Left
              ( "cannot find the YCHR Scheme runtime. Set YCHR_SCHEME_LIB_DIR "
                  ++ "to a checkout's scheme/ directory, or run from the "
                  ++ "checkout root."
              )

validateRuntime :: FilePath -> IO (Either String FilePath)
validateRuntime dir = do
  ok <- validRuntime dir
  if ok
    then Right <$> makeAbsolute dir
    else
      pure $
        Left
          ( "YCHR_SCHEME_LIB_DIR does not name a YCHR Scheme runtime: "
              ++ dir
              ++ " (expected ychr/runtime.sls and ychr/repl-server.scm)."
          )

validRuntime :: FilePath -> IO Bool
validRuntime dir = do
  runtime <- doesFileExist (dir </> "ychr" </> "runtime.sls")
  server <- doesFileExist (dir </> "ychr" </> "repl-server.scm")
  pure (runtime && server)

-- | The Scheme implementation. The backend is Chez-specific, but the
-- command name is configurable for installations that call it something
-- other than @scheme@.
findSchemeCommand :: IO (Either String FilePath)
findSchemeCommand = do
  override <- lookupEnv "YCHR_SCHEME"
  let name = maybe "scheme" id override
      missing =
        Left
          ( "cannot find the Chez Scheme executable `"
              ++ name
              ++ "` on PATH (set YCHR_SCHEME to override)."
          )
  -- findExecutable reads PATH and throws when the variable is unset.
  found <- try @IOException (findExecutable name)
  pure $ case found of
    Left _ -> missing
    Right (Just path) -> Right path
    Right Nothing -> missing

createTempDir :: IO FilePath
createTempDir = do
  tmp <- getTemporaryDirectory
  (path, handle) <- openTempFile tmp "ychr-repl-"
  hClose handle
  removeFile path
  createDirectory path
  pure path

-- | Write the generated library where the Chez @--libdirs@ entry can see
-- it: @TMP\/ychr\/generated\/repl.sls@.
writeLibrary :: FilePath -> CompiledProgram -> IO ()
writeLibrary tmp cp = do
  let dir = tmp </> "ychr" </> "generated"
      path = dir </> "repl.sls"
      vmp =
        VMProgram
          { program = cp.program,
            exportedSet = cp.exportedSet,
            symbolTable = cp.symbolTable
          }
      code = generateScheme libraryName cp.symbolTable vmp cp.opTable
  createDirectoryIfMissing True dir
  withFile path WriteMode $ \handle -> do
    hSetEncoding handle utf8
    TIO.hPutStr handle code

-- | Start @scheme --quiet --libdirs ... server.scm@ and wait for its ready
-- marker.
spawnServer :: FilePath -> FilePath -> FilePath -> IO (Either String Chez)
spawnServer tmp runtimeDir exe = do
  let libDirs = runtimeDir ++ [searchPathSeparator] ++ tmp
      server = runtimeDir </> "ychr" </> "repl-server.scm"
      args =
        [ "--quiet",
          "--libdirs",
          libDirs,
          "--libexts",
          ".sls",
          server
        ]
  (Just hin, _, Just herr, ph) <-
    createProcess
      (proc exe args)
        { std_in = CreatePipe,
          std_out = Inherit,
          std_err = CreatePipe
        }
  let closeHandles = do
        ignoreIO (hClose hin)
        ignoreIO (terminateProcess ph)
        ignoreIO (waitForProcess ph)
        ignoreIO (hClose herr)
      setup = do
        hSetEncoding hin utf8
        hSetBuffering hin LineBuffering
        hSetEncoding herr utf8
        hSetBuffering herr LineBuffering
        ready <- awaitReady herr []
        case ready of
          Left err -> do
            closeHandles
            pure (Left err)
          Right () -> pure (Right (Chez hin herr ph tmp))
  setup `onException` closeHandles

awaitReady :: Handle -> [Text] -> IO (Either String ())
awaitReady handle seen = do
  mline <- readLineMaybe handle
  case mline of
    Nothing -> pure (Left (startupFailure seen))
    Just line
      | line == readyMarker -> pure (Right ())
      | Just rest <- T.stripPrefix errMarker line ->
          pure (Left (T.unpack (unescape rest)))
      | otherwise -> awaitReady handle (line : seen)

startupFailure :: [Text] -> String
startupFailure [] = "the Chez backend exited before it was ready"
startupFailure seen =
  "the Chez backend failed during startup:\n"
    ++ T.unpack (T.unlines (reverse seen))

-- ---------------------------------------------------------------------------
-- Protocol
-- ---------------------------------------------------------------------------

awaitFrame :: Chez -> IO (Either ChezFailure ())
awaitFrame chez = do
  mline <- readLineMaybe chez.chezProtocol
  case mline of
    Nothing ->
      pure
        ( Left
            ( ChezBackend
                "the Chez backend exited unexpectedly; run :recompile to restart it"
            )
        )
    Just line
      | line == okMarker -> pure (Right ())
      | line == readyMarker -> awaitFrame chez
      | Just rest <- T.stripPrefix errMarker line ->
          pure (Left (ChezRuntime (T.unpack (unescape rest))))
      | otherwise -> do
          -- Chez itself can write warnings to stderr. Keep them visible
          -- without confusing them with protocol frames.
          TIO.hPutStrLn stderr ("chez: " <> line)
          awaitFrame chez

readLineMaybe :: Handle -> IO (Maybe Text)
readLineMaybe handle = do
  result <- try @IOException $ do
    eof <- hIsEOF handle
    if eof then pure Nothing else Just <$> TIO.hGetLine handle
  case result of
    Left exc -> do
      -- A real read error is not a clean EOF. Keep the reason visible.
      TIO.hPutStrLn stderr ("chez: " <> T.pack (displayException exc))
      pure Nothing
    Right value -> pure value

-- | Undo 'escapeLine' in the server script.
unescape :: Text -> Text
unescape = go
  where
    go text = case T.uncons text of
      Nothing -> ""
      Just ('\\', rest) -> case T.uncons rest of
        Just ('n', more) -> T.cons '\n' (go more)
        Just ('r', more) -> T.cons '\r' (go more)
        Just ('\\', more) -> T.cons '\\' (go more)
        _ -> T.cons '\\' (go rest)
      Just (c, rest) -> T.cons c (go rest)

-- | Ignore an I\/O failure during cleanup.
ignoreIO :: IO a -> IO ()
ignoreIO action = do
  _ <- try @SomeException action
  pure ()
