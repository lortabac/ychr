{-# LANGUAGE OverloadedStrings #-}

-- | Interactive REPL for compiled CHR programs.
--
-- Owns all REPL UI: outer command loop (one-off queries plus colon
-- commands like @:list_declarations@), live-session loop (persistent
-- constraint store between queries, exit with @:end@), haskeline
-- 'Settings' (history file, tab completions, prompts), and the help
-- text. Only 'runRepl' is exported; everything else is internal.
module YCHR.Repl
  ( runRepl,
  )
where

import Control.Exception (SomeException, displayException, fromException, try)
import Control.Monad (unless, when)
import Control.Monad.IO.Class (liftIO)
import Data.List (intercalate, isPrefixOf, sort)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Effectful (Eff)
import Effectful.Exception qualified as Eff
import System.Console.Haskeline
  ( Completion (isFinished),
    InputT,
    Settings (complete, historyFile),
    completeWord,
    defaultSettings,
    getInputLine,
    outputStr,
    outputStrLn,
    runInputT,
    simpleCompletion,
  )
import System.Console.Haskeline.Completion (CompletionFunc)
import System.Directory (XdgDirectory (..), createDirectoryIfMissing, getXdgDirectory)
import System.Exit (exitFailure)
import System.FilePath (takeDirectory)
import System.IO (hPutStr, hPutStrLn, stderr)
import YCHR.Display (Display (..), displayMsg)
import YCHR.PExpr qualified as P
import YCHR.Parsed qualified as Parsed
import YCHR.Parser (opTableEntries)
import YCHR.Pretty (prettyQueryResult, renderAtom)
import YCHR.Run
  ( CompiledProgram (..),
    Error (..),
    PreparedQuery (..),
    Warning,
    compileFiles,
    executePreparedQuery,
    prepareQuery,
  )
import YCHR.Runtime.Interpreter (HostCallRegistry)
import YCHR.Runtime.Session (CHREffects, toSessionInput, withCHR, withCHRExtra)
import YCHR.TypeCheck (typeCheckProgram)
import YCHR.Types (Term)
import YCHR.Types qualified as Types

-- ---------------------------------------------------------------------------
-- Entry point
-- ---------------------------------------------------------------------------

-- | Run the interactive REPL on the given files. Compiles the inputs
-- (or an empty program if @files@ is empty), prints any warnings and
-- type errors to stderr, then enters the outer command loop. The
-- session continues until the user types @:quit@ or hits EOF. When
-- @werror@ is set, warnings during the initial load abort startup;
-- during @:recompile@ they keep the previous program loaded.
runRepl :: HostCallRegistry -> Bool -> Bool -> [FilePath] -> IO ()
runRepl hostCalls quietMode werror files = do
  result <- compileFiles True files
  case result of
    Left err -> do
      putStr (displayMsg err)
      exitFailure
    Right (prog, warnings) -> do
      let warnsFatal = werror && not (null warnings)
      when (warnsFatal || not quietMode) (printWarnings warnings)
      when warnsFatal exitFailure
      unless quietMode (printTypeErrors prog)
      histFile <- getXdgDirectory XdgData "ychr/history"
      createDirectoryIfMissing True (takeDirectory histFile)
      let exported = exportedNames prog
          baseSettings = (defaultSettings :: Settings IO) {historyFile = Just histFile}
          outerSettings = baseSettings {complete = matchAgainst (commandNames ++ exported)}
          liveSettings = baseSettings {complete = matchAgainst (":end" : exported)}
      runInputT outerSettings (outerLoop hostCalls quietMode werror files liveSettings prog)

-- ---------------------------------------------------------------------------
-- Outer REPL loop
-- ---------------------------------------------------------------------------

outerLoop ::
  HostCallRegistry ->
  Bool ->
  Bool ->
  [FilePath] ->
  Settings IO ->
  CompiledProgram ->
  InputT IO ()
outerLoop hostCalls quietMode werror files liveSettings = go
  where
    prompt = if quietMode then "" else "ychr> "
    go prog = do
      minput <- getInputLine prompt
      case minput of
        Nothing -> pure ()
        Just input -> dispatch prog input
    dispatch prog input = case input of
      ":quit" -> pure ()
      ":q" -> pure ()
      ":help" -> showHelp *> go prog
      ":h" -> showHelp *> go prog
      ":recompile" -> recompile prog
      ":r" -> recompile prog
      ":list_files" -> showFiles files *> go prog
      ":list_modules" -> showModules prog *> go prog
      ":list_declarations" -> showDeclarations prog *> go prog
      ":list_operators" -> showOperators prog *> go prog
      ":begin" -> do
        liftIO (runLiveSession hostCalls liveSettings quietMode werror prog)
        go prog
      "" -> go prog
      line -> runOuterQuery hostCalls werror prog line *> go prog
    recompile prog = do
      result <- liftIO (compileFiles True files)
      case result of
        Left err -> outputStr (displayMsg err) *> go prog
        Right (prog', warnings)
          | werror && not (null warnings) -> do
              liftIO (printWarnings warnings)
              -- Surface type errors of the rejected program too, so the
              -- user sees the full diagnostic picture before deciding
              -- what to fix; the previous program stays loaded.
              liftIO (printTypeErrors prog')
              go prog
          | otherwise -> do
              liftIO (printWarnings warnings)
              liftIO (printTypeErrors prog')
              go prog'

-- | Run a one-off query in the outer REPL: parse, typecheck, execute
-- in a fresh CHR session. Distinct exception classes are surfaced
-- differently — 'Error' values via 'displayMsg', everything else as
-- @"Error: " ++ displayException@. Under @--Werror@, query-rename
-- warnings short-circuit before execution; the constraint store is
-- untouched (one-shot queries get a fresh store anyway).
runOuterQuery :: HostCallRegistry -> Bool -> CompiledProgram -> String -> InputT IO ()
runOuterQuery hostCalls werror prog line = do
  prepResult <-
    liftIO $
      try @SomeException $
        prepareQuery prog (T.pack line)
  case prepResult of
    Left exc -> reportException exc
    Right (prep, ws) -> do
      liftIO (printWarnings ws)
      unless (werror && not (null ws)) $ do
        execResult <-
          liftIO $
            try @SomeException $
              withCHRExtra (toSessionInput prog) hostCalls prep.extraProcs $
                executePreparedQuery hostCalls prep.liftedGoals
        case execResult of
          Left exc -> reportException exc
          Right bindings -> outputStr (prettyQueryResult bindings)
  where
    reportException exc = case fromException exc of
      Just err -> outputStr (displayMsg (err :: Error))
      Nothing -> outputStrLn ("Error: " ++ displayException exc)

-- ---------------------------------------------------------------------------
-- Live REPL session
-- ---------------------------------------------------------------------------

-- | Run an interactive live session. A single 'withCHR' call wraps
-- the whole session, so the constraint store, propagation history,
-- and reactivation queue persist across queries entered at the
-- @ychr live>@ prompt. The session ends when the user types @:end@,
-- hits EOF, or a runtime error aborts execution.
runLiveSession ::
  HostCallRegistry ->
  Settings IO ->
  Bool ->
  Bool ->
  CompiledProgram ->
  IO ()
runLiveSession hostCalls settings quietMode werror cp =
  withCHR (toSessionInput cp) hostCalls liveLoop
  where
    prompt = if quietMode then "" else "ychr live> "
    liveLoop :: (CHREffects es) => Eff es ()
    liveLoop = do
      mline <- liftIO (runInputT settings (getInputLine prompt))
      case mline of
        Nothing -> pure ()
        Just line -> dispatch line
    dispatch line
      | stripped == ":end" = pure ()
      | T.null stripped = liveLoop
      | otherwise = do
          outcome <- handleLiveQuery cp hostCalls werror (T.pack line)
          case outcome of
            QueryOk bindings -> do
              liftIO (putStr (prettyQueryResult bindings))
              liveLoop
            QueryRecoverable msg -> do
              liftIO (hPutStr stderr msg)
              liveLoop
            QueryFatal msg -> liftIO $ do
              hPutStr stderr msg
              hPutStrLn stderr "live session aborted due to runtime error."
      where
        stripped = T.strip (T.pack line)

-- | Outcome of executing a single live-session query.
data QueryOutcome
  = -- | Query ran to completion. Carries the resulting bindings.
    QueryOk (Map Text Term)
  | -- | A pre-execution problem (parse, type, lambdas-rejected) that
    -- left the constraint store untouched. The session can continue.
    QueryRecoverable String
  | -- | A runtime exception thrown during goal execution. The store
    -- and bindings may be inconsistent; the live session must abort.
    QueryFatal String

-- | Handle one query inside an existing live session: parse / typecheck
-- in 'IO' (catching 'Error'), reject lifted lambdas (live sessions
-- cannot grow the procedure map), then execute and catch any runtime
-- exception as a fatal outcome. Under @--Werror@, query-rename
-- warnings short-circuit before execution: the warnings are printed
-- to stderr and the query is treated as recoverable, leaving the
-- session's constraint store untouched.
handleLiveQuery ::
  (CHREffects es) =>
  CompiledProgram ->
  HostCallRegistry ->
  Bool ->
  Text ->
  Eff es QueryOutcome
handleLiveQuery cp hostCalls werror src = do
  prepResult <- liftIO (try @SomeException (prepareQuery cp src))
  case prepResult of
    Left exc -> pure (classifyAsRecoverable exc)
    Right (prep, ws) -> do
      liftIO (printWarnings ws)
      if werror && not (null ws)
        then pure (QueryRecoverable "")
        else
          if not (null prep.queryLambdas)
            then pure (QueryRecoverable (displayMsg LambdasInLiveQuery))
            else do
              execResult <-
                Eff.try @SomeException
                  ( executePreparedQuery
                      hostCalls
                      prep.liftedGoals
                  )
              case execResult of
                Left exc -> pure (QueryFatal (renderFatal exc))
                Right bindings -> pure (QueryOk bindings)
  where
    classifyAsRecoverable exc = case fromException exc :: Maybe Error of
      Just err -> QueryRecoverable (displayMsg err)
      Nothing -> QueryFatal (renderFatal exc)
    renderFatal exc = displayException exc ++ "\n"

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
    Command [":begin"] "Start a live CHR session (end with :end)",
    Command [":quit", ":q"] "Exit the REPL"
  ]

commandNames :: [String]
commandNames = concatMap (\c -> c.names) commands

-- ---------------------------------------------------------------------------
-- Command handlers
-- ---------------------------------------------------------------------------

showHelp :: InputT IO ()
showHelp = do
  outputStrLn "Commands:"
  mapM_ (outputStrLn . renderCommand) commands
  where
    -- Align descriptions at column 25 to match the original layout.
    renderCommand c =
      let label = intercalate ", " c.names
          padding = replicate (max 1 (23 - length label)) ' '
       in "  " ++ label ++ padding ++ c.description

showFiles :: [FilePath] -> InputT IO ()
showFiles = mapM_ outputStrLn

showModules :: CompiledProgram -> InputT IO ()
showModules prog =
  mapM_ (\(Parsed.Module {name = n}) -> outputStrLn (T.unpack n)) prog.allModules

showDeclarations :: CompiledProgram -> InputT IO ()
showDeclarations prog = mapM_ outputStrLn declLines
  where
    declLines =
      [ renderDecl kw m.name n a
      | m <- prog.allModules,
        Parsed.Ann d _ <- m.decls,
        (kw, n, a) <- case d of
          Parsed.ConstraintDecl {name = n, arity = a} -> [("chr_constraint", n, a)]
          Parsed.FunctionDecl {name = n, arity = a, isOpen = o} ->
            [(if o then "open_function" else "function", n, a)]
          Parsed.ExtendFunctionTypeDecl {name = n, arity = a} ->
            [("extend_function_type", n, a)]
          _ -> []
      ]
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

showOperators :: CompiledProgram -> InputT IO ()
showOperators prog = mapM_ (outputStrLn . renderOp) entries
  where
    entries = sort [(fix, opTypeStr ty, name) | (fix, ty, name) <- opTableEntries prog.opTable]
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
-- Completion and reporting helpers
-- ---------------------------------------------------------------------------

-- | Build a completion function that matches a fixed list of
-- candidates by prefix. Word boundaries are space and comma, matching
-- how a constraint conjunction is written.
matchAgainst :: [String] -> CompletionFunc IO
matchAgainst candidates =
  completeWord Nothing " ," $ \prefix ->
    pure $
      [ (simpleCompletion n) {isFinished = False}
      | n <- candidates,
        prefix `isPrefixOf` n
      ]

-- | Sorted list of unqualified exported constraint names from a
-- compiled program. Used as completion candidates in both modes.
exportedNames :: CompiledProgram -> [String]
exportedNames prog =
  Set.toAscList . Set.fromList $
    [T.unpack n | Types.UnqualifiedIdentifier n _ <- Map.keys prog.exportMap]

printWarnings :: [Warning] -> IO ()
printWarnings = mapM_ (hPutStr stderr . displayMsg)

printTypeErrors :: CompiledProgram -> IO ()
printTypeErrors prog = do
  errs <- typeCheckProgram prog.desugaredProgram
  mapM_ (hPutStr stderr . displayMsg) errs
