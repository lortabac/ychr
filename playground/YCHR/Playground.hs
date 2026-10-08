{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The engine behind the web playground.
--
-- A 'Playground' is one loaded program plus the two resources every
-- YCHR entry point needs (the parsed standard library and the compiled
-- type checker), and the operations the page offers: reload the editor
-- contents, run one query, type-check what is loaded.
--
-- This module is deliberately free of FFI and of any assumption about a
-- browser: the WASM bridge ('YCHR.Playground.Wasm') and the native
-- harness (@playground\/Main.hs@) are thin wrappers over the functions
-- below, so both front ends behave identically and the native one is
-- testable without emscripten.
--
-- Every operation returns a /response/: a status token and a payload,
--
-- > ok\n\n<payload>
-- > error\n\n<payload>
--
-- where the payload is the text the CLI would have printed. Splitting on
-- the first @\\n\\n@ is the whole protocol — no JSON, hence no escaping
-- layer — and the payload keeps the ANSI SGR sequences @displayMsg@
-- produces, which the page renders as HTML.
--
-- Type checking is never implicit: 'reload' and 'runReplLine' behave
-- like the CLI's @--no-check@, and only 'typecheck' forces
-- 'YCHR.Internal.TypeCheck.typeCheckProgram'. That is deliberate — the
-- checker is itself a CHR program, and compiling it is a one-off cost
-- that dwarfs a program check (see @docs\/how-to\/web-playground.md@).
module YCHR.Playground
  ( -- * State
    Playground (..),

    -- * Operations
    initPlayground,
    reload,
    runReplLine,
    typecheck,

    -- * Rendering
    helpText,
    response,
    statusOk,
    statusError,
  )
where

import Control.Exception
  ( SomeException,
    displayException,
    evaluate,
    fromException,
    try,
  )
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Collected (CollectedModule (..))
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..))
import YCHR.Internal.Display (displayMsg)
import YCHR.Internal.Parsed qualified as Parsed
import YCHR.Internal.Pretty (prettyQueryResult)
import YCHR.Internal.Repl qualified as Repl
import YCHR.Internal.Resources (Resources (..), loadResourcesAt)
import YCHR.Internal.Runtime.Interpreter (HostCallRegistry)
import YCHR.Internal.Runtime.Search (defaultHostCallRegistry)
import YCHR.Internal.Runtime.Session (SessionInput, toSessionInput, withCHRExtra)
import YCHR.Internal.StdLib (StdLib (..))
import YCHR.Internal.TypeCheck (TypeCheckResult (..), typeCheckProgram)
import YCHR.Run
  ( Error,
    PreparedQuery (..),
    Warning (..),
    compileModules,
    executePreparedQuery,
    prepareQueryUnchecked,
  )

-- ---------------------------------------------------------------------------
-- State
-- ---------------------------------------------------------------------------

-- | Everything the page keeps between requests: the two resources and
-- whatever program is currently loaded ('Nothing' until the first
-- successful reload).
--
-- 'loaded' holds the /last program that compiled/. A reload that fails
-- leaves it alone, so a typo in the editor never costs you the working
-- program — the same policy the terminal REPL applies to
-- @:recompile@.
data Playground = Playground
  { stdlib :: StdLib,
    -- | The compiled type checker. Lazy: building it is the expensive
    -- step, and 'reload' and 'runReplLine' never force it.
    checker :: SessionInput,
    loaded :: Maybe CompiledProgram
  }

-- | Load the bundled resources from a source-tree root (@libraries\/@
-- and @typechecker\/@ under it; @\"\/\"@ in the browser, where the two
-- directories are preloaded into the WASM file system).
--
-- Only the standard library is parsed here: the type checker stays a
-- thunk, so a bad checker is reported when the user first presses
-- /Typecheck/ rather than at page load.
initPlayground :: FilePath -> IO (Either String Playground)
initPlayground root = do
  result <- loadResourcesAt root
  pure $ case result of
    Left err -> Left (T.unpack err)
    Right resources ->
      Right
        Playground
          { stdlib = resources.stdlib,
            checker = resources.typeCheckerProgram,
            loaded = Nothing
          }

-- ---------------------------------------------------------------------------
-- Responses
-- ---------------------------------------------------------------------------

-- | The success status token. The page matches on it to pick the
-- payload's styling.
statusOk :: String
statusOk = "ok"

-- | The failure status token.
statusError :: String
statusError = "error"

-- | Build a response from a status and a payload.
response :: String -> String -> String
response status payload = status ++ "\n\n" ++ payload

-- | Run an operation and force its payload before returning.
--
-- Everything an operation reports — warnings, diagnostics, query
-- bindings — is built lazily, so an operation that returns normally may
-- still raise while its payload is being rendered (the compiler has
-- partial pure functions on these paths). Past this function the payload
-- is written into a C string and crosses back into JavaScript, where
-- there is no handler: on the WASM side that would abort the
-- module and lose the loaded program. So the payload is forced /here/,
-- inside the same 'try' as the operation itself, and a failure becomes
-- an ordinary error response.
--
-- The state a failed operation would have installed is dropped with it:
-- the response describes the 'Playground' the caller still has.
guarded :: Playground -> IO (Playground, String) -> IO (Playground, String)
guarded pg act = do
  attempt <- try @SomeException $ do
    pair@(_, out) <- act
    _ <- evaluate (length out)
    pure pair
  pure $ case attempt of
    Left exc -> (pg, response statusError (renderException exc))
    Right pair -> pair

-- | Render the warnings of a compilation the way the CLI does — through
-- 'displayMsg', so the payload carries the same ANSI colours.
renderWarnings :: [Warning] -> String
renderWarnings = concatMap displayMsg

-- | The type checker reports its warnings as plain diagnostics rather
-- than as a 'Warning'; wrap them the way the CLI and the REPL do, so
-- they render identically.
renderTypeWarnings :: TypeCheckResult -> String
renderTypeWarnings result
  | null result.warnings = ""
  | otherwise = renderWarnings [TypeCheckWarnings result.warnings]

-- | Render an exception the way the REPL does: a project 'Error' through
-- its formatter, anything else through 'displayException'.
renderException :: SomeException -> String
renderException exc = case fromException exc of
  Just err -> displayMsg (err :: Error)
  Nothing -> "Error: " ++ displayException exc ++ "\n"

-- ---------------------------------------------------------------------------
-- Reload
-- ---------------------------------------------------------------------------

-- | Compile the editor's text as a one-file program and make it the
-- loaded program. Never type-checks (the CLI's @--no-check@).
--
-- The synthetic module path @editor.chr@ is what diagnostics print; the
-- file need not exist, since 'compileModules' compiles from text.
--
-- @includeStdlib@ is 'False', as it is for every CLI command: the
-- standard library is pulled in only as far as the program's own
-- @:- use_module(library(…))@ clauses reach (the prelude is always
-- seeded). Passing 'True' would compile /and type-check/ the whole
-- bundled library on every reload, which is invisible for compilation
-- but dominates type checking — the checker would be handed ~900
-- procedures of library code before the program's own.
reload :: Playground -> Text -> IO (Playground, String)
reload pg src = guarded pg $ do
  compiled <-
    evaluate (compileModules pg.stdlib False [("editor.chr", src)])
  pure $ case compiled of
    Left err -> (pg, response statusError (displayMsg err))
    Right (prog, warnings) ->
      ( pg {loaded = Just prog},
        response statusOk (renderWarnings warnings ++ summary pg prog)
      )

-- | The one line a successful reload prints: which constraint types the
-- /user's/ modules declare. Standard-library constraints are left out —
-- the libraries export a hundred names between them, and listing them
-- would bury the program's own declarations.
--
-- This line is the playground's own; no CLI command prints it.
summary :: Playground -> CompiledProgram -> String
summary pg prog =
  case constraints of
    [] -> "Loaded (no constraint declarations).\n"
    _ ->
      "Loaded "
        ++ show (length constraints)
        ++ " constraint"
        ++ (if length constraints == 1 then "" else "s")
        ++ ": "
        ++ unwords (map render constraints)
        ++ "\n"
  where
    -- The bundled libraries, by module name: everything else in the
    -- program came from the editor.
    libraryModules = case pg.stdlib of StdLib m -> Map.keysSet m
    constraints =
      Set.toAscList . Set.fromList $
        [ (n, a)
        | m <- prog.allModules,
          not (Set.member m.name libraryModules),
          Parsed.Ann d _ <- m.decls,
          Parsed.ConstraintDecl Parsed.ConstraintDeclBody {name = n, arity = a} <- [d]
        ]
    render (n, a) = T.unpack n ++ "/" ++ show a

-- ---------------------------------------------------------------------------
-- Queries
-- ---------------------------------------------------------------------------

-- | Answer one line from the REPL pane: a colon command, or a goal.
--
-- A goal runs exactly like the CLI's outer REPL under @--no-check@ —
-- parse, execute in a fresh CHR session, print the bindings — except
-- that nothing is written to @stdout@; the response carries it. The
-- goal syntax is documented in @docs\/reference\/repl.md@.
runReplLine :: Playground -> Text -> IO (Playground, String)
runReplLine pg line = guarded pg (dispatch (T.strip line))
  where
    dispatch stripped
      | T.null stripped = pure (pg, response statusOk "")
      | Just _ <- T.stripPrefix ":" stripped = pure (pg, runCommand pg stripped)
      | otherwise = runGoal pg stripped

-- | The colon commands the page supports: the terminal REPL's
-- @:help@\/@:h@, @:list_modules@, @:list_files@,
-- @:list_declarations@ and @:info@\/@:i@, rendered by the shared
-- helpers in "YCHR.Internal.Repl"; anything else is rejected with a
-- pointer at @:help@. @:quit@ and @:q@ are accepted and ignored —
-- there is nothing to exit.
--
-- @:begin@, @:trace@, @:time@, @:recompile@ and @:list_operators@ are
-- deliberately absent: the page runs one-shot queries from a buffer it
-- already owns, and the other three are bound to a terminal (a live
-- session, a trace stream, a CPU-clock reading).
runCommand :: Playground -> Text -> String
runCommand pg command = case words (T.unpack command) of
  (cmd : _) | cmd `elem` [":help", ":h"] -> response statusOk helpText
  (cmd : _) | cmd `elem` [":q", ":quit"] -> response statusOk ""
  (":list_modules" : _) -> withProgram Repl.modulesText
  -- The page has exactly one input file — the editor buffer — so this
  -- answers without a program loaded.
  (":list_files" : _) -> response statusOk "editor.chr\n"
  (":list_declarations" : _) -> withProgram Repl.declarationsText
  (":info" : rest) -> withProgram (\prog -> Repl.infoText prog (unwords rest))
  (":i" : rest) -> withProgram (\prog -> Repl.infoText prog (unwords rest))
  (cmd : _) -> response statusError ("Unknown command: " ++ cmd ++ " (try :help)\n")
  [] -> response statusOk ""
  where
    withProgram render = case pg.loaded of
      Nothing -> response statusError noProgram
      Just prog -> response statusOk (render prog)

-- | Run one goal against the loaded program, in a fresh CHR session.
runGoal :: Playground -> Text -> IO (Playground, String)
runGoal pg goal = case pg.loaded of
  Nothing -> pure (pg, response statusError noProgram)
  Just prog -> do
    prepared <- try @SomeException (prepareQueryUnchecked prog goal)
    case prepared of
      Left exc -> pure (pg, response statusError (renderException exc))
      Right (prep, warnings) -> executeQuery pg prog prep warnings

-- | Execute a prepared query in a fresh session. Split out of 'runGoal'
-- so 'PreparedQuery' is named in a signature: with @NoFieldSelectors@,
-- record-dot selection resolves through the field labels the type's
-- import brings in.
executeQuery ::
  Playground ->
  CompiledProgram ->
  PreparedQuery ->
  [Warning] ->
  IO (Playground, String)
executeQuery pg prog prep warnings = do
  let warns = renderWarnings warnings
  executed <-
    try @SomeException $
      withCHRExtra
        (toSessionInput prog)
        hostCalls
        prep.extraProcs
        prep.extraCallables
        (executePreparedQuery prep.liftedGoals)
  pure $ case executed of
    Left exc -> (pg, response statusError (warns ++ renderException exc))
    -- A ground goal binds nothing, and 'prettyQueryResult' returns
    -- the empty string for it; that is success, not silence.
    Right bindings -> (pg, response statusOk (warns ++ prettyQueryResult bindings))

-- | The message a query or a colon command prints when nothing has been
-- loaded yet.
noProgram :: String
noProgram = "No program loaded. Press Reload first.\n"

-- ---------------------------------------------------------------------------
-- Type checking
-- ---------------------------------------------------------------------------

-- | Type-check the loaded program with the compiled type checker,
-- forcing the checker on first use. Errors make the response an error
-- (as @ychr check@ exits non-zero); warnings do not.
typecheck :: Playground -> IO (Playground, String)
typecheck pg = guarded pg $ case pg.loaded of
  Nothing -> pure (pg, response statusError noProgram)
  Just prog -> do
    checked <-
      try @SomeException (typeCheckProgram pg.checker prog.desugaredProgram)
    pure $ case checked of
      Left exc -> (pg, response statusError (renderException exc))
      Right result
        | not (null result.errors) ->
            ( pg,
              response
                statusError
                (concatMap displayMsg result.errors ++ renderTypeWarnings result)
            )
        | otherwise ->
            (pg, response statusOk (renderTypeWarnings result))

-- ---------------------------------------------------------------------------
-- Help
-- ---------------------------------------------------------------------------

-- | The @:help@ text. Only the commands the page implements: the
-- terminal REPL's full list would advertise @:begin@, @:trace@ and
-- @:time@, which the page does not run.
helpText :: String
helpText =
  unlines
    [ "Commands:",
      "  :help                  Show this help message",
      "  :list_modules          List the compiled modules",
      "  :list_files            List the compiled files",
      "  :list_declarations     List visible declarations",
      "  :info <identifier>     Show information about an identifier",
      "",
      "Anything else is a goal, run in a fresh CHR session."
    ]

-- ---------------------------------------------------------------------------
-- Host calls
-- ---------------------------------------------------------------------------

-- | The host-call registry every session gets: the same default the CLI
-- installs.
hostCalls :: HostCallRegistry
hostCalls = defaultHostCallRegistry
