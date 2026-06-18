{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Interactive REPL for compiled CHR programs.
--
-- Owns all REPL UI: outer command loop (one-off queries plus colon
-- commands like @:list_declarations@), live-session loop (persistent
-- constraint store between queries, exit with @:end@), prompts, and
-- the help text. Line input (history, tab completion, EOF handling)
-- is delegated to 'YCHR.LineInput', whose implementation differs
-- between GHC (haskeline) and MicroHS (bare 'getLine'). Only
-- 'runRepl' is exported; everything else is internal.
module YCHR.Repl
  ( runRepl,
  )
where

import Control.Exception (SomeException, displayException, fromException, try)
import Control.Monad (unless, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask, runReaderT)
import Data.List (intercalate, sort, stripPrefix)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import System.Exit (exitFailure)
import System.IO (hPutStr, hPutStrLn, stderr, stdout)
import YCHR.Collected (CollectedModule (..))
import YCHR.Compile.Pipeline (ExportResolution (..))
import YCHR.Desugared qualified as D
import YCHR.Display (Display (..), displayMsg)
import YCHR.LineInput (LineInput (..), LineInputSettings (..), mkLineInput)
import YCHR.PExpr qualified as P
import YCHR.Parsed qualified as Parsed
import YCHR.Parser (opTableEntries, parseTermWith)
import YCHR.Pretty
  ( DeclKind (..),
    prettyConstraintDecl,
    prettyFunctionDecl,
    prettyQualifiedName,
    prettyQueryResult,
    prettyTypeDecl,
    renderAtom,
  )
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
import YCHR.Runtime.Monad (Chr)
import YCHR.Runtime.Session
  ( toSessionInput,
    withCHR,
    withCHRExtra,
    withCHRExtraTraced,
    withTraceHandler,
  )
import YCHR.Runtime.Trace (defaultTraceHandler)
import YCHR.TypeCheck (typeCheckProgram)
import YCHR.Types
  ( BoundSig,
    DataConstructor (..),
    Name (..),
    QualifiedName (..),
    Term (..),
    TypeDefinition (..),
    TypeExpr,
    typeConstructors,
  )
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
      let exported = exportedNames prog
      outerInput <-
        mkLineInput
          LineInputSettings
            { historyFile = Just "ychr/history",
              completionCandidates = commandNames ++ exported
            }
      liveInput <-
        mkLineInput
          LineInputSettings
            { historyFile = Just "ychr/history",
              completionCandidates = ":end" : exported
            }
      outerLoop hostCalls quietMode werror files outerInput liveInput prog

-- ---------------------------------------------------------------------------
-- Outer REPL loop
-- ---------------------------------------------------------------------------

outerLoop ::
  HostCallRegistry ->
  Bool ->
  Bool ->
  [FilePath] ->
  LineInput ->
  LineInput ->
  CompiledProgram ->
  IO ()
outerLoop hostCalls quietMode werror files outerInput liveInput = go
  where
    prompt = if quietMode then "" else "ychr> "
    go prog = do
      minput <- outerInput.readLine prompt
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
      ":info" -> showInfoUsage *> go prog
      ":i" -> showInfoUsage *> go prog
      ":trace" -> showTraceUsage *> go prog
      ":begin" -> do
        runLiveSession hostCalls liveInput quietMode werror prog
        go prog
      "" -> go prog
      line
        | Just rest <- stripPrefix ":info " line -> showInfo prog rest *> go prog
        | Just rest <- stripPrefix ":i " line -> showInfo prog rest *> go prog
        | Just rest <- stripPrefix ":trace " line ->
            runTracedQuery hostCalls werror prog rest *> go prog
        | otherwise -> runOuterQuery hostCalls werror prog line *> go prog
    recompile prog = do
      result <- compileFiles True files
      case result of
        Left err -> putStr (displayMsg err) *> go prog
        Right (prog', warnings)
          | werror && not (null warnings) -> do
              printWarnings warnings
              -- Surface type errors of the rejected program too, so the
              -- user sees the full diagnostic picture before deciding
              -- what to fix; the previous program stays loaded.
              printTypeErrors prog'
              go prog
          | otherwise -> do
              printWarnings warnings
              printTypeErrors prog'
              go prog'

-- | Run a one-off query in the outer REPL: parse, typecheck, execute
-- in a fresh CHR session. Distinct exception classes are surfaced
-- differently — 'Error' values via 'displayMsg', everything else as
-- @"Error: " ++ displayException@. Under @--Werror@, query-rename
-- warnings short-circuit before execution; the constraint store is
-- untouched (one-shot queries get a fresh store anyway).
runOuterQuery :: HostCallRegistry -> Bool -> CompiledProgram -> String -> IO ()
runOuterQuery hostCalls werror prog line = do
  prepResult <-
    try @SomeException $
      prepareQuery prog (T.pack line)
  case prepResult of
    Left exc -> reportException exc
    Right (prep, ws) -> do
      printWarnings ws
      unless (werror && not (null ws)) $ do
        execResult <-
          try @SomeException $
            withCHRExtra (toSessionInput prog) hostCalls prep.extraProcs $
              executePreparedQuery prep.liftedGoals
        case execResult of
          Left exc -> reportException exc
          Right bindings -> putStr (prettyQueryResult bindings)
  where
    reportException exc = case fromException exc of
      Just err -> putStr (displayMsg (err :: Error))
      Nothing -> putStrLn ("Error: " ++ displayException exc)

-- | Run a one-off query in the outer REPL with refined-operational-
-- semantics tracing enabled. Output is the trace stream only —
-- bindings are intentionally not printed, matching the documented
-- @:trace@ behaviour. To see bindings, re-run the goal without
-- @:trace@.
runTracedQuery :: HostCallRegistry -> Bool -> CompiledProgram -> String -> IO ()
runTracedQuery hostCalls werror prog line = do
  prepResult <-
    try @SomeException $
      prepareQuery prog (T.pack line)
  case prepResult of
    Left exc -> reportException exc
    Right (prep, ws) -> do
      printWarnings ws
      unless (werror && not (null ws)) $ do
        execResult <-
          try @SomeException $
            withCHRExtraTraced
              (toSessionInput prog)
              hostCalls
              prep.extraProcs
              (defaultTraceHandler stdout)
              (executePreparedQuery prep.liftedGoals)
        case execResult of
          Left exc -> reportException exc
          Right _ -> pure ()
  where
    reportException exc = case fromException exc of
      Just err -> putStr (displayMsg (err :: Error))
      Nothing -> putStrLn ("Error: " ++ displayException exc)

showTraceUsage :: IO ()
showTraceUsage =
  putStrLn ":trace GOAL  -- run GOAL with refined-operational-semantics tracing"

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
  LineInput ->
  Bool ->
  Bool ->
  CompiledProgram ->
  IO ()
runLiveSession hostCalls liveInput quietMode werror cp =
  withCHR (toSessionInput cp) hostCalls liveLoop
  where
    prompt = if quietMode then "" else "ychr live> "
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
              handleLiveQuery cp werror rest
          case outcome of
            QueryOk _ -> liveLoop
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
          outcome <- handleLiveQuery cp werror (T.pack line)
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
  CompiledProgram ->
  Bool ->
  Text ->
  Chr QueryOutcome
handleLiveQuery cp werror src = do
  prepResult <- liftIO (try @SomeException (prepareQuery cp src))
  case prepResult of
    Left exc -> pure (classifyAsRecoverable exc)
    Right (prep, ws) -> do
      liftIO (printWarnings ws)
      if werror && not (null ws)
        then pure (QueryRecoverable "")
        else case prep.queryLambdas of
          (lam : _) ->
            let lamEqs = lam.equations :: Parsed.AnnP [D.Equation]
                Parsed.AnnP _ loc origin = lamEqs
             in pure (QueryRecoverable (displayMsg (LambdasInLiveQuery loc origin)))
          [] -> do
            env <- ask
            execResult <-
              liftIO $
                try @SomeException $
                  runReaderT (executePreparedQuery prep.liftedGoals) env
            case execResult of
              Left exc -> pure (QueryFatal (renderFatal exc))
              Right bindings -> pure (QueryOk bindings)
  where
    classifyAsRecoverable exc = case fromException exc :: Maybe Error of
      Just err -> QueryRecoverable (displayMsg err)
      Nothing -> QueryFatal (renderFatal exc)
    -- A fatal exception is most often an 'Error' (e.g. a runtime error
    -- escaping 'executePreparedQuery'); rendering through 'displayMsg'
    -- gives the same nicely-formatted output the outer REPL produces.
    -- Anything else falls back to 'displayException'.
    renderFatal exc = case fromException exc :: Maybe Error of
      Just err -> displayMsg err
      Nothing -> displayException exc ++ "\n"

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
    Command [":trace"] "Run a goal with refined-operational-semantics tracing",
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
    -- Align descriptions at column 25 to match the original layout.
    renderCommand c =
      let label = intercalate ", " c.names
          padding = replicate (max 1 (23 - length label)) ' '
       in "  " ++ label ++ padding ++ c.description

showFiles :: [FilePath] -> IO ()
showFiles = mapM_ putStrLn

showModules :: CompiledProgram -> IO ()
showModules prog =
  mapM_ (\(CollectedModule {name = n}) -> putStrLn (T.unpack n)) prog.allModules

showDeclarations :: CompiledProgram -> IO ()
showDeclarations prog = mapM_ putStrLn declLines
  where
    declLines = dedup entries
    entries =
      [ (kw, m.name, n, a)
      | m <- prog.allModules,
        Parsed.Ann d _ <- m.decls,
        (kw, n, a) <- case d of
          Parsed.ConstraintDecl {name = n, arity = a} -> [("chr_constraint", n, a)]
          Parsed.FunctionDecl {name = n, arity = a, isOpen = o, kind = k} ->
            let kw = case (o, k) of
                  (False, Parsed.DKFunction) -> "function"
                  (True, Parsed.DKFunction) -> "open_function"
                  (False, Parsed.DKClass) -> "class"
                  (True, Parsed.DKClass) -> "open_class"
             in [(kw, n, a)]
          Parsed.ExtendClassTypeDecl {name = n, arity = a} ->
            [("extend_class_type", n, a)]
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
-- :info / :i — identifier inspection
-- ---------------------------------------------------------------------------

-- | Hard-coded set of names recognized as base types of the
-- @'$typechecker'@ module. These match the @ty@ ADT constructors
-- treated specially by 'YCHR.TypeCheck.encodeTypeExpr'.
builtinTypeNames :: [Text]
builtinTypeNames = ["int", "float", "string", "any"]

showInfoUsage :: IO ()
showInfoUsage = putStrLn "usage: :info <identifier>"

-- | Parse the argument to @:info@. Accepts @name@, @name/arity@,
-- @mod:name@, or @mod:name/arity@. Returns 'Nothing' if the parse
-- fails or the resulting term is not a recognized identifier shape,
-- in which case 'showInfo' falls back to "unknown identifier".
parseInfoArg :: CompiledProgram -> Text -> Maybe (Either Text QualifiedName, Maybe Int)
parseInfoArg prog raw = case parseTermWith prog.opTable "<:info>" raw of
  Left _ -> Nothing
  Right t -> termToInfoArg t

termToInfoArg :: Term -> Maybe (Either Text QualifiedName, Maybe Int)
termToInfoArg = \case
  CompoundTerm (Unqualified "/") [headT, IntTerm a] -> do
    (nm, _) <- termToInfoArg headT
    pure (nm, Just (fromInteger a))
  CompoundTerm (Unqualified n) [] ->
    Just (Left n, Nothing)
  CompoundTerm (Qualified m n) [] ->
    Just (Right (QualifiedName m n), Nothing)
  _ -> Nothing

-- | One discovered fact about an identifier. The qualified name is
-- always attached so 'renderInfoEntry' does not need to re-derive it.
data InfoEntry
  = -- | The identifier is a constraint. The @Maybe [TypeExpr]@ is
    -- 'Just' when the constraint is typed (declared via
    -- @:- chr_constraint name(T1, ..., Tn)@), 'Nothing' otherwise.
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
                [ IEBuiltinType (QualifiedName "$typechecker" n)
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
                [ length args
                | (qn', args) <- Map.toList prog.desugaredProgram.constraintTypes,
                  qn' == qn
                ]
              fArities =
                [f.arity | f <- prog.desugaredProgram.functions, f.name == qn]
              exportArities =
                [ a
                | Types.QualifiedIdentifier m n a <- Set.toAscList prog.exportedSet,
                  m == qn.moduleName && n == qn.baseName
                ]
              allArities =
                sort (Set.toAscList (Set.fromList (cTyArities ++ fArities ++ exportArities)))
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
        | qn.moduleName == "$typechecker",
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
    [] -> case Map.lookup qn prog.desugaredProgram.constraintTypes of
      Just args
        | length args == arity ->
            let bs = Map.findWithDefault [] qn prog.desugaredProgram.constraintBounds
             in [IEConstraint qn arity (Just args) bs]
      _ -> []

-- | Recover the @function@ / @open_function@ / @class@ / @open_class@
-- keyword for a 'D.Function' by scanning every parsed module's
-- declarations. Returns the first matching 'Parsed.FunctionDecl' (in
-- 'allModules' iteration order); defaults to 'DKFunction' if none is
-- found, which only happens for synthetic declarations like lifted
-- lambdas (@__lambda_N@) that users would not normally inspect.
functionDeclKind :: CompiledProgram -> QualifiedName -> Int -> DeclKind
functionDeclKind prog qn arity =
  let matches =
        [ (d.isOpen, d.kind)
        | m <- prog.allModules,
          m.name == qn.moduleName,
          Parsed.Ann d _ <- m.decls,
          Parsed.FunctionDecl {} <- [d],
          d.name == qn.baseName,
          d.arity == arity
        ]
   in case matches of
        ((False, Parsed.DKFunction) : _) -> DKFunction
        ((True, Parsed.DKFunction) : _) -> DKOpenFunction
        ((False, Parsed.DKClass) : _) -> DKClass
        ((True, Parsed.DKClass) : _) -> DKOpenClass
        [] -> DKFunction

-- The renamer guarantees that 'TypeDefinition.name' and
-- 'DataConstructor.conName' are always 'Qualified' once resolution
-- completes (see 'renameDataConstructor' and 'renameTypeDefinition'
-- in "YCHR.Rename"). The 'Unqualified' arms below are defensive
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
-- The rule mirrors 'YCHR.Rename.exporterAllowance': a module with no
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
            case [cs | Parsed.TypeExportDecl tn' ta' cs <- exports, tn' == tn, ta' == ta] of
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
showInfo prog raw =
  let trimmed = T.strip (T.pack raw)
   in if T.null trimmed
        then showInfoUsage
        else case parseInfoArg prog trimmed of
          Nothing -> printUnknown (T.unpack trimmed)
          Just (name, mArity) ->
            case lookupInfo prog name mArity of
              [] -> printUnknown (T.unpack trimmed)
              entries -> putStr (renderInfo entries)
  where
    printUnknown s = putStrLn ("unknown identifier: " ++ s)

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
      ++ prettyFunctionDecl f.name f.arity f.signatures f.requiring kind
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

printTypeErrors :: CompiledProgram -> IO ()
printTypeErrors prog = do
  errs <- typeCheckProgram prog.desugaredProgram
  mapM_ (hPutStr stderr . displayMsg) errs
