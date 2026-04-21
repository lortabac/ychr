{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module YCHR.Run
  ( -- * Compilation
    Error (..),
    Warning (..),
    CompiledProgram (..),
    ExportResolution (..),
    ConstraintType,
    compileModules,
    compileFiles,

    -- * CHR effect
    CHR,
    CHREffects,
    runCHR,
    withCHR,
    tellConstraint,

    -- * Re-exports for embedding
    Value (..),
    newVar,
    deref,
    equal,
    unify,

    -- * Single-goal API
    resolveQueryConstraint,
    runProgramWithGoalDSL,
    runProgramWithGoal,

    -- * Multi-goal query API
    runProgramWithQuery,
  )
where

import Control.Exception (Exception, throwIO)
import Control.Monad (unless, void, when)
import Data.Bifunctor (first)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Void (Void)
import Effectful
import Effectful.Dispatch.Static
import Effectful.State.Static.Local (State, evalState, get, modify)
import Effectful.Writer.Static.Local (Writer, listen, runWriter)
import Text.Megaparsec (ParseErrorBundle)
import YCHR.Collect (CollectError, addLibraryPrelude, resolveLibraryClosure, rewriteImports)
import YCHR.Compile (CompileError, buildFunctionSet, compile, compileFunctionDef, funcProcName, genCallFunDispatches, tellProcName, vmName)
import YCHR.Desugar (DesugarError, desugarProgram, desugarQueryGoals, extractSymbolTable, liftAllLambdas, liftQueryLambdas)
import YCHR.Desugared qualified as D
import YCHR.Diagnostic (Diagnostic)
import YCHR.Meta (valueToTerm)
import YCHR.PExpr (PExpr (Atom))
import YCHR.Parsed (AnnP (..), Import (..), Module (..), SourceLoc (..), noAnnP)
import YCHR.Parser (ModuleHeader (..), OpTable, ParseValidationError (..), buildModuleOpTable, builtinOps, collectModuleHeader, extractOpDecls, mergeOps, parseConstraint, parseModuleWith, parseQueryWith)
import YCHR.Pretty (prettyTerm)
import YCHR.Rename (RenameError, RenameInputs (..), RenameWarning, buildExportEnv, renameProgram, renameQueryGoals)
import YCHR.Rename.Types (toListExport)
import YCHR.Resolve (ResolveError, resolveProgram)
import YCHR.Resolved qualified as R
import YCHR.Runtime.History (PropHistory, runPropHistory)
import YCHR.Runtime.Interpreter (HostCallFn (..), HostCallRegistry, callProc)
import YCHR.Runtime.Reactivation (ReactQueue, drainQueue, enqueue, runReactQueue)
import YCHR.Runtime.Store (CHRStore, aliveConstraint, runCHRStore)
import YCHR.Runtime.Types (RuntimeVal (..), SuspensionId, Value (..))
import YCHR.Runtime.Var (Unify, deref, equal, newVar, runUnify, unify)
import YCHR.StdLib (stdlib)
import YCHR.Types (Constraint (..), ConstraintType, SymbolTable, Term (..))
import YCHR.Types qualified as Types
import YCHR.VM (Name (..), Procedure (..), Program (..), StackFrame)

data Error
  = ParseError FilePath (ParseErrorBundle Text Void)
  | ParseValidationErrors [AnnP ParseValidationError]
  | CollectErrors [Diagnostic CollectError]
  | RenameErrors [Diagnostic RenameError]
  | DesugarErrors [Diagnostic DesugarError]
  | ResolveErrors [Diagnostic ResolveError]
  | CompileErrors [Diagnostic CompileError]
  | OperatorConflict (AnnP Text)
  deriving (Show)

instance Exception Error

data Warning
  = RenameWarnings [Diagnostic RenameWarning]
  deriving (Show)

-- | A compiled CHR program together with module visibility information.
data CompiledProgram = CompiledProgram
  { program :: Program,
    exportMap :: Map Types.UnqualifiedIdentifier ExportResolution,
    exportedSet :: Set Types.QualifiedIdentifier,
    symbolTable :: SymbolTable,
    allModules :: [Module],
    opTable :: OpTable,
    -- | All functions in the desugared program (for call dispatch in queries).
    allFunctions :: [D.Function],
    -- | Counter for the next lambda index (to avoid collisions in queries).
    nextLambdaIndex :: Int,
    -- | Set of declared function names (for query goal classification).
    functionNameSet :: Set Types.Name
  }

data ExportResolution
  = UniqueExport Types.Name
  | AmbiguousExport [Text]
  deriving (Show, Eq)

compileModules :: Bool -> [(FilePath, Text)] -> Either Error (CompiledProgram, [Warning])
compileModules includeStdlib inputs = do
  -- Phase 1: lightweight first parse of each user file to collect the
  -- module name, exported operators, header use_module imports, and the
  -- location at which header parsing stopped.
  userHeaders <-
    first (\(fp, e) -> ParseError fp e) $
      traverse (\(fp, src) -> (fp,) <$> first' (fp,) (collectModuleHeader fp src)) inputs
  -- Resolve the transitive closure of library imports starting from the
  -- libraries each user header asks for (plus prelude as an implicit
  -- seed, and every stdlib library if includeStdlib is True).
  let userLibrarySeeds =
        noAnnP "prelude"
          : [AnnP n loc p | (_, h) <- userHeaders, AnnP (LibraryImport n _) loc p <- h.headerImports]
  libraryMods <- first CollectErrors (resolveLibraryClosure includeStdlib stdlib userLibrarySeeds)
  -- Build the module-name → exported-operators map used by per-module op
  -- table construction and by the renamer's UnknownOperatorImport check.
  let stdlibOpExports = Map.fromList [(m.name, extractOpDecls m) | m <- libraryMods]
      userOpExports = Map.fromList [(h.modName, h.exportOps) | (_, h) <- userHeaders]
      opExports = stdlibOpExports `Map.union` userOpExports
      preludeOps = Map.findWithDefault [] "prelude" opExports
  -- Build per-module operator tables and full-parse each user file with
  -- its specific table. A first conflict in any table aborts the whole
  -- compilation with OperatorConflict.
  parsedWithErrors <-
    traverse
      ( \((fp, src), (_, hdr)) -> do
          table <- case buildModuleOpTable builtinOps preludeOps opExports hdr of
            Left conflict -> Left (OperatorConflict (AnnP conflict hdr.modLoc hdr.modOrigin))
            Right t -> Right t
          first (ParseError fp) (parseModuleWith table fp src)
      )
      (zip inputs userHeaders)
  let parsed = map fst parsedWithErrors
      validationErrors = concatMap snd parsedWithErrors
  case validationErrors of
    [] -> pure ()
    errs -> Left (ParseValidationErrors errs)
  -- Auto-import prelude into every user module and into every library
  -- module (except prelude itself), then rewrite all LibraryImports to
  -- ModuleImports for the renamer.
  let allMods = rewriteImports (addLibraryPrelude libraryMods ++ map addPreludeImport parsed)
  let exportEnv = buildExportEnv allMods
      exportMap =
        Map.fromList
          [ (Types.UnqualifiedIdentifier n a, toResolution n ms)
          | ((n, a), ms) <- toListExport exportEnv
          ]
      exportedSet =
        Set.fromList
          [Types.QualifiedIdentifier m n a | ((n, a), ms) <- toListExport exportEnv, m <- ms]
      renameInputs =
        RenameInputs
          { riOperatorExports = opExports,
            riTrailingLoc = Map.fromList [(h.modName, h.trailingLoc) | (_, h) <- userHeaders]
          }
  (renamed, renameWarnings) <- first RenameErrors (renameProgram renameInputs allMods)
  resolved <- first ResolveErrors (resolveProgram renamed)
  desugared <- first DesugarErrors (desugarProgram resolved)
  desugared' <- first DesugarErrors (liftAllLambdas desugared)
  let symTab = extractSymbolTable desugared'
      warnings = [RenameWarnings renameWarnings | not (null renameWarnings)]
  prog <- first CompileErrors (compile desugared' symTab)
  -- The query parser uses the union of every user module's operator
  -- visibility, so a query at the REPL can use any operator any user
  -- module declares.
  queryTable <- case mergeOps builtinOps (concat (Map.elems opExports)) of
    Left conflict -> Left (OperatorConflict (noAnnP conflict))
    Right t -> Right t
  let lambdaCount = length [() | f <- desugared'.functions, isLambdaName f.name]
  pure (CompiledProgram prog exportMap exportedSet symTab allMods queryTable desugared'.functions lambdaCount resolved.functionNames, warnings)
  where
    first' f (Left e) = Left (f e)
    first' _ (Right x) = Right x
    toResolution n [m] = UniqueExport (Types.Qualified m n)
    toResolution _ ms = AmbiguousExport ms

-- | Prepend a synthetic @use_module(library(prelude))@ to a user module so
-- the renamer treats prelude exports as visible.
addPreludeImport :: Module -> Module
addPreludeImport m = m {imports = noAnnP (LibraryImport "prelude" Nothing) : m.imports}

compileFiles :: Bool -> [FilePath] -> IO (Either Error (CompiledProgram, [Warning]))
compileFiles includeStdlib paths = do
  contents <- mapM (\fp -> (fp,) <$> TIO.readFile fp) paths
  pure (compileModules includeStdlib contents)

-- ---------------------------------------------------------------------------
-- CHR effect
-- ---------------------------------------------------------------------------

type ProcMap = Map Name Procedure

-- | The CHR effect holds the program context needed to execute constraints.
-- | Runtime call stack for error reporting (newest first).
type CallStack = [StackFrame]

data CHR :: Effect

type instance DispatchOf CHR = Static WithSideEffects

data instance StaticRep CHR
  = CHRRep ProcMap HostCallRegistry (Map Types.UnqualifiedIdentifier ExportResolution) (Set Types.QualifiedIdentifier)

-- | Shorthand for the full set of effects available inside a CHR session.
type CHREffects es =
  ( CHR :> es,
    Unify :> es,
    CHRStore :> es,
    PropHistory :> es,
    ReactQueue :> es,
    Writer [SuspensionId] :> es,
    State CallStack :> es,
    IOE :> es
  )

-- | Set up a CHR session for a compiled program. All runtime state (constraint
-- store, propagation history, reactivation queue, unification variables) is
-- initialised and persists for the duration of the computation.
runCHR ::
  (IOE :> es) =>
  CompiledProgram ->
  HostCallRegistry ->
  Eff (CHR : State CallStack : Writer [SuspensionId] : ReactQueue : PropHistory : CHRStore : Unify : es) a ->
  Eff es a
runCHR cp hc =
  runUnify
    . runCHRStore cp.program.typeNames
    . runPropHistory
    . runReactQueue
    . fmap fst
    . runWriter @[SuspensionId]
    . evalState @CallStack []
    . evalStaticRep (CHRRep procMap hc cp.exportMap cp.exportedSet)
  where
    procMap = Map.fromList [(pname, p) | p@Procedure {name = pname} <- cp.program.procedures]

-- | Convenience wrapper that runs a CHR session in 'IO'.
withCHR ::
  CompiledProgram ->
  HostCallRegistry ->
  (forall es. (CHREffects es) => Eff es a) ->
  IO a
withCHR cp hc action = runEff (runCHR cp hc action)

-- | Like 'withCHR' but merges extra procedures (e.g. query-time lambda
-- compilations and updated call dispatches) into the ProcMap.
withCHRExtra ::
  CompiledProgram ->
  HostCallRegistry ->
  [Procedure] ->
  (forall es. (CHREffects es) => Eff es a) ->
  IO a
withCHRExtra cp hc extraProcs action =
  runEff
    . runUnify
    . runCHRStore cp.program.typeNames
    . runPropHistory
    . runReactQueue
    . fmap fst
    . runWriter @[SuspensionId]
    . evalState @CallStack []
    . evalStaticRep (CHRRep procMap hc cp.exportMap cp.exportedSet)
    $ action
  where
    baseProcMap = Map.fromList [(pname, p) | p@Procedure {name = pname} <- cp.program.procedures]
    extraProcMap = Map.fromList [(pname, p) | p@Procedure {name = pname} <- extraProcs]
    procMap = extraProcMap `Map.union` baseProcMap

-- | Add a constraint to the store. The constraint name can be unqualified
-- (resolved via the export map) or fully qualified.
tellConstraint :: (CHREffects es) => Types.Name -> [Value] -> Eff es ()
tellConstraint name args = do
  CHRRep procMap hc exportMap exportedSet <- getStaticRep
  let arity = length args
  resolved <- case resolveQueryConstraint' exportMap exportedSet name arity of
    Left err -> error err
    Right qname -> pure qname
  let tellName = tellProcName resolved arity
  unless (Map.member tellName procMap) $
    error ("Constraint not found: " ++ T.unpack tellName.unName)
  _ <- callProc procMap hc tellName (map RVal args)
  pure ()

-- | Name resolution extracted from 'resolveQueryConstraint' to work with
-- just a name and arity.
resolveQueryConstraint' ::
  Map Types.UnqualifiedIdentifier ExportResolution -> Set Types.QualifiedIdentifier -> Types.Name -> Int -> Either String Types.Name
resolveQueryConstraint' expMap expSet name arity = case name of
  Types.Unqualified n ->
    case Map.lookup (Types.UnqualifiedIdentifier n arity) expMap of
      Just (UniqueExport qname) -> Right qname
      Just (AmbiguousExport ms) ->
        Left
          ( "Ambiguous constraint: "
              ++ T.unpack n
              ++ "/"
              ++ show arity
              ++ ", exported by: "
              ++ intercalate ", " (map T.unpack ms)
          )
      Nothing -> Left ("Unknown constraint: " ++ T.unpack n ++ "/" ++ show arity)
  Types.Qualified m n ->
    if Set.member (Types.QualifiedIdentifier m n arity) expSet
      then Right name
      else Left ("Constraint not exported: " ++ T.unpack m ++ ":" ++ T.unpack n ++ "/" ++ show arity)

-- ---------------------------------------------------------------------------
-- Single-goal API
-- ---------------------------------------------------------------------------

-- | Resolve a query constraint against the export map.
resolveQueryConstraint :: CompiledProgram -> Constraint -> Either String Constraint
resolveQueryConstraint cp (Constraint cname cargs) = case cname of
  Types.Unqualified n ->
    let arity = length cargs
     in case Map.lookup (Types.UnqualifiedIdentifier n arity) cp.exportMap of
          Just (UniqueExport qname) ->
            Right (Constraint qname cargs)
          Just (AmbiguousExport ms) ->
            Left
              ( "Ambiguous constraint: "
                  ++ T.unpack n
                  ++ "/"
                  ++ show arity
                  ++ ", exported by: "
                  ++ intercalate ", " (map T.unpack ms)
              )
          Nothing -> Left ("Unknown constraint: " ++ T.unpack n ++ "/" ++ show arity)
  Types.Qualified m n ->
    let arity = length cargs
     in if Set.member (Types.QualifiedIdentifier m n arity) cp.exportedSet
          then Right (Constraint cname cargs)
          else Left ("Constraint not exported: " ++ T.unpack m ++ ":" ++ T.unpack n ++ "/" ++ show arity)

-- | Run a single CHR constraint against a compiled program.
runProgramWithGoalDSL :: CompiledProgram -> HostCallRegistry -> Constraint -> IO (RuntimeVal, Map Text Term)
runProgramWithGoalDSL cp hostCalls constraint = do
  resolved <- case resolveQueryConstraint cp constraint of
    Left err -> fail err
    Right c -> pure c
  let prog = cp.program
      procMap = Map.fromList [(p.name, p) | p <- prog.procedures]
      tellName = tellProcName resolved.name (length resolved.args)
  unless (Map.member tellName procMap) $
    fail ("Constraint not found: " ++ T.unpack tellName.unName)
  runEff
    . runUnify
    . fmap fst
    . runWriter @[SuspensionId]
    . runCHRStore prog.typeNames
    . runPropHistory
    . runReactQueue
    . evalState @CallStack []
    . evalState (Map.empty :: Map Text Value)
    $ do
      argVals <- traverse termToValue resolved.args
      result <- callProc procMap hostCalls tellName (map RVal argVals)
      varMap <- get
      bindings <- Map.traverseWithKey valueToTerm varMap
      pure (result, bindings)

-- | Like 'runProgramWithGoalDSL' but accepts a query as surface-language 'Text'.
runProgramWithGoal :: CompiledProgram -> HostCallRegistry -> Text -> IO (RuntimeVal, Map Text Term)
runProgramWithGoal cp hostCalls src =
  case parseConstraint "<query>" src of
    Left err -> throwIO (ParseError "<query>" err)
    Right c -> runProgramWithGoalDSL cp hostCalls c

termToValue :: (Unify :> es, State (Map Text Value) :> es) => Term -> Eff es Value
termToValue (VarTerm n) = do
  varMap <- get
  case Map.lookup n varMap of
    Just v -> pure v
    Nothing -> do
      v <- newVar
      modify (Map.insert n v)
      pure v
termToValue (IntTerm n) = pure (VInt n)
termToValue (AtomTerm s) = pure (VAtom s)
termToValue (TextTerm s) = pure (VText s)
termToValue Wildcard = pure VWildcard
termToValue (CompoundTerm (Types.Qualified m n) []) = do
  pure (VTerm ":" [VAtom m, VAtom n])
termToValue (CompoundTerm (Types.Qualified m n) ts) = do
  ts' <- traverse termToValue ts
  pure (VTerm ":" [VAtom m, VTerm n ts'])
termToValue (CompoundTerm name ts) = VTerm (vmName name).unName <$> traverse termToValue ts

-- ---------------------------------------------------------------------------
-- Multi-goal query API
-- ---------------------------------------------------------------------------

-- | Run a multi-goal query against a compiled program.
--
-- Parses the input as a comma-separated, dot-terminated list of goals,
-- renames and desugars them like rule bodies, then executes each goal.
runProgramWithQuery :: CompiledProgram -> HostCallRegistry -> Text -> IO (Map Text Term)
runProgramWithQuery cp hostCalls src =
  case parseQueryWith cp.opTable "<query>" src of
    Left err -> throwIO (ParseError "<query>" err)
    Right goals -> do
      (renamed, _renameWarnings) <- either (throwIO . RenameErrors) pure (renameQueryGoals cp.allModules goals)
      bodyGoals <- either (throwIO . DesugarErrors) pure (desugarQueryGoals cp.functionNameSet renamed)
      -- Lambda-lift query body goals and compile the generated functions
      let queryLoc = SourceLoc "<query>" 1 1
      (liftedGoals, queryLambdas) <- either (throwIO . DesugarErrors) pure (liftQueryLambdas cp.nextLambdaIndex queryLoc (Atom "") bodyGoals)
      let allFuns = cp.allFunctions ++ queryLambdas
          funSet = buildFunctionSet (D.Program [] allFuns Map.empty [])
          queryProcs = compileQueryLambdas funSet queryLambdas
          queryDispatches = genCallFunDispatches allFuns
          extraProcs = queryProcs ++ queryDispatches
      withCHRExtra cp hostCalls extraProcs $
        evalState (Map.empty :: Map Text Value) $ do
          mapM_ (executeBodyGoal hostCalls) liftedGoals
          varMap <- get
          Map.traverseWithKey valueToTerm varMap

-- | Execute a single desugared body goal in the query context.
executeBodyGoal ::
  (CHREffects es, State (Map Text Value) :> es) =>
  HostCallRegistry ->
  D.BodyGoal ->
  Eff es ()
executeBodyGoal _ D.BodyTrue = pure ()
executeBodyGoal _ (D.BodyUnify l r) = do
  v1 <- termToValue l
  v2 <- termToValue r
  CHRRep procMap hc' _ _ <- getStaticRep
  (ok, observers) <- listen (unify v1 v2)
  enqueue observers
  unless ok (raiseUnifyFailure v1 v2)
  drainReactivation procMap hc'
executeBodyGoal hc (D.BodyHostStmt f args) = do
  argVals <- traverse termToValue args
  _ <- hostCall (Map.lookup (Name f) hc) f (map RVal argVals)
  pure ()
executeBodyGoal hc (D.BodyIs v expr) = do
  result <- evalNestedExpr hc expr
  varMap <- get
  case Map.lookup v varMap of
    Just existing -> do
      CHRRep procMap hc' _ _ <- getStaticRep
      (ok, observers) <- listen (unify existing result)
      enqueue observers
      unless ok (raiseUnifyFailure existing result)
      drainReactivation procMap hc'
    Nothing -> modify (Map.insert v result)
executeBodyGoal _ (D.BodyConstraint c) = do
  argVals <- traverse termToValue c.args
  tellConstraint c.name argVals
executeBodyGoal hc (D.BodyFunctionCall (Types.Unqualified "$call") args) = do
  CHRRep procMap _ _ _ <- getStaticRep
  argVals <- traverse termToValue args
  let n = length args - 1
      dispatchName = Name ("call_" <> T.pack (show n))
  _ <- callProc procMap hc dispatchName (map RVal argVals)
  pure ()
executeBodyGoal hc (D.BodyFunctionCall name args) = do
  CHRRep procMap _ _ _ <- getStaticRep
  argVals <- traverse termToValue args
  _ <- callProc procMap hc (funcProcName name (length argVals)) (map RVal argVals)
  pure ()

-- | Raise a runtime error describing a failed unification.
raiseUnifyFailure :: (Unify :> es) => Value -> Value -> Eff es ()
raiseUnifyFailure v1 v2 = do
  t1 <- valueToTerm "_" v1
  t2 <- valueToTerm "_" v2
  error $
    "unification failure: cannot unify "
      ++ prettyTerm t1
      ++ " with "
      ++ prettyTerm t2

-- | Call a host function, failing with a clear message if not found.
hostCall :: (Unify :> es, CHRStore :> es, IOE :> es) => Maybe HostCallFn -> Text -> [RuntimeVal] -> Eff es RuntimeVal
hostCall (Just (HostCallFn f)) _ args = f args
hostCall Nothing name _ = error $ "Unknown host function: " ++ T.unpack name

-- | Drain the reactivation queue, dispatching each constraint.
drainReactivation ::
  (CHREffects es) =>
  ProcMap ->
  HostCallRegistry ->
  Eff es ()
drainReactivation procMap hc =
  drainQueue $ \sid -> do
    alive <- aliveConstraint sid
    when alive $
      void $
        callProc procMap hc (Name "reactivate_dispatch") [RConstraint sid]

-- | Evaluate a term as a nested expression (used for @is@ RHS and guard
-- expressions). Handles host calls (@host:f(args)@), user-defined function
-- calls, and data terms.
evalNestedExpr ::
  (CHREffects es, State (Map Text Value) :> es) =>
  HostCallRegistry ->
  Term ->
  Eff es Value
evalNestedExpr _ (IntTerm n) = pure (VInt n)
evalNestedExpr _ (AtomTerm s) = pure (VAtom s)
evalNestedExpr _ (TextTerm s) = pure (VText s)
evalNestedExpr _ Wildcard = pure VWildcard
evalNestedExpr _ (VarTerm v) = do
  varMap <- get
  case Map.lookup v varMap of
    Just val -> deref val
    Nothing -> do
      fresh <- newVar
      modify (Map.insert v fresh)
      pure fresh
evalNestedExpr hc (CompoundTerm (Types.Unqualified "$call") args)
  | length args >= 2 = do
      CHRRep procMap _ _ _ <- getStaticRep
      argVals <- traverse (evalNestedExpr hc) args
      let n = length args - 1
          dispatchName = Name ("call_" <> T.pack (show n))
      result <- callProc procMap hc dispatchName (map RVal argVals)
      case result of
        RVal val -> pure val
        _ -> error "call returned non-value"
evalNestedExpr hc (CompoundTerm (Types.Qualified "host" f) args) = do
  argVals <- traverse (evalNestedExpr hc) args
  result <- hostCall (Map.lookup (Name f) hc) f (map RVal argVals)
  case result of
    RVal val -> pure val
    _ -> error "host call returned non-value in expression position"
evalNestedExpr hc (CompoundTerm name args) = do
  CHRRep procMap _ _ _ <- getStaticRep
  let fnName = funcProcName name (length args)
  if Map.member fnName procMap
    then do
      argVals <- traverse (evalNestedExpr hc) args
      result <- callProc procMap hc fnName (map RVal argVals)
      case result of
        RVal val -> pure val
        _ -> error "function call returned non-value in expression position"
    else VTerm (vmName name).unName <$> traverse termToValue args

-- | Check if a name is a lambda (generated by lambda lifting).
isLambdaName :: Types.Name -> Bool
isLambdaName (Types.Qualified _ n) = T.isPrefixOf "__lambda_" n
isLambdaName (Types.Unqualified n) = T.isPrefixOf "__lambda_" n

-- | Compile lifted lambda functions for use in queries.
compileQueryLambdas :: Set Types.Identifier -> [D.Function] -> [Procedure]
compileQueryLambdas funSet lambdas =
  let (procs, _errs) = runPureEff . runWriter $ traverse (compileFunctionDef funSet) lambdas
   in procs
