{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module YCHR.EndToEnd
  ( -- * Compilation
    Error (..),
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
import YCHR.Collect (CollectError, collectLibraries)
import YCHR.Compile (CompileError, compile, funcProcName, tellProcName)
import YCHR.Desugar (DesugarError, desugarProgram, desugarQueryGoals, extractSymbolTable)
import YCHR.Desugared qualified as D
import YCHR.Meta (valueToTerm)
import YCHR.Parsed (Import (..), Module (..), OpDecl (..), noAnn)
import YCHR.Parser (OpTable, builtinOps, collectOperatorDecls, extractOpDecls, mergeOps, parseConstraint, parseModuleWith, parseQueryWith)
import YCHR.Rename (RenameError, buildExportEnv, renameProgram, renameQueryGoals)
import YCHR.Rename.Types (toListExport)
import YCHR.Runtime.History (PropHistory, runPropHistory)
import YCHR.Runtime.Interpreter (HostCallFn (..), HostCallRegistry, callProc)
import YCHR.Runtime.Reactivation (ReactQueue, drainQueue, enqueue, runReactQueue)
import YCHR.Runtime.Store (CHRStore, aliveConstraint, runCHRStore)
import YCHR.Runtime.Types (RuntimeVal (..), SuspensionId, Value (..))
import YCHR.Runtime.Var (Unify, deref, equal, newVar, runUnify, unify)
import YCHR.StdLib (stdlib)
import YCHR.Types (Constraint (..), ConstraintType, SymbolTable, Term (..))
import YCHR.Types qualified as Types
import YCHR.VM (Name (..), Procedure (..), Program (..))

data Error
  = ParseError FilePath (ParseErrorBundle Text Void)
  | CollectErrors [CollectError]
  | RenameErrors [RenameError]
  | DesugarErrors [DesugarError]
  | CompileErrors [CompileError]
  | OperatorConflict [FilePath] Text
  deriving (Show)

instance Exception Error

-- | A compiled CHR program together with module visibility information.
data CompiledProgram = CompiledProgram
  { program :: Program,
    exportMap :: Map (Text, Int) ExportResolution,
    exportedSet :: Set Types.Identifier,
    symbolTable :: SymbolTable,
    allModules :: [Module],
    opTable :: OpTable
  }

data ExportResolution
  = UniqueExport Types.Name
  | AmbiguousExport [Text]
  deriving (Show, Eq)

compileModules :: Bool -> [(FilePath, Text)] -> Either Error CompiledProgram
compileModules includeStdlib inputs = do
  -- Collect operators from user sources (lightweight first pass)
  userOpsByFile <-
    first (\(fp, e) -> ParseError fp e) $
      traverse (\(fp, src) -> (fp,) <$> first' (fp,) (collectOperatorDecls fp src)) inputs
  let userOps = concatMap snd userOpsByFile
  -- Collect operators from all stdlib modules (already parsed by TH).
  -- Always include these since builtins are auto-imported regardless of
  -- includeStdlib, and extra syntactic operators don't affect correctness.
  let stdlibOps = concatMap extractOpDecls (Map.elems stdlib)
  -- Merge all operators into one table
  table <- case mergeOps builtinOps (userOps ++ stdlibOps) of
    Left conflict ->
      let sources = [fp | (fp, ops) <- userOpsByFile, any (\(OpDecl {opName}) -> opName == conflict) ops]
       in Left (OperatorConflict sources conflict)
    Right t -> Right t
  -- Full parse user modules with the merged operator table
  parsed <-
    traverse
      (\(fp, src) -> first (ParseError fp) (parseModuleWith table fp src))
      inputs
  let withBuiltins = map addBuiltinsImport parsed
  collected <- first CollectErrors (collectLibraries includeStdlib stdlib withBuiltins)
  let exportEnv = buildExportEnv collected
      exportMap =
        Map.fromList
          [ ((n, a), toResolution n ms)
          | ((n, a), ms) <- toListExport exportEnv
          ]
      exportedSet =
        Set.fromList
          [Types.Identifier (Types.Qualified m n) a | ((n, a), ms) <- toListExport exportEnv, m <- ms]
  renamed <- first RenameErrors (renameProgram collected)
  desugared <- first DesugarErrors (desugarProgram renamed)
  let symTab = extractSymbolTable desugared
  prog <- first CompileErrors (compile desugared symTab)
  pure (CompiledProgram prog exportMap exportedSet symTab collected table)
  where
    first' f (Left e) = Left (f e)
    first' _ (Right x) = Right x
    toResolution n [m] = UniqueExport (Types.Qualified m n)
    toResolution _ ms = AmbiguousExport ms

addBuiltinsImport :: Module -> Module
addBuiltinsImport m = m {imports = noAnn (LibraryImport "builtins") : m.imports}

compileFiles :: Bool -> [FilePath] -> IO (Either Error CompiledProgram)
compileFiles includeStdlib paths = do
  contents <- mapM (\fp -> (fp,) <$> TIO.readFile fp) paths
  pure (compileModules includeStdlib contents)

-- ---------------------------------------------------------------------------
-- CHR effect
-- ---------------------------------------------------------------------------

type ProcMap = Map Name Procedure

-- | The CHR effect holds the program context needed to execute constraints.
data CHR :: Effect

type instance DispatchOf CHR = Static WithSideEffects

data instance StaticRep CHR
  = CHRRep ProcMap HostCallRegistry (Map (Text, Int) ExportResolution) (Set Types.Identifier)

-- | Shorthand for the full set of effects available inside a CHR session.
type CHREffects es =
  ( CHR :> es,
    Unify :> es,
    CHRStore :> es,
    PropHistory :> es,
    ReactQueue :> es,
    Writer [SuspensionId] :> es,
    IOE :> es
  )

-- | Set up a CHR session for a compiled program. All runtime state (constraint
-- store, propagation history, reactivation queue, unification variables) is
-- initialised and persists for the duration of the computation.
runCHR ::
  (IOE :> es) =>
  CompiledProgram ->
  HostCallRegistry ->
  Eff (CHR : Writer [SuspensionId] : ReactQueue : PropHistory : CHRStore : Unify : es) a ->
  Eff es a
runCHR cp hc =
  runUnify
    . runCHRStore cp.program.numTypes
    . runPropHistory
    . runReactQueue
    . fmap fst
    . runWriter @[SuspensionId]
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
  Map (Text, Int) ExportResolution -> Set Types.Identifier -> Types.Name -> Int -> Either String Types.Name
resolveQueryConstraint' expMap expSet name arity = case name of
  Types.Unqualified n ->
    case Map.lookup (n, arity) expMap of
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
    if Set.member (Types.Identifier (Types.Qualified m n) arity) expSet
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
     in case Map.lookup (n, arity) cp.exportMap of
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
     in if Set.member (Types.Identifier (Types.Qualified m n) arity) cp.exportedSet
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
    . runCHRStore prog.numTypes
    . runPropHistory
    . runReactQueue
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
termToValue (CompoundTerm (Types.Unqualified f) ts) = VTerm f <$> traverse termToValue ts
termToValue (CompoundTerm (Types.Qualified m f) ts) = VTerm (m <> ":" <> f) <$> traverse termToValue ts

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
      renamed <- either (throwIO . RenameErrors) pure (renameQueryGoals cp.allModules goals)
      bodyGoals <- either (throwIO . DesugarErrors) pure (desugarQueryGoals cp.allModules renamed)
      withCHR cp hostCalls $
        evalState (Map.empty :: Map Text Value) $ do
          mapM_ (executeBodyGoal hostCalls) bodyGoals
          varMap <- get
          Map.traverseWithKey valueToTerm varMap

-- | Execute a single desugared body goal in the query context.
executeBodyGoal ::
  (CHREffects es, State (Map Text Value) :> es) =>
  HostCallRegistry ->
  D.BodyGoal ->
  Eff es ()
executeBodyGoal _ (D.BodyCommon D.GoalTrue) = pure ()
executeBodyGoal _ (D.BodyUnify l r) = do
  v1 <- termToValue l
  v2 <- termToValue r
  CHRRep procMap hc' _ _ <- getStaticRep
  (_, observers) <- listen (unify v1 v2)
  enqueue observers
  drainReactivation procMap hc'
executeBodyGoal hc (D.BodyHostStmt f args) = do
  argVals <- traverse termToValue args
  _ <- hostCall (Map.lookup (Name f) hc) f (map RVal argVals)
  pure ()
executeBodyGoal hc (D.BodyIs v expr) = do
  result <- evalTermArith hc expr
  varMap <- get
  case Map.lookup v varMap of
    Just existing -> do
      CHRRep procMap hc' _ _ <- getStaticRep
      (_, observers) <- listen (unify existing result)
      enqueue observers
      drainReactivation procMap hc'
    Nothing -> modify (Map.insert v result)
executeBodyGoal _ (D.BodyConstraint c) = do
  argVals <- traverse termToValue c.args
  tellConstraint c.name argVals
executeBodyGoal hc (D.BodyFunctionCall name args) = do
  CHRRep procMap _ _ _ <- getStaticRep
  argVals <- traverse termToValue args
  _ <- callProc procMap hc (funcProcName name (length argVals)) (map RVal argVals)
  pure ()

-- | Call a host function, failing with a clear message if not found.
hostCall :: (Unify :> es, IOE :> es) => Maybe HostCallFn -> Text -> [RuntimeVal] -> Eff es RuntimeVal
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

-- | Evaluate a term as an arithmetic expression (used for @is@ RHS).
-- Handles host calls (@host:f(args)@), user-defined function calls, and data terms.
evalTermArith ::
  (CHREffects es, State (Map Text Value) :> es) =>
  HostCallRegistry ->
  Term ->
  Eff es Value
evalTermArith _ (IntTerm n) = pure (VInt n)
evalTermArith _ (AtomTerm s) = pure (VAtom s)
evalTermArith _ (TextTerm s) = pure (VText s)
evalTermArith _ Wildcard = pure VWildcard
evalTermArith _ (VarTerm v) = do
  varMap <- get
  case Map.lookup v varMap of
    Just val -> deref val
    Nothing -> do
      fresh <- newVar
      modify (Map.insert v fresh)
      pure fresh
evalTermArith hc (CompoundTerm (Types.Qualified "host" f) args) = do
  argVals <- traverse (evalTermArith hc) args
  result <- hostCall (Map.lookup (Name f) hc) f (map RVal argVals)
  case result of
    RVal val -> pure val
    _ -> error "host call returned non-value in expression position"
evalTermArith hc (CompoundTerm name args) = do
  CHRRep procMap _ _ _ <- getStaticRep
  argVals <- traverse (evalTermArith hc) args
  let fnName = funcProcName name (length argVals)
  if Map.member fnName procMap
    then do
      result <- callProc procMap hc fnName (map RVal argVals)
      case result of
        RVal val -> pure val
        _ -> error "function call returned non-value in expression position"
    else pure $ VTerm (termFunctor name) argVals
  where
    termFunctor (Types.Qualified m n) = m <> ":" <> n
    termFunctor (Types.Unqualified n) = n
