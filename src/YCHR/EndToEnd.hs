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
import YCHR.Compile (CompileError, compile, procNameFor)
import YCHR.Desugar (DesugarError, desugarProgram, extractSymbolTable)
import YCHR.Meta (valueToTerm)
import YCHR.Parser (parseConstraint, parseModule, parseQuery)
import YCHR.Rename (RenameError, buildExportEnv, renameProgram)
import YCHR.Rename.Types (toListGlobal)
import YCHR.Runtime.History (PropHistory, runPropHistory)
import YCHR.Runtime.Interpreter (HostCallRegistry, callProc)
import YCHR.Runtime.Reactivation (ReactQueue, drainQueue, enqueue, runReactQueue)
import YCHR.Runtime.Store (CHRStore, aliveConstraint, runCHRStore)
import YCHR.Runtime.Types (RuntimeVal (..), SuspensionId, Value (..))
import YCHR.Runtime.Var (Unify, deref, equal, newVar, runUnify, unify)
import YCHR.StdLib (stdlib)
import YCHR.Types (Constraint (..), ConstraintType, SymbolTable, Term (..))
import YCHR.Types qualified as T
import YCHR.VM (Name (..), Procedure, Program (..), procName)

data Error
  = ParseError FilePath (ParseErrorBundle Text Void)
  | CollectErrors [CollectError]
  | RenameErrors [RenameError]
  | DesugarErrors [DesugarError]
  | CompileErrors [CompileError]
  deriving (Show)

-- | A compiled CHR program together with module visibility information.
data CompiledProgram = CompiledProgram
  { cpProgram :: Program,
    cpExportMap :: Map (Text, Int) ExportResolution,
    cpExportedSet :: Set T.Name,
    cpSymbolTable :: SymbolTable
  }

data ExportResolution
  = UniqueExport T.Name
  | AmbiguousExport [Text]
  deriving (Show, Eq)

compileModules :: [(FilePath, Text)] -> Either Error CompiledProgram
compileModules inputs = do
  parsed <- mapM (\(fp, txt) -> first (ParseError fp) (parseModule fp txt)) inputs
  collected <- first CollectErrors (collectLibraries stdlib parsed)
  let exportEnv = buildExportEnv collected
      exportMap =
        Map.fromList
          [ ((n, a), toResolution n ms)
          | ((n, a), ms) <- toListGlobal exportEnv
          ]
      exportedSet =
        Set.fromList
          [T.Qualified m n | ((n, _), ms) <- toListGlobal exportEnv, m <- ms]
  renamed <- first RenameErrors (renameProgram collected)
  desugared <- first DesugarErrors (desugarProgram renamed)
  let symTab = extractSymbolTable desugared
  prog <- first CompileErrors (compile desugared symTab)
  pure (CompiledProgram prog exportMap exportedSet symTab)
  where
    toResolution n [m] = UniqueExport (T.Qualified m n)
    toResolution _ ms = AmbiguousExport ms

compileFiles :: [FilePath] -> IO (Either Error CompiledProgram)
compileFiles paths = do
  contents <- mapM (\fp -> (fp,) <$> TIO.readFile fp) paths
  pure (compileModules contents)

-- ---------------------------------------------------------------------------
-- CHR effect
-- ---------------------------------------------------------------------------

type ProcMap = Map Name Procedure

-- | The CHR effect holds the program context needed to execute constraints.
data CHR :: Effect

type instance DispatchOf CHR = Static WithSideEffects

data instance StaticRep CHR
  = CHRRep ProcMap HostCallRegistry (Map (Text, Int) ExportResolution) (Set T.Name)

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
    . runCHRStore (progNumTypes (cpProgram cp))
    . runPropHistory
    . runReactQueue
    . fmap fst
    . runWriter @[SuspensionId]
    . evalStaticRep (CHRRep procMap hc (cpExportMap cp) (cpExportedSet cp))
  where
    procMap = Map.fromList [(procName p, p) | p <- progProcedures (cpProgram cp)]

-- | Convenience wrapper that runs a CHR session in 'IO'.
withCHR ::
  CompiledProgram ->
  HostCallRegistry ->
  (forall es. (CHREffects es) => Eff es a) ->
  IO a
withCHR cp hc action = runEff (runCHR cp hc action)

-- | Add a constraint to the store. The constraint name can be unqualified
-- (resolved via the export map) or fully qualified.
tellConstraint :: (CHREffects es) => T.Name -> [Value] -> Eff es ()
tellConstraint name args = do
  CHRRep procMap hc exportMap exportedSet <- getStaticRep
  let arity = length args
  resolved <- case resolveQueryConstraint' exportMap exportedSet name arity of
    Left err -> error err
    Right qname -> pure qname
  let tellName = procNameFor "tell" resolved
  unless (Map.member tellName procMap) $
    error ("Constraint not found: " ++ T.unpack (unName tellName))
  _ <- callProc procMap hc tellName (map RVal args)
  pure ()

-- | Name resolution extracted from 'resolveQueryConstraint' to work with
-- just a name and arity.
resolveQueryConstraint' ::
  Map (Text, Int) ExportResolution -> Set T.Name -> T.Name -> Int -> Either String T.Name
resolveQueryConstraint' exportMap exportedSet name arity = case name of
  T.Unqualified n ->
    case Map.lookup (n, arity) exportMap of
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
  T.Qualified m n ->
    if Set.member (T.Qualified m n) exportedSet
      then Right name
      else Left ("Constraint not exported: " ++ T.unpack m ++ ":" ++ T.unpack n)

-- ---------------------------------------------------------------------------
-- Single-goal API
-- ---------------------------------------------------------------------------

-- | Resolve a query constraint against the export map.
resolveQueryConstraint :: CompiledProgram -> Constraint -> Either String Constraint
resolveQueryConstraint cp (Constraint name args) = case name of
  T.Unqualified n ->
    let arity = length args
     in case Map.lookup (n, arity) (cpExportMap cp) of
          Just (UniqueExport qname) ->
            Right (Constraint qname args)
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
  T.Qualified m n ->
    if Set.member (T.Qualified m n) (cpExportedSet cp)
      then Right (Constraint name args)
      else Left ("Constraint not exported: " ++ T.unpack m ++ ":" ++ T.unpack n)

-- | Run a single CHR constraint against a compiled program.
runProgramWithGoalDSL :: CompiledProgram -> HostCallRegistry -> Constraint -> IO (RuntimeVal, Map Text Term)
runProgramWithGoalDSL cp hostCalls constraint = do
  resolved <- case resolveQueryConstraint cp constraint of
    Left err -> fail err
    Right c -> pure c
  let Program {progNumTypes, progProcedures} = cpProgram cp
      procMap = Map.fromList [(procName p, p) | p <- progProcedures]
      tellName = procNameFor "tell" (conName resolved)
  unless (Map.member tellName procMap) $
    fail ("Constraint not found: " ++ T.unpack (unName tellName))
  runEff
    . runUnify
    . fmap fst
    . runWriter @[SuspensionId]
    . runCHRStore progNumTypes
    . runPropHistory
    . runReactQueue
    . evalState (Map.empty :: Map Text Value)
    $ do
      argVals <- traverse termToValue (conArgs resolved)
      result <- callProc procMap hostCalls tellName (map RVal argVals)
      varMap <- get
      bindings <- Map.traverseWithKey valueToTerm varMap
      pure (result, bindings)

-- | Like 'runProgramWithGoalDSL' but accepts a query as surface-language 'Text'.
runProgramWithGoal :: CompiledProgram -> HostCallRegistry -> Text -> IO (RuntimeVal, Map Text Term)
runProgramWithGoal cp hostCalls src =
  case parseConstraint "<query>" src of
    Left err -> fail (show err)
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
termToValue (CompoundTerm (T.Unqualified f) ts) = VTerm f <$> traverse termToValue ts
termToValue (CompoundTerm (T.Qualified m f) ts) = VTerm (m <> ":" <> f) <$> traverse termToValue ts

-- ---------------------------------------------------------------------------
-- Multi-goal query API
-- ---------------------------------------------------------------------------

-- | Run a multi-goal query against a compiled program.
--
-- Parses the input as a comma-separated, dot-terminated list of goals
-- and interprets each goal directly.
runProgramWithQuery :: CompiledProgram -> HostCallRegistry -> Text -> IO (Map Text Term)
runProgramWithQuery cp hostCalls src =
  case parseQuery "<query>" src of
    Left err -> fail (show err)
    Right goals ->
      withCHR cp hostCalls $
        evalState (Map.empty :: Map Text Value) $ do
          mapM_ (interpretGoal hostCalls) goals
          varMap <- get
          Map.traverseWithKey valueToTerm varMap

-- | Interpret a single query goal.
interpretGoal ::
  (CHREffects es, State (Map Text Value) :> es) =>
  HostCallRegistry ->
  Term ->
  Eff es ()
interpretGoal _ (AtomTerm "true") = pure ()
interpretGoal _ (CompoundTerm (T.Unqualified "=") [l, r]) = do
  v1 <- termToValue l
  v2 <- termToValue r
  CHRRep procMap hc' _ _ <- getStaticRep
  (_, observers) <- listen (unify v1 v2)
  enqueue observers
  drainReactivation procMap hc'
interpretGoal hc (CompoundTerm (T.Unqualified "is") [VarTerm v, expr]) = do
  result <- evalTermArith hc expr
  modify (Map.insert v result)
interpretGoal hc (CompoundTerm (T.Unqualified ":=") [VarTerm v, CompoundTerm (T.Unqualified f) args]) = do
  argVals <- traverse termToValue args
  result <- liftIO (hostCall (Map.lookup (Name f) hc) f (map RVal argVals))
  case result of
    RVal val -> modify (Map.insert v val)
    _ -> error $ ":= host call returned non-value"
interpretGoal hc (CompoundTerm (T.Unqualified ":=") [T.Wildcard, CompoundTerm (T.Unqualified f) args]) = do
  argVals <- traverse termToValue args
  _ <- liftIO (hostCall (Map.lookup (Name f) hc) f (map RVal argVals))
  pure ()
interpretGoal hc (CompoundTerm (T.Unqualified "host") [CompoundTerm (T.Unqualified f) args]) = do
  argVals <- traverse termToValue args
  _ <- liftIO (hostCall (Map.lookup (Name f) hc) f (map RVal argVals))
  pure ()
interpretGoal _ term = do
  -- Treat as a constraint: extract name and args from the term.
  let (name, args) = termToConstraint term
  argVals <- traverse termToValue args
  tellConstraint name argVals

-- | Extract a constraint name and arguments from a term.
termToConstraint :: Term -> (T.Name, [Term])
termToConstraint (CompoundTerm name args) = (name, args)
termToConstraint (AtomTerm s) = (T.Unqualified s, [])
termToConstraint t = error $ "Not a valid goal: " ++ show t

-- | Call a host function, failing with a clear message if not found.
hostCall :: Maybe ([RuntimeVal] -> IO RuntimeVal) -> Text -> [RuntimeVal] -> IO RuntimeVal
hostCall (Just f) _ args = f args
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

-- | Evaluate a term as an arithmetic expression.
evalTermArith ::
  (Unify :> es, State (Map Text Value) :> es, IOE :> es) =>
  HostCallRegistry ->
  Term ->
  Eff es Value
evalTermArith _ (IntTerm n) = pure (VInt n)
evalTermArith _ (AtomTerm s) = pure (VAtom s)
evalTermArith _ (VarTerm v) = do
  varMap <- get
  case Map.lookup v varMap of
    Just val -> deref val
    Nothing -> error $ "Unbound variable in arithmetic expression: " ++ T.unpack v
evalTermArith hc (CompoundTerm (T.Unqualified op) [l, r]) = do
  lv <- evalTermArith hc l
  rv <- evalTermArith hc r
  result <- liftIO (hostCall (Map.lookup (Name op) hc) op [RVal lv, RVal rv])
  case result of
    RVal val -> pure val
    _ -> error "Arithmetic host call returned non-value"
evalTermArith _ t = error $ "Unsupported arithmetic expression: " ++ show t
