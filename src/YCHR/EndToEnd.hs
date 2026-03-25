{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module YCHR.EndToEnd
  ( -- * Compilation
    Error (..),
    CompiledProgram (..),
    ExportResolution (..),
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
  )
where

import Control.Monad (unless)
import Data.Bifunctor (first)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text.IO qualified as TIO
import Data.Void (Void)
import Effectful
import Effectful.Dispatch.Static
import Effectful.State.Static.Local (State, evalState, get, modify)
import Effectful.Writer.Static.Local (Writer, runWriter)
import Text.Megaparsec (ParseErrorBundle)
import YCHR.Compile (CompileError, compile, procNameFor)
import YCHR.Desugar (DesugarError, desugarProgram, extractSymbolTable)
import YCHR.Parser (parseConstraint, parseModule)
import YCHR.Rename (RenameError, buildExportEnv, renameProgram)
import YCHR.Runtime.History (PropHistory, runPropHistory)
import YCHR.Runtime.Interpreter (HostCallRegistry, callProc)
import YCHR.Runtime.Reactivation (ReactQueue, runReactQueue)
import YCHR.Runtime.Store (CHRStore, runCHRStore)
import YCHR.Runtime.Types (RuntimeVal (..), SuspensionId, Value (..))
import YCHR.Runtime.Var (Unify, deref, equal, newVar, runUnify, unify)
import YCHR.Types (Constraint (..), Term (..))
import YCHR.Types qualified as T
import YCHR.VM (Name (..), Procedure, Program (..), procName)

data Error
  = ParseError FilePath (ParseErrorBundle Text Void)
  | RenameErrors [RenameError]
  | DesugarErrors [DesugarError]
  | CompileErrors [CompileError]
  deriving (Show)

-- | A compiled CHR program together with module visibility information.
data CompiledProgram = CompiledProgram
  { cpProgram :: Program,
    cpExportMap :: Map (String, Int) ExportResolution,
    cpExportedSet :: Set T.Name
  }

data ExportResolution
  = UniqueExport T.Name
  | AmbiguousExport [String]
  deriving (Show, Eq)

compileModules :: [(FilePath, Text)] -> Either Error CompiledProgram
compileModules inputs = do
  parsed <- mapM (\(fp, txt) -> first (ParseError fp) (parseModule fp txt)) inputs
  let exportEnv = buildExportEnv parsed
      exportMap =
        Map.fromList
          [ ((n, a), toResolution n ms)
          | ((n, a), ms) <- Map.toList exportEnv
          ]
      exportedSet =
        Set.fromList
          [T.Qualified m n | ((n, _), ms) <- Map.toList exportEnv, m <- ms]
  renamed <- first RenameErrors (renameProgram parsed)
  desugared <- first DesugarErrors (desugarProgram renamed)
  let symTab = extractSymbolTable desugared
  prog <- first CompileErrors (compile desugared symTab)
  pure (CompiledProgram prog exportMap exportedSet)
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
  = CHRRep ProcMap HostCallRegistry (Map (String, Int) ExportResolution) (Set T.Name)

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
    error ("Constraint not found: " ++ unName tellName)
  _ <- callProc procMap hc tellName (map RVal args)
  pure ()

-- | Name resolution extracted from 'resolveQueryConstraint' to work with
-- just a name and arity.
resolveQueryConstraint' ::
  Map (String, Int) ExportResolution -> Set T.Name -> T.Name -> Int -> Either String T.Name
resolveQueryConstraint' exportMap exportedSet name arity = case name of
  T.Unqualified n ->
    case Map.lookup (n, arity) exportMap of
      Just (UniqueExport qname) -> Right qname
      Just (AmbiguousExport ms) ->
        Left
          ( "Ambiguous constraint: "
              ++ n
              ++ "/"
              ++ show arity
              ++ ", exported by: "
              ++ intercalate ", " ms
          )
      Nothing -> Left ("Unknown constraint: " ++ n ++ "/" ++ show arity)
  T.Qualified m n ->
    if Set.member (T.Qualified m n) exportedSet
      then Right name
      else Left ("Constraint not exported: " ++ m ++ ":" ++ n)

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
                  ++ n
                  ++ "/"
                  ++ show arity
                  ++ ", exported by: "
                  ++ intercalate ", " ms
              )
          Nothing -> Left ("Unknown constraint: " ++ n ++ "/" ++ show arity)
  T.Qualified m n ->
    if Set.member (T.Qualified m n) (cpExportedSet cp)
      then Right (Constraint name args)
      else Left ("Constraint not exported: " ++ m ++ ":" ++ n)

-- | Run a single CHR constraint against a compiled program.
runProgramWithGoalDSL :: CompiledProgram -> HostCallRegistry -> Constraint -> IO (RuntimeVal, Map String Term)
runProgramWithGoalDSL cp hostCalls constraint = do
  resolved <- case resolveQueryConstraint cp constraint of
    Left err -> fail err
    Right c -> pure c
  let Program {progNumTypes, progProcedures} = cpProgram cp
      procMap = Map.fromList [(procName p, p) | p <- progProcedures]
      tellName = procNameFor "tell" (conName resolved)
  unless (Map.member tellName procMap) $
    fail ("Constraint not found: " ++ unName tellName)
  runEff
    . runUnify
    . fmap fst
    . runWriter @[SuspensionId]
    . runCHRStore progNumTypes
    . runPropHistory
    . runReactQueue
    . evalState (Map.empty :: Map String Value)
    $ do
      argVals <- traverse termToValue (conArgs resolved)
      result <- callProc procMap hostCalls tellName (map RVal argVals)
      varMap <- get
      bindings <- Map.traverseWithKey valueToTerm varMap
      pure (result, bindings)

-- | Like 'runProgramWithGoalDSL' but accepts a query as surface-language 'Text'.
runProgramWithGoal :: CompiledProgram -> HostCallRegistry -> Text -> IO (RuntimeVal, Map String Term)
runProgramWithGoal cp hostCalls src =
  case parseConstraint "<query>" src of
    Left err -> fail (show err)
    Right c -> runProgramWithGoalDSL cp hostCalls c

termToValue :: (Unify :> es, State (Map String Value) :> es) => Term -> Eff es Value
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
termToValue Wildcard = pure VWildcard
termToValue (CompoundTerm (T.Unqualified f) ts) = VTerm f <$> traverse termToValue ts
termToValue (CompoundTerm (T.Qualified m f) ts) = VTerm (m ++ ":" ++ f) <$> traverse termToValue ts

valueToTerm :: (Unify :> es) => String -> Value -> Eff es Term
valueToTerm varName v = do
  v' <- deref v
  case v' of
    VInt n -> pure (IntTerm n)
    VAtom s -> pure (AtomTerm s)
    VBool True -> pure (AtomTerm "true")
    VBool False -> pure (AtomTerm "false")
    VWildcard -> pure Wildcard
    VTerm f ts -> CompoundTerm (T.Unqualified f) <$> traverse (valueToTerm "_") ts
    VVar _ -> pure (VarTerm varName)
