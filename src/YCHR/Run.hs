{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Top-level orchestration: compile a program, then run goals or
-- multi-goal queries against it. The CHR session machinery lives in
-- "YCHR.Runtime.Session"; the compilation pipeline lives in
-- "YCHR.Compile.Pipeline". This module ties the two together and
-- adds the query-time goal evaluator used by 'runProgramWithQuery'
-- and the live REPL session in "YCHR.Repl".
module YCHR.Run
  ( -- * Compilation (re-exported from "YCHR.Compile.Pipeline")
    Error (..),
    Warning (..),
    CompiledProgram (..),
    ExportResolution (..),
    ConstraintType,
    compileModules,
    compileFiles,
    compileParsedModules,

    -- * CHR session (re-exported from "YCHR.Runtime.Session")
    Chr,
    withCHR,
    toSessionInput,
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
    prepareGoal,
    runPreparedGoal,

    -- * Multi-goal query API
    PreparedQuery (..),
    prepareQuery,
    executePreparedQuery,
    runProgramWithQuery,
  )
where

import Control.Exception (handle, throwIO)
import Control.Monad (unless, void, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ask, runReaderT)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, modify)
import Control.Monad.Trans.Writer.CPS (runWriter)
import Data.IORef (readIORef)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Compile
  ( buildFunctionSet,
    compileFunctionDef,
    funcProcName,
    genCallFunDispatches,
    tellProcName,
    vmName,
  )
import YCHR.Compile.Pipeline
  ( CompiledProgram (..),
    Error (..),
    ExportResolution (..),
    Warning (..),
    compileFiles,
    compileModules,
    compileParsedModules,
  )
import YCHR.Desugar (desugarQueryGoals, liftQueryLambdas)
import YCHR.Desugared qualified as D
import YCHR.Meta (valueToTerm)
import YCHR.PExpr (PExpr (Atom))
import YCHR.Parsed (SourceLoc (..))
import YCHR.Parser (parseConstraint, parseQueryWith)
import YCHR.Pretty (prettyTerm)
import YCHR.Rename (renameQueryArgs, renameQueryGoals)
import YCHR.Runtime.Error (RuntimeErrorThrown (..))
import YCHR.Runtime.Interpreter (HostCallFn (..), HostCallRegistry, callProc)
import YCHR.Runtime.Monad (Chr, SessionEnv (..))
import YCHR.Runtime.Reactivation (drainQueue, enqueue)
import YCHR.Runtime.Session
  ( tellConstraint,
    toSessionInput,
    withCHR,
    withCHRExtra,
  )
import YCHR.Runtime.Store (aliveConstraint)
import YCHR.Runtime.Types (CallVal (..), Value (..), VarId)
import YCHR.Runtime.Var (deref, equal, getVarId, newVar, unify)
import YCHR.TypeCheck (typeCheckGoals)
import YCHR.Types (Constraint (..), ConstraintType, Term (..))
import YCHR.Types qualified as Types
import YCHR.VM (Name (..), Procedure (..), Program (..))

-- ---------------------------------------------------------------------------
-- Single-goal API
-- ---------------------------------------------------------------------------

-- | Resolve a query constraint against the export map. The resolved
-- form is a 'Types.QualifiedConstraint' since name resolution always
-- produces a fully-qualified name.
resolveQueryConstraint ::
  CompiledProgram ->
  Constraint ->
  Either String Types.QualifiedConstraint
resolveQueryConstraint cp (Constraint cname cargs) = case cname of
  Types.Unqualified n ->
    let arity = length cargs
     in case Map.lookup (Types.UnqualifiedIdentifier n arity) cp.exportMap of
          Just (UniqueExport (Types.Qualified m b)) ->
            Right (Types.QualifiedConstraint (Types.QualifiedName m b) cargs)
          Just (UniqueExport (Types.Unqualified _)) ->
            Left ("Unqualified export resolution for " ++ T.unpack n)
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
          then Right (Types.QualifiedConstraint (Types.QualifiedName m n) cargs)
          else
            Left
              ( "Constraint not exported: "
                  ++ T.unpack m
                  ++ ":"
                  ++ T.unpack n
                  ++ "/"
                  ++ show arity
              )

-- | Run a single CHR constraint against a compiled program.
runProgramWithGoalDSL ::
  CompiledProgram ->
  HostCallRegistry ->
  Constraint ->
  IO (Value, Map Text Term)
runProgramWithGoalDSL cp hostCalls constraint = convertRuntimeError $ do
  resolved <- case resolveQueryConstraint cp constraint of
    Left err -> fail err
    Right c -> pure c
  let procMap = Map.fromList [(p.name, p) | p <- cp.program.procedures]
      tellName = tellProcName (Types.qualifiedToName resolved.name) (length resolved.args)
  unless (Map.member tellName procMap) $
    fail ("Constraint not found: " ++ T.unpack tellName.unName)
  withCHR (toSessionInput cp) hostCalls $
    evalStateT (runConstraintAndCollect tellName resolved) Map.empty

runConstraintAndCollect ::
  Name ->
  Types.QualifiedConstraint ->
  StateT (Map Text Value) Chr (Value, Map Text Term)
runConstraintAndCollect tellName resolved = do
  argVals <- traverse termToValue resolved.args
  result <- lift (callProc tellName (map CVal argVals))
  varMap <- get
  classes <- lift (buildAliasClasses varMap)
  bindings <-
    lift $
      Map.traverseWithKey
        (\k v -> valueToTerm (perKeyAliases classes k) v)
        varMap
  pure (result, bindings)

-- | Re-throw 'RuntimeErrorThrown' (from the runtime layer) as the
-- user-facing 'RuntimeError' constructor of 'Error'. Applied at the
-- top-level IO entry points so callers can pattern-match a single
-- exception type ('Error') without depending on the runtime's
-- internal exception.
convertRuntimeError :: IO a -> IO a
convertRuntimeError = handle $ \(RuntimeErrorThrown msg stack) ->
  throwIO (RuntimeError msg stack)

-- | 'Chr'-flavored version of 'convertRuntimeError', applied at the
-- 'executePreparedQuery' boundary so the REPL's catch helpers see a
-- uniform 'Error' value regardless of which path raised it.
convertRuntimeErrorChr :: Chr a -> Chr a
convertRuntimeErrorChr m = do
  env <- ask
  liftIO $
    handle (\(RuntimeErrorThrown msg stack) -> throwIO (RuntimeError msg stack)) $
      runReaderT m env

-- | Parse and rename a goal, returning the canonicalized 'Constraint'
-- alongside any rename warnings. Throws on parse or rename errors.
-- Splitting this out lets the CLI surface goal-argument warnings before
-- the goal runs (notably for @--Werror@).
prepareGoal :: CompiledProgram -> Text -> IO (Constraint, [Warning])
prepareGoal cp src = case parseConstraint "<query>" src of
  Left err -> throwIO (ParseError "<query>" err)
  Right (Left validErr) -> throwIO (ParseValidationErrors [validErr])
  Right (Right (Constraint cname cargs)) -> do
    (renamedArgs, ws) <-
      either
        (throwIO . RenameErrors)
        pure
        (renameQueryArgs cp.allModules cargs)
    let warnings = [RenameWarnings ws | not (null ws)]
    pure (Constraint cname renamedArgs, warnings)

-- | Type-check and run a previously prepared single-goal constraint.
-- Throws 'TypeErrors' on goal-time type errors.
runPreparedGoal ::
  CompiledProgram ->
  HostCallRegistry ->
  Constraint ->
  IO (Value, Map Text Term)
runPreparedGoal cp hostCalls original = do
  tcErrs <- case resolveQueryConstraint cp original of
    Right qc ->
      typeCheckGoals
        cp.desugaredProgram
        (SourceLoc "<query>" 1 1)
        (Just "query")
        [D.BodyConstraint qc]
    Left _ -> pure []
  unless (null tcErrs) (throwIO (TypeErrors tcErrs))
  runProgramWithGoalDSL cp hostCalls original

-- | Like 'runProgramWithGoalDSL' but accepts a query as surface-language 'Text'.
runProgramWithGoal ::
  CompiledProgram ->
  HostCallRegistry ->
  Text ->
  IO (Value, Map Text Term)
runProgramWithGoal cp hostCalls src = do
  (constraint, _ws) <- prepareGoal cp src
  runPreparedGoal cp hostCalls constraint

-- ---------------------------------------------------------------------------
-- Multi-goal query API
-- ---------------------------------------------------------------------------

-- | Result of parsing, desugaring, lambda-lifting, and type-checking
-- a query — everything that can be done before entering the CHR effect
-- stack. 'queryLambdas' is non-empty iff the query introduced anonymous
-- @fun(...) -> ... end@ expressions; 'extraProcs' must be added to the
-- 'ProcMap' before executing the query.
data PreparedQuery = PreparedQuery
  { liftedGoals :: [D.BodyGoal],
    queryLambdas :: [D.Function],
    extraProcs :: [Procedure]
  }

-- | Parse, rename, desugar, lambda-lift, and type-check a query.
prepareQuery :: CompiledProgram -> Text -> IO (PreparedQuery, [Warning])
prepareQuery cp src = do
  goals <-
    either
      (throwIO . ParseError "<query>")
      pure
      ( parseQueryWith
          cp.opTable
          "<query>"
          src
      )
  (renamed, renameWs) <-
    either
      (throwIO . RenameErrors)
      pure
      ( renameQueryGoals
          cp.allModules
          goals
      )
  bodyGoals <-
    either
      (throwIO . DesugarErrors)
      pure
      ( desugarQueryGoals
          cp.functionNameSet
          renamed
      )
  let queryLoc = SourceLoc "<query>" 1 1
  (lifted, lambdas) <-
    either
      (throwIO . DesugarErrors)
      pure
      ( liftQueryLambdas
          cp.nextLambdaIndex
          queryLoc
          (Atom "")
          bodyGoals
      )
  let cdp = cp.desugaredProgram
      progForCheck =
        D.Program
          { rules = cdp.rules,
            functions = cdp.functions ++ lambdas,
            constraintTypes = cdp.constraintTypes,
            constraintBounds = cdp.constraintBounds,
            typeDefinitions = cdp.typeDefinitions
          }
  tcErrs <- typeCheckGoals progForCheck queryLoc (Just "query") lifted
  unless (null tcErrs) (throwIO (TypeErrors tcErrs))
  let allFuns = cp.allFunctions ++ lambdas
      funSet =
        buildFunctionSet
          ( D.Program
              { rules = [],
                functions = allFuns,
                constraintTypes = Map.empty,
                constraintBounds = Map.empty,
                typeDefinitions = []
              }
          )
      queryProcs = compileQueryLambdas funSet lambdas
      queryDispatches = genCallFunDispatches allFuns
      warnings = [RenameWarnings renameWs | not (null renameWs)]
  pure
    ( PreparedQuery
        { liftedGoals = lifted,
          queryLambdas = lambdas,
          extraProcs = queryProcs ++ queryDispatches
        },
      warnings
    )

-- | Execute the lifted goals of a 'PreparedQuery' inside an existing CHR
-- session. Opens its own per-query variable scope and returns the
-- resulting bindings. The host-call registry is read from the ambient
-- 'SessionEnv'; the action only needs the goals.
executePreparedQuery :: [D.BodyGoal] -> Chr (Map Text Term)
executePreparedQuery lifted =
  convertRuntimeErrorChr $
    evalStateT
      ( do
          mapM_ executeBodyGoal lifted
          varMap <- get
          classes <- lift (buildAliasClasses varMap)
          lift $
            Map.traverseWithKey
              (\k v -> valueToTerm (perKeyAliases classes k) v)
              varMap
      )
      (Map.empty :: Map Text Value)

-- | Group the user-visible query variables by their underlying
-- 'VarId'. See module-internal explanation in 'perKeyAliases'.
buildAliasClasses :: Map Text Value -> Chr (Map VarId [Text])
buildAliasClasses varMap = do
  pairs <- traverse vidOf (Map.toAscList varMap)
  pure $ Map.fromListWith (flip (++)) [(vid, [k]) | (k, Just vid) <- pairs]
  where
    vidOf (k, v)
      | "_" `T.isPrefixOf` k = pure (k, Nothing)
      | otherwise = do
          mvid <- getVarId v
          pure (k, mvid)

-- | Build the 'VarId' → display name map that 'valueToTerm' should
-- use when printing the binding for surface variable @k@.
perKeyAliases :: Map VarId [Text] -> Text -> Map VarId Text
perKeyAliases classes k = Map.mapMaybe pick classes
  where
    pick [] = Nothing
    pick [_] = Nothing
    pick names@(canonical : _) = Just $ case break (== k) names of
      (_, _ : next : _) -> next
      (_, [_]) -> canonical
      (_, []) -> canonical

-- | Run a multi-goal query against a compiled program.
runProgramWithQuery :: CompiledProgram -> HostCallRegistry -> Text -> IO (Map Text Term)
runProgramWithQuery cp hostCalls src = do
  (prep, _ws) <- prepareQuery cp src
  withCHRExtra (toSessionInput cp) hostCalls prep.extraProcs $
    executePreparedQuery prep.liftedGoals

-- ---------------------------------------------------------------------------
-- Query goal evaluator (internal)
-- ---------------------------------------------------------------------------

type QueryM = StateT (Map Text Value) Chr

-- | Resolve a surface 'Term' to a 'Value' inside the per-query
-- variable scope, allocating a fresh logical variable for each new
-- 'VarTerm' the query introduces.
termToValue :: Term -> QueryM Value
termToValue (VarTerm n) = do
  varMap <- get
  case Map.lookup n varMap of
    Just v -> pure v
    Nothing -> do
      v <- lift newVar
      modify (Map.insert n v)
      pure v
termToValue (IntTerm n) = pure (VInt n)
termToValue (FloatTerm n) = pure (VFloat n)
termToValue (AtomTerm s) = pure (VAtom s)
termToValue (TextTerm s) = pure (VText s)
termToValue Wildcard = pure VWildcard
termToValue (CompoundTerm name@(Types.Qualified _ _) ts) = do
  ts' <- traverse termToValue ts
  pure (VTerm (vmName name).unName ts')
termToValue (CompoundTerm name ts) = VTerm (vmName name).unName <$> traverse termToValue ts

-- | Execute a single desugared body goal in the query context.
executeBodyGoal :: D.BodyGoal -> QueryM ()
executeBodyGoal D.BodyTrue = pure ()
executeBodyGoal (D.BodyUnify l r) = do
  v1 <- termToValue l
  v2 <- termToValue r
  (ok, observers) <- lift (unify v1 v2)
  lift (enqueue observers)
  unless ok (lift (raiseUnifyFailure v1 v2))
  lift drainReactivation
executeBodyGoal (D.BodyHostStmt f args) = do
  argVals <- traverse termToValue args
  env <- lift ask
  _ <- lift (hostCall (Map.lookup (Name f) env.hostCalls) f argVals)
  pure ()
executeBodyGoal (D.BodyIs v expr) = do
  result <- evalNestedExpr expr
  varMap <- get
  case Map.lookup v varMap of
    Just existing -> do
      (ok, observers) <- lift (unify existing result)
      lift (enqueue observers)
      unless ok (lift (raiseUnifyFailure existing result))
      lift drainReactivation
    Nothing -> modify (Map.insert v result)
executeBodyGoal (D.BodyConstraint c) = do
  argVals <- traverse termToValue c.args
  lift (tellConstraint (Types.qualifiedToName c.name) argVals)
executeBodyGoal (D.BodyFunctionCall (Types.Unqualified "$call") args) = do
  argVals <- traverse termToValue args
  let n = length args - 1
      dispatchName = Name ("call_" <> T.pack (show n))
  _ <- lift (callProc dispatchName (map CVal argVals))
  pure ()
executeBodyGoal (D.BodyFunctionCall name args) = do
  argVals <- traverse termToValue args
  _ <- lift (callProc (funcProcName name (length argVals)) (map CVal argVals))
  pure ()

-- | Raise a runtime error describing a failed unification.
raiseUnifyFailure :: Value -> Value -> Chr ()
raiseUnifyFailure v1 v2 = do
  t1 <- valueToTerm Map.empty v1
  t2 <- valueToTerm Map.empty v2
  error $
    "unification failure: cannot unify "
      ++ prettyTerm t1
      ++ " with "
      ++ prettyTerm t2

-- | Call a host function, failing with a clear message if not found.
hostCall :: Maybe HostCallFn -> Text -> [Value] -> Chr Value
hostCall (Just (HostCallFn f)) _ args = f args
hostCall Nothing name _ = error $ "Unknown host function: " ++ T.unpack name

-- | Drain the reactivation queue, dispatching each constraint.
drainReactivation :: Chr ()
drainReactivation =
  drainQueue $ \sid -> do
    alive <- aliveConstraint sid
    when alive $
      void $
        callProc (Name "reactivate_dispatch") [CId sid]

-- | Evaluate a term as a nested expression (used for @is@ RHS and guard
-- expressions). Handles host calls (@host:f(args)@), user-defined function
-- calls, @term(X)@ (quoting), and data terms.
evalNestedExpr :: Term -> QueryM Value
evalNestedExpr (IntTerm n) = pure (VInt n)
evalNestedExpr (FloatTerm n) = pure (VFloat n)
evalNestedExpr (AtomTerm s) = pure (VAtom s)
evalNestedExpr (TextTerm s) = pure (VText s)
evalNestedExpr Wildcard = pure VWildcard
evalNestedExpr (VarTerm v) = do
  varMap <- get
  case Map.lookup v varMap of
    Just val -> lift (deref val)
    Nothing -> do
      fresh <- lift newVar
      modify (Map.insert v fresh)
      pure fresh
evalNestedExpr (CompoundTerm (Types.Unqualified "$call") args)
  | length args >= 2 = do
      argVals <- traverse evalNestedExpr args
      let n = length args - 1
          dispatchName = Name ("call_" <> T.pack (show n))
      lift (callProc dispatchName (map CVal argVals))
evalNestedExpr (CompoundTerm (Types.Unqualified "term") [arg]) =
  termToValue arg
evalNestedExpr (CompoundTerm (Types.Qualified "host" f) args) = do
  argVals <- traverse evalNestedExpr args
  env <- lift ask
  lift (hostCall (Map.lookup (Name f) env.hostCalls) f argVals)
evalNestedExpr (CompoundTerm name args) = do
  env <- lift ask
  pm <- liftIO (readIORef env.procMap)
  let fnName = funcProcName name (length args)
  if Map.member fnName pm
    then do
      argVals <- traverse evalNestedExpr args
      lift (callProc fnName (map CVal argVals))
    else VTerm (vmName name).unName <$> traverse termToValue args

-- | Compile lifted query lambdas into VM procedures. Discards the
-- error channel: by the time this runs, 'prepareQuery' has already
-- lifted these lambdas from a desugared program that compiled
-- cleanly and has type-checked them, so any error here would
-- indicate a compiler bug rather than a user problem.
compileQueryLambdas :: Set Types.Identifier -> [D.Function] -> [Procedure]
compileQueryLambdas funSet lambdas =
  let (procs, _errs) = runWriter $ traverse (compileFunctionDef funSet) lambdas
   in procs
