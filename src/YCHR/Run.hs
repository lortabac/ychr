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
    resolveQueryTell,
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
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Compile
  ( compileFunctionDef,
    funcProcName,
    genCallFunDispatches,
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
import YCHR.Diagnostic (Diagnostic)
import YCHR.Meta (valueToTerm)
import YCHR.PExpr (PExpr (Atom))
import YCHR.Parsed (SourceLoc (..))
import YCHR.Parser (parseConstraintWith, parseQueryWith)
import YCHR.Pretty (prettyTerm)
import YCHR.Rename (renameQueryArgs, renameQueryGoals)
import YCHR.Resolve (ResolveError, termToExpr)
import YCHR.Resolved qualified as R
import YCHR.Runtime.Error (RuntimeErrorThrown (..))
import YCHR.Runtime.Interpreter (HostCallFn (..), HostCallRegistry, callProc, deepEvalValue)
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
import YCHR.VM (Name (..), Procedure (..))

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
          Just (UniqueExport qname) ->
            Right (Types.QualifiedConstraint qname cargs)
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

-- | Resolve a query constraint to its qualified name and 'Expr'-typed
-- arguments. The arguments are lifted from the surface 'Term' shape via
-- 'termToExpr', so they are evaluated like any other tell-side
-- argument when the goal runs. The outer 'Either' carries
-- name-resolution failures (in the same string format as
-- 'resolveQueryConstraint'); the inner diagnostic list collects any
-- non-fatal resolve errors emitted while typing the arguments.
resolveQueryTell ::
  CompiledProgram ->
  Constraint ->
  Either String ((Types.QualifiedName, [R.Expr]), [Diagnostic ResolveError])
resolveQueryTell cp c = do
  qc <- resolveQueryConstraint cp c
  let (exprs, errs) =
        runWriter
          (traverse (termToExpr cp.queryFunctionVisibility queryLoc queryOrigin) qc.args)
  pure ((qc.name, exprs), errs)

-- | Run a single CHR constraint against a compiled program. Returns
-- the per-query variable bindings.
runProgramWithGoalDSL ::
  CompiledProgram ->
  HostCallRegistry ->
  Constraint ->
  IO (Map Text Term)
runProgramWithGoalDSL cp hostCalls constraint = convertRuntimeError $ do
  (qn, exprs) <- resolveQueryTellOrThrow cp constraint
  let (lifted, lambdas) =
        liftQueryLambdas cp.nextLambdaIndex [D.BodyTell qn exprs]
      queryProcs = compileQueryLambdas lambdas
      allFuns = cp.allFunctions ++ lambdas
      queryDispatches = genCallFunDispatches allFuns
      extraProcs = queryProcs ++ queryDispatches
  withCHRExtra (toSessionInput cp) hostCalls extraProcs $
    executePreparedQuery lifted

-- | Resolve a goal and throw on any failure. Used by both
-- 'runProgramWithGoalDSL' and 'runPreparedGoal'.
resolveQueryTellOrThrow ::
  CompiledProgram -> Constraint -> IO (Types.QualifiedName, [R.Expr])
resolveQueryTellOrThrow cp c = case resolveQueryTell cp c of
  Left err -> fail err
  Right (pair, errs) -> do
    unless (null errs) (throwIO (ResolveErrors errs))
    pure pair

queryLoc :: SourceLoc
queryLoc = SourceLoc "<query>" 1 1

queryOrigin :: PExpr
queryOrigin = Atom ""

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
prepareGoal cp src = case parseConstraintWith cp.opTable "<query>" src of
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
-- Throws 'TypeErrors' on goal-time type errors. Returns the per-query
-- variable bindings.
runPreparedGoal ::
  CompiledProgram ->
  HostCallRegistry ->
  Constraint ->
  IO (Map Text Term)
runPreparedGoal cp hostCalls original = do
  tcErrs <- case resolveQueryTell cp original of
    Right ((qn, exprs), errs)
      | null errs ->
          typeCheckGoals
            cp.desugaredProgram
            queryLoc
            (Just "query")
            [D.BodyTell qn exprs]
    -- Skip type-checking if name resolution failed or termToExpr
    -- raised diagnostics; the runtime path will surface the same
    -- errors with the same messages.
    _ -> pure []
  unless (null tcErrs) (throwIO (TypeErrors tcErrs))
  runProgramWithGoalDSL cp hostCalls original

-- | Like 'runProgramWithGoalDSL' but accepts a query as surface-language 'Text'.
runProgramWithGoal ::
  CompiledProgram ->
  HostCallRegistry ->
  Text ->
  IO (Map Text Term)
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
  let vis = cp.queryFunctionVisibility
      (exprs, exprErrs) =
        runWriter (traverse (termToExpr vis queryLoc queryOrigin) renamed)
  unless (null exprErrs) (throwIO (ResolveErrors exprErrs))
  bodyGoals <-
    either
      (throwIO . DesugarErrors)
      pure
      (desugarQueryGoals exprs)
  let (lifted, lambdas) = liftQueryLambdas cp.nextLambdaIndex bodyGoals
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
      queryProcs = compileQueryLambdas lambdas
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
-- 'VarId'. Each class is non-empty by construction: a fresh class
-- starts as a one-element 'NonEmpty', and subsequent variables sharing
-- the same 'VarId' are appended.
buildAliasClasses :: Map Text Value -> Chr (Map VarId (NonEmpty Text))
buildAliasClasses varMap = do
  pairs <- traverse vidOf (Map.toAscList varMap)
  pure $ Map.fromListWith (flip (<>)) [(vid, k :| []) | (k, Just vid) <- pairs]
  where
    vidOf (k, v)
      | "_" `T.isPrefixOf` k = pure (k, Nothing)
      | otherwise = do
          mvid <- getVarId v
          pure (k, mvid)

-- | Build the 'VarId' → display name map that 'valueToTerm' should
-- use when printing the binding for surface variable @k@. A singleton
-- alias class contributes nothing (no aliasing); otherwise we pick the
-- name that follows @k@ in the class, wrapping back to the canonical
-- (head) name if @k@ is at the end of, or absent from, the class.
perKeyAliases :: Map VarId (NonEmpty Text) -> Text -> Map VarId Text
perKeyAliases classes k = Map.mapMaybe pick classes
  where
    pick (_ :| []) = Nothing
    pick names@(canonical :| _) = Just $ case break (== k) (NE.toList names) of
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
  v1 <- exprToValue l
  v2 <- exprToValue r
  (ok, observers) <- lift (unify v1 v2)
  lift (enqueue observers)
  unless ok (lift (raiseUnifyFailure v1 v2))
  lift drainReactivation
executeBodyGoal (D.BodyHostStmt f args) = do
  argVals <- traverse evalNestedExpr args
  env <- lift ask
  _ <- lift (hostCall (Map.lookup (Name f) env.hostCalls) f argVals)
  pure ()
executeBodyGoal (D.BodyIs v expr) = do
  -- Mirror 'evalValExpr (EvalDeep (Var _))' in the compiled interpreter:
  -- when the RHS is syntactically a variable, walk the dereferenced
  -- value so a bound compound with an evaluable functor gets evaluated
  -- (@X = 1 + 1, R is X@ ⇒ @R = 2@). For all other RHS shapes the
  -- result of the outer typed operation is already final.
  raw <- evalNestedExpr expr
  result <- case expr of
    R.VarExpr _ -> lift (deepEvalValue raw)
    _ -> pure raw
  varMap <- get
  case Map.lookup v varMap of
    Just existing -> do
      (ok, observers) <- lift (unify existing result)
      lift (enqueue observers)
      unless ok (lift (raiseUnifyFailure existing result))
      lift drainReactivation
    Nothing -> modify (Map.insert v result)
executeBodyGoal (D.BodyTell qn args) = do
  argVals <- traverse evalNestedExpr args
  lift (tellConstraint (Types.qualifiedToName qn) argVals)
executeBodyGoal (D.BodyCall qn args) = do
  argVals <- traverse exprToValue args
  let funcName = Types.qualifiedToName qn
  _ <- lift (callProc (funcProcName funcName (length argVals)) (map CVal argVals))
  pure ()
executeBodyGoal (D.BodyApply f args) = do
  fAndArgVals <- traverse exprToValue (f : args)
  let n = length args
      dispatchName = Name ("call_" <> T.pack (show n))
  _ <- lift (callProc dispatchName (map CVal fAndArgVals))
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

-- | Build a runtime 'Value' from a desugared 'D.Expr' without
-- evaluating embedded function calls. Mirrors 'termToValue' on the
-- typed side by round-tripping through the surface 'Term' shape via
-- 'R.exprToTerm', so query-time value construction stays bit-for-bit
-- compatible with the pre-refactor behaviour.
exprToValue :: D.Expr -> QueryM Value
exprToValue = termToValue . R.exprToTerm

-- | Evaluate an expression in the query context (used for @is@ RHS
-- and guard expressions). 'CallExpr', 'ApplyExpr', and 'HostExpr'
-- evaluate their arguments and invoke the appropriate procedure;
-- 'CtorExpr' (and the @term\/1@ quoting form) build values
-- structurally without re-evaluating their children.
evalNestedExpr :: D.Expr -> QueryM Value
evalNestedExpr (R.IntExpr n) = pure (VInt n)
evalNestedExpr (R.FloatExpr n) = pure (VFloat n)
evalNestedExpr (R.AtomExpr s) = pure (VAtom s)
evalNestedExpr (R.TextExpr s) = pure (VText s)
evalNestedExpr R.WildcardExpr = pure VWildcard
evalNestedExpr (R.VarExpr v) = do
  varMap <- get
  case Map.lookup v varMap of
    Just val -> lift (deref val)
    Nothing -> do
      fresh <- lift newVar
      modify (Map.insert v fresh)
      pure fresh
evalNestedExpr (R.CallExpr qn args) = do
  argVals <- traverse evalNestedExpr args
  let funcName = Types.qualifiedToName qn
  lift (callProc (funcProcName funcName (length argVals)) (map CVal argVals))
evalNestedExpr (R.ApplyExpr f args) = do
  fAndArgVals <- traverse evalNestedExpr (f : args)
  let n = length args
      dispatchName = Name ("call_" <> T.pack (show n))
  lift (callProc dispatchName (map CVal fAndArgVals))
evalNestedExpr (R.HostExpr f args) = do
  argVals <- traverse evalNestedExpr args
  env <- lift ask
  lift (hostCall (Map.lookup (Name f) env.hostCalls) f argVals)
-- @term(X)@ short-circuit: build the inner value as data, no
-- nested-call evaluation. Mirrors the legacy 'termToValue arg' path.
evalNestedExpr (R.CtorExpr (Types.Unqualified "term") [arg]) = exprToValue arg
evalNestedExpr (R.CtorExpr name args) =
  -- Recurse with 'evalNestedExpr' (not 'exprToValue'): a 'CtorExpr'
  -- can contain nested 'CallExpr' / 'HostExpr' children that must
  -- evaluate before the surrounding compound is built. Mirrors the
  -- compiled path in 'Compile.compileExpr' for 'CtorExpr'.
  VTerm (vmName name).unName <$> traverse evalNestedExpr args
evalNestedExpr e@(R.FunRefExpr _ _) = exprToValue e
evalNestedExpr (R.LambdaExpr _ _) =
  error "Run.evalNestedExpr: LambdaExpr survived lambda lifting"

-- | Compile lifted query lambdas into VM procedures. Discards the
-- error channel: by the time this runs, 'prepareQuery' has already
-- lifted these lambdas from a desugared program that compiled
-- cleanly and has type-checked them, so any error here would
-- indicate a compiler bug rather than a user problem.
compileQueryLambdas :: [D.Function] -> [Procedure]
compileQueryLambdas lambdas =
  let (procs, _errs) = runWriter $ traverse compileFunctionDef lambdas
   in procs
