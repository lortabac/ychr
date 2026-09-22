{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Compile a program, then run goals or multi-goal queries against it.
-- Ties "YCHR.Internal.Compile.Pipeline" to "YCHR.Internal.Runtime.Session"
-- and adds the query-time goal evaluator behind 'runProgramWithQuery' and
-- the REPL.
--
-- The bundled standard library ('StdLib') and the compiled type-checker
-- ('SessionInput') are explicit inputs of the entry points that need
-- them: the library embeds nothing at compile time. See
-- @docs\/how-to\/embed-a-chr-module.md#5-supplying-the-resources@.
module YCHR.Run
  ( -- * Compilation (re-exported from "YCHR.Internal.Compile.Pipeline")
    Error (..),
    GoalRejection (..),
    Warning (..),
    CompiledProgram,
    StdLib,
    compileModules,
    compileFiles,
    compileParsedModules,

    -- * Rendering diagnostics
    displayError,
    displayWarning,

    -- * Running goals
    runProgramWithGoal,
    runProgramWithGoalDSL,
    runProgramWithGoalDSLWithWarnings,
    runProgramWithQuery,

    -- * CHR sessions
    Chr,
    SessionInput (..),
    withCHR,
    withTraceHandler,
    tellConstraint,

    -- * Runtime values
    Value (..),
    newVar,
    deref,
    equal,
    unify,

    -- * Query pipeline
    -- $queryPipeline
    ExportResolution (..),
    resolveQueryConstraint,
    resolveQueryTellOrThrow,
    prepareGoal,
    prepareGoalTerm,
    goalShapeConstraint,
    runGoalConstraint,
    runPreparedGoal,
    ResolvedQuery (..),
    resolveQueryGoals,
    PreparedQuery (..),
    prepareQuery,
    prepareQueryUnchecked,
    executePreparedQuery,
    withCHRExtraTraced,
    toSessionInput,
  )
where

-- 'try' comes from the shim so its type variables keep GHC's order
-- (dev-docs/MICROHS_GAPS.md, gap 7).
import Control.Exception.Shim
  ( SomeException,
    displayException,
    handle,
    throwIO,
    try,
  )
import Control.Monad (unless, void)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ask, runReaderT)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, modify)
import Control.Monad.Trans.Writer.CPS (runWriter)
import Data.IORef (readIORef, writeIORef)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Compile
  ( compileFunctionDef,
    funcProcName,
    genCallFunDispatches,
    vmName,
  )
import YCHR.Internal.Compile.Pipeline
  ( CompiledProgram (..),
    Error (..),
    ExportResolution (..),
    GoalRejection (..),
    Warning (..),
    compileFiles,
    compileModules,
    compileParsedModules,
  )
import YCHR.Internal.Desugar (desugarQueryGoals, liftQueryLambdas)
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Diagnostic (Diagnostic)
import YCHR.Internal.Display (displayMsg)
import YCHR.Internal.Meta (valueToTerm)
import YCHR.Internal.PExpr (PExpr (Atom))
import YCHR.Internal.Parsed (AnnP (..), SourceLoc (..))
import YCHR.Internal.Parser (ParseValidationError (..), parseConstraintWith, parseQueryWith)
import YCHR.Internal.Pretty (prettyPExprSrc, prettyTerm)
import YCHR.Internal.Rename (RenameWarning, renameQueryArgsWith, renameQueryGoalsWith)
import YCHR.Internal.Resolve (ResolveError, termToExpr)
import YCHR.Internal.Resolved qualified as R
import YCHR.Internal.Runtime.Error
  ( RuntimeErrorThrown (..),
    isControlException,
    runtimeErrorS,
  )
import YCHR.Internal.Runtime.Interpreter
  ( HostCallFn (..),
    HostCallRegistry,
    callProc,
    deepEvalValue,
    emitTrace,
    snapshotValue,
    snapshotValues,
  )
import YCHR.Internal.Runtime.Monad (Chr, SessionEnv (..))
import YCHR.Internal.Runtime.Reactivation (enqueueObservers)
import YCHR.Internal.Runtime.Session
  ( SessionInput (..),
    drainReactivation,
    tellConstraint,
    toSessionInput,
    withCHR,
    withCHRExtra,
    withCHRExtraTraced,
    withTraceHandler,
  )
import YCHR.Internal.Runtime.Trace (TraceEvent (..))
import YCHR.Internal.Runtime.Types (CallVal (..), Value (..), VarId)
import YCHR.Internal.Runtime.Var (deref, equal, getVarId, newVar, unify)
import YCHR.Internal.StdLib (StdLib)
import YCHR.Internal.TypeCheck (TypeCheckResult (..), typeCheckGoals)
import YCHR.Internal.Types (Constraint (..), Term (..))
import YCHR.Internal.Types qualified as Types
import YCHR.Internal.VM (Name (..), Procedure (..))

-- ---------------------------------------------------------------------------
-- Single-goal API
-- ---------------------------------------------------------------------------

-- | Resolve a query constraint's name against the export map. Covers
-- name resolution only; that the name is a constraint and not a function
-- is checked by 'resolveQueryTellOrThrow'.
resolveQueryConstraint ::
  CompiledProgram ->
  Constraint ->
  Either GoalRejection Types.QualifiedConstraint
resolveQueryConstraint cp (Constraint cname cargs) = case cname of
  Types.Unqualified n ->
    let arity = length cargs
     in case Map.lookup (Types.UnqualifiedIdentifier n arity) cp.exportMap of
          Just (UniqueExport qname) ->
            Right (Types.QualifiedConstraint qname cargs)
          Just (AmbiguousExport ms) ->
            Left (AmbiguousConstraint ms)
          Nothing -> Left NoSuchConstraint
  Types.Qualified m n ->
    let arity = length cargs
     in if Set.member (Types.QualifiedIdentifier m n arity) cp.exportedSet
          then Right (Types.QualifiedConstraint (Types.QualifiedName m n) cargs)
          else Left (ConstraintNotExported (Types.QualifiedName m n))

-- | 'resolveQueryConstraint' plus 'termToExpr' over the arguments, so they
-- evaluate like any tell-side argument; the inner list is the resolve
-- diagnostics from typing them.
resolveQueryTell ::
  CompiledProgram ->
  Constraint ->
  Either GoalRejection ((Types.QualifiedName, [R.Expr]), [Diagnostic ResolveError])
resolveQueryTell cp c = do
  qc <- resolveQueryConstraint cp c
  let (exprs, errs) =
        runWriter
          (traverse (termToExpr cp.queryFunctionVisibility queryLoc queryOrigin) qc.args)
  pure ((qc.name, exprs), errs)

-- | Run one host-built constraint; returns the goal's variable bindings.
-- Arguments are canonicalized by 'prepareGoalTerm' first (rename errors
-- thrown as 'Error', warnings discarded). See Note [Goal argument
-- canonicalization] in "YCHR.Convert".
runProgramWithGoalDSL ::
  CompiledProgram ->
  HostCallRegistry ->
  Constraint ->
  IO (Map Text Term)
runProgramWithGoalDSL cp hostCalls constraint =
  fst <$> runProgramWithGoalDSLWithWarnings cp hostCalls constraint

-- | 'runProgramWithGoalDSL' plus the canonicalization warnings — the only
-- way an embedder sees @YCHR-20101@; render them with 'displayWarning'.
-- See Note [Goal argument canonicalization] in "YCHR.Convert".
runProgramWithGoalDSLWithWarnings ::
  CompiledProgram ->
  HostCallRegistry ->
  Constraint ->
  IO (Map Text Term, [Warning])
runProgramWithGoalDSLWithWarnings cp hostCalls constraint = do
  (prepared, ws) <- prepareGoalTerm cp constraint
  bindings <- runGoalConstraint cp hostCalls prepared
  pure (bindings, ws)

-- | Run a goal with no renaming and no type checking. The goal /must/ come
-- from 'prepareGoal' \/ 'prepareGoalTerm': a raw host-built 'Constraint'
-- keeps its constructor references unqualified, so rules silently never
-- fire. Use 'runProgramWithGoalDSL' unless staging the work yourself.
runGoalConstraint ::
  CompiledProgram ->
  HostCallRegistry ->
  Constraint ->
  IO (Map Text Term)
runGoalConstraint cp hostCalls constraint = convertRuntimeError $ do
  (qn, exprs) <- resolveQueryTellOrThrow cp constraint
  let (lifted, lambdas, liftErrs) =
        liftQueryLambdas cp.nextLambdaIndex [D.BodyTell qn exprs]
  unless (null liftErrs) (throwIO (DesugarErrors liftErrs))
  let queryProcs = compileQueryLambdas lambdas
      allFuns = cp.allFunctions ++ lambdas
      queryDispatches = genCallFunDispatches allFuns
      extraProcs = queryProcs ++ queryDispatches
  withCHRExtra (toSessionInput cp) hostCalls extraProcs $
    executePreparedQuery lifted

-- | Resolve a goal's name and arguments, throwing. A name that does not
-- resolve, or resolves to a function, is 'GoalNotAConstraint'
-- (@YCHR-20013@).
resolveQueryTellOrThrow ::
  CompiledProgram -> Constraint -> IO (Types.QualifiedName, [R.Expr])
resolveQueryTellOrThrow cp c = case resolveQueryTell cp c of
  Left rejection -> throwIO (GoalNotAConstraint c rejection)
  Right ((qn, exprs), errs)
    | not
        ( Map.member
            (Types.ConstraintKey qn (length exprs))
            cp.desugaredProgram.constraintTypes
        ) ->
        throwIO (GoalNotAConstraint c (NotAConstraintItem qn))
    | otherwise -> do
        unless (null errs) (throwIO (ResolveErrors errs))
        pure (qn, exprs)

queryLoc :: SourceLoc
queryLoc = SourceLoc "<query>" 1 1

queryOrigin :: PExpr
queryOrigin = Atom ""

-- $queryPipeline
-- The stages behind 'runProgramWithGoal' and 'runProgramWithQuery':
-- resolve, prepare, execute.
--
-- __Not covered by the package version policy__ (several signatures
-- mention @YCHR.Internal.*@ types). Use 'runProgramWithGoal',
-- 'runProgramWithQuery', or "YCHR.Convert" unless you need to drive the
-- stages yourself.

-- | Render an 'Error' as the @ychr@ CLI does (@file:line:col:@, the
-- @YCHR-NNNNN@ code, message, source line). Prefer it to 'show', which
-- dumps the internal representation. The codes are covered by the package
-- version policy and catalogued in
-- <https://github.com/lortabac/ychr/blob/master/src/YCHR/Internal/Display.hs>.
--
-- __Contains ANSI colour escapes__, unconditionally (no terminal
-- detection, no @NO_COLOR@): strip them before logging, serializing, or
-- asserting on the string.
displayError :: Error -> String
displayError = displayMsg

-- | 'displayError' for a 'Warning'.
displayWarning :: Warning -> String
displayWarning = displayMsg

-- | Re-throw the runtime's 'RuntimeErrorThrown' as the 'RuntimeError'
-- constructor of 'Error', so callers match one exception type.
convertRuntimeError :: IO a -> IO a
convertRuntimeError = handle $ \(RuntimeErrorThrown _kind msg stack) ->
  throwIO (RuntimeError msg stack)

-- | 'convertRuntimeError' in 'Chr', at the 'executePreparedQuery'
-- boundary. Also restores the session call stack on failure, which
-- 'YCHR.Internal.Runtime.Interpreter.withSavedCallStack' unwinds only on
-- normal exit.
convertRuntimeErrorChr :: Chr a -> Chr a
convertRuntimeErrorChr m = do
  env <- ask
  saved <- liftIO (readIORef env.callStack)
  liftIO
    $ handle
      ( \(RuntimeErrorThrown _kind msg stack) -> do
          writeIORef env.callStack saved
          throwIO (RuntimeError msg stack)
      )
    $ runReaderT m env

-- | Parse and canonicalize a goal, with its rename warnings. Throws on
-- parse or rename errors. Separate from running so the CLI can honour
-- @--Werror@ before the goal runs.
prepareGoal :: CompiledProgram -> Text -> IO (Constraint, [Warning])
prepareGoal cp src = case parseConstraintWith cp.opTable "<query>" src of
  Left err -> throwIO (ParseError "<query>" err)
  Right parsed -> case either goalShapeConstraint Right parsed of
    Left validErr -> throwIO (ParseValidationErrors [validErr])
    Right constraint -> prepareGoalTerm cp constraint

-- | 'prepareGoal' minus the parse: canonicalize a goal already in term
-- form. Throws 'RenameErrors'.
prepareGoalTerm :: CompiledProgram -> Constraint -> IO (Constraint, [Warning])
prepareGoalTerm cp (Constraint cname cargs) = do
  (renamedArgs, ws) <-
    either
      (throwIO . RenameErrors)
      pure
      (renameQueryArgsWith cp.queryRenameEnv cargs)
  let warnings = [RenameWarnings ws | not (null ws)]
  pure (Constraint cname renamedArgs, warnings)

-- | Turn a 'MalformedConstraint' goal (bare literal, variable, wildcard)
-- into a 0-arity goal named after the term, so name resolution rejects it
-- as YCHR-20013 like any other non-constraint goal, not as the rule-head
-- code YCHR-15003. Other validation errors pass through.
goalShapeConstraint ::
  AnnP ParseValidationError -> Either (AnnP ParseValidationError) Constraint
goalShapeConstraint (AnnP MalformedConstraint _ pexpr) =
  Right (Constraint (Types.Unqualified (T.pack (prettyPExprSrc pexpr))) [])
goalShapeConstraint other = Left other

-- | Type-check and run a goal from 'prepareGoal' \/ 'prepareGoalTerm'.
-- Throws 'TypeErrors'.
--
-- The 'SessionInput' is the compiled type-checker, an explicit input
-- because the @ychr@ library embeds nothing at compile time; build it
-- once and reuse it across goals.
runPreparedGoal ::
  SessionInput ->
  CompiledProgram ->
  HostCallRegistry ->
  Constraint ->
  IO (Map Text Term)
runPreparedGoal typeChecker cp hostCalls original = do
  tcErrs <- case resolveQueryTell cp original of
    Right ((qn, exprs), errs)
      | null errs -> do
          -- Errors only: no warning channel here, and the checker's one
          -- warning (YCHR-20104) needs a guard, which a goal never has.
          -- 'prepareQuery' surfaces warnings if one is ever added.
          result <-
            typeCheckGoals
              typeChecker
              cp.desugaredProgram
              queryLoc
              (Just "query")
              [D.BodyTell qn exprs]
          pure result.errors
    -- Resolution failed: the runtime path raises the same errors.
    _ -> pure []
  unless (null tcErrs) (throwIO (TypeErrors tcErrs))
  -- Already canonicalized by 'prepareGoal'; do not rename again.
  runGoalConstraint cp hostCalls original

-- | 'runProgramWithGoalDSL' for a goal given as surface-language 'Text'.
runProgramWithGoal ::
  SessionInput ->
  CompiledProgram ->
  HostCallRegistry ->
  Text ->
  IO (Map Text Term)
runProgramWithGoal typeChecker cp hostCalls src = do
  (constraint, _ws) <- prepareGoal cp src
  runPreparedGoal typeChecker cp hostCalls constraint

-- ---------------------------------------------------------------------------
-- Multi-goal query API
-- ---------------------------------------------------------------------------

-- | A query parsed, desugared, lambda-lifted, and type-checked.
-- 'extraProcs' (the lifted lambdas and their dispatchers) must be added
-- to the session's procedures before 'executePreparedQuery'.
data PreparedQuery = PreparedQuery
  { liftedGoals :: [D.BodyGoal],
    queryLambdas :: [D.Function],
    extraProcs :: [Procedure]
  }

-- | 'PreparedQuery' minus the type check. 'goalProgram' is the program to
-- check 'liftedGoals' against: the compiled one plus 'queryLambdas'.
data ResolvedQuery = ResolvedQuery
  { liftedGoals :: [D.BodyGoal],
    queryLambdas :: [D.Function],
    goalProgram :: D.Program,
    renameWarnings :: [Diagnostic RenameWarning]
  }

-- | 'prepareQuery' without the type check, for callers that check
-- themselves or not at all.
resolveQueryGoals :: CompiledProgram -> Text -> IO ResolvedQuery
resolveQueryGoals cp src = do
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
      ( renameQueryGoalsWith
          cp.queryRenameEnv
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
  let (lifted, lambdas, liftErrs) = liftQueryLambdas cp.nextLambdaIndex bodyGoals
  unless (null liftErrs) (throwIO (DesugarErrors liftErrs))
  let cdp = cp.desugaredProgram
  pure
    ResolvedQuery
      { liftedGoals = lifted,
        queryLambdas = lambdas,
        goalProgram =
          D.Program
            { rules = cdp.rules,
              functions = cdp.functions ++ lambdas,
              constraintTypes = cdp.constraintTypes,
              constraintBounds = cdp.constraintBounds,
              typeDefinitions = cdp.typeDefinitions
            },
        renameWarnings = renameWs
      }

-- | Parse, rename, desugar, lambda-lift, and type-check a query. The
-- 'SessionInput' is the compiled type-checker; see 'runPreparedGoal'.
prepareQuery :: SessionInput -> CompiledProgram -> Text -> IO (PreparedQuery, [Warning])
prepareQuery typeChecker cp src = do
  resolved <- resolveQueryGoals cp src
  tcResult <-
    typeCheckGoals
      typeChecker
      resolved.goalProgram
      queryLoc
      (Just "query")
      resolved.liftedGoals
  unless (null tcResult.errors) (throwIO (TypeErrors tcResult.errors))
  pure
    ( prepareResolved cp resolved,
      [RenameWarnings resolved.renameWarnings | not (null resolved.renameWarnings)]
        ++ [TypeCheckWarnings tcResult.warnings | not (null tcResult.warnings)]
    )

-- | 'prepareQuery' without the type check: parse, rename, desugar and
-- lambda-lift the query, and report its rename warnings, but do not run
-- the checker over its goals. This is what @ychr repl --no-check@ uses,
-- and what an embedder that does not want the optional type system uses
-- in place of 'prepareQuery'.
--
-- Only the checker is skipped: parse, rename, resolve and desugar errors
-- still throw, exactly as in 'prepareQuery'.
prepareQueryUnchecked :: CompiledProgram -> Text -> IO (PreparedQuery, [Warning])
prepareQueryUnchecked cp src = do
  resolved <- resolveQueryGoals cp src
  pure
    ( prepareResolved cp resolved,
      [RenameWarnings resolved.renameWarnings | not (null resolved.renameWarnings)]
    )

-- | Finish preparing a resolved query: compile its lifted lambdas and
-- their call dispatchers into the extra procedures the session needs.
-- Shared by 'prepareQuery' and 'prepareQueryUnchecked'.
prepareResolved :: CompiledProgram -> ResolvedQuery -> PreparedQuery
prepareResolved cp resolved =
  PreparedQuery
    { liftedGoals = resolved.liftedGoals,
      queryLambdas = resolved.queryLambdas,
      extraProcs =
        compileQueryLambdas resolved.queryLambdas
          ++ genCallFunDispatches (cp.allFunctions ++ resolved.queryLambdas)
    }

-- | Run the 'liftedGoals' of a 'PreparedQuery' in the current session, in
-- a fresh per-query variable scope; the host-call registry comes from
-- the ambient 'SessionEnv'.
executePreparedQuery :: [D.BodyGoal] -> Chr (Map Text Term)
executePreparedQuery lifted =
  convertRuntimeErrorChr $
    evalStateT
      ( do
          mapM_ executeBodyGoal lifted
          varMap <- get
          classes <- liftChr (buildAliasClasses varMap)
          liftChr $
            Map.traverseWithKey
              (\k v -> valueToTerm (perKeyAliases classes k) v)
              varMap
      )
      (Map.empty :: Map Text Value)

-- | Group user-visible query variables (not @_@-prefixed) by 'VarId'.
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

-- | The 'VarId' → display-name map for printing variable @k@'s binding:
-- each aliased class shows as the name after @k@ in it, wrapping to the
-- head name; singleton classes contribute nothing.
perKeyAliases :: Map VarId (NonEmpty Text) -> Text -> Map VarId Text
perKeyAliases classes k = Map.mapMaybe pick classes
  where
    pick (_ :| []) = Nothing
    pick names@(canonical :| _) = Just $ case break (== k) (NE.toList names) of
      (_, _ : next : _) -> next
      (_, [_]) -> canonical
      (_, []) -> canonical

-- | Run a multi-goal query against a compiled program. The
-- 'SessionInput' is the compiled type-checker; see 'runPreparedGoal'.
runProgramWithQuery ::
  SessionInput -> CompiledProgram -> HostCallRegistry -> Text -> IO (Map Text Term)
runProgramWithQuery typeChecker cp hostCalls src = do
  (prep, _ws) <- prepareQuery typeChecker cp src
  withCHRExtra (toSessionInput cp) hostCalls prep.extraProcs $
    executePreparedQuery prep.liftedGoals

-- ---------------------------------------------------------------------------
-- Query goal evaluator (internal)
-- ---------------------------------------------------------------------------

type QueryM = StateT (Map Text Value) Chr

-- | Run a 'Chr' action in 'QueryM'. The single lift this stack needs;
-- named so call sites read as "do this in the session".
liftChr :: Chr a -> QueryM a
liftChr = lift
{-# INLINE liftChr #-}

-- | Surface 'Term' to 'Value' in the per-query scope, allocating a fresh
-- variable per new 'VarTerm'. An anonymous @_@ is a fresh variable too,
-- one per occurrence: it is never entered in the scope map, so it cannot
-- collide with a named goal variable and never appears in the bindings
-- a query reports.
termToValue :: Term -> QueryM Value
termToValue (VarTerm n) = do
  varMap <- get
  case Map.lookup n varMap of
    Just v -> pure v
    Nothing -> do
      v <- liftChr newVar
      modify (Map.insert n v)
      pure v
termToValue (IntTerm n) = pure (VInt n)
termToValue (FloatTerm n) = pure (VFloat n)
termToValue (TextTerm s) = pure (VText s)
termToValue Wildcard = liftChr newVar
-- Mirrors 'Compile.compileTerm': @=@ operands must lower to 'VBool' so
-- they unify with comparison results.
termToValue (CompoundTerm name []) | Just b <- Types.preludeBool name = pure (VBool b)
-- 0-arity ctors are atoms at runtime: qualified in the @vmName@-mangled
-- form, unqualified as the raw name. See 'YCHR.Internal.Compile.compileTerm'.
termToValue (CompoundTerm name@(Types.Qualified _ _) []) =
  pure (VAtom (vmName name).unName)
termToValue (CompoundTerm (Types.Unqualified n) []) = pure (VAtom n)
termToValue (CompoundTerm name ts) = VTerm (vmName name).unName <$> traverse termToValue ts

-- | Execute a single desugared body goal in the query context.
executeBodyGoal :: D.BodyGoal -> QueryM ()
executeBodyGoal D.BodyTrue = pure ()
-- Rejected by 'YCHR.Internal.Desugar.desugarQueryGoals' (YCHR-30006):
-- a query has no enclosing rule to lift a disjunct out of.
executeBodyGoal (D.BodyOr _) =
  error "Run.executeBodyGoal: a query disjunction should have been rejected"
executeBodyGoal (D.BodyUnify l r) = do
  v1 <- exprToValue l
  v2 <- exprToValue r
  liftChr (queryUnify v1 v2)
executeBodyGoal (D.BodyHostStmt f args) = do
  argVals <- traverse evalNestedExpr args
  env <- liftChr ask
  result <- liftChr (hostCall (Map.lookup (Name f) env.hostCalls) f argVals)
  liftChr $
    emitTrace $ do
      argTs <- snapshotValues argVals
      resT <- snapshotValue result
      pure (TECallHost f argTs resT)
executeBodyGoal (D.BodyIs v expr) = do
  -- Mirror 'evalValExpr (EvalDeep (Var _))' in the compiled interpreter:
  -- when the RHS is syntactically a variable, walk the dereferenced
  -- value so a bound compound with an evaluable functor gets evaluated
  -- (@X = 1 + 1, R is X@ ⇒ @R = 2@). For all other RHS shapes the
  -- result of the outer typed operation is already final.
  raw <- evalNestedExpr expr
  result <- case expr of
    R.VarExpr _ -> liftChr (deepEvalValue raw)
    _ -> pure raw
  varMap <- get
  case Map.lookup v varMap of
    Just existing -> liftChr (queryUnify existing result)
    Nothing -> modify (Map.insert v result)
executeBodyGoal (D.BodyTell qn args) = do
  argVals <- traverse evalNestedExpr args
  liftChr (tellConstraint (Types.qualifiedToName qn) argVals)
executeBodyGoal (D.BodyCall qn args) = do
  argVals <- traverse evalNestedExpr args
  let funcName = Types.qualifiedToName qn
  _ <- liftChr (callProc (funcProcName funcName (length argVals)) (map CVal argVals))
  pure ()
executeBodyGoal (D.BodyApply f args) = do
  fAndArgVals <- traverse evalNestedExpr (f : args)
  let n = length args
      dispatchName = Name ("call_" <> T.pack (show n))
  _ <- liftChr (callProc dispatchName (map CVal fAndArgVals))
  pure ()

-- | Runtime error for a failed unification.
raiseUnifyFailure :: Value -> Value -> Chr ()
raiseUnifyFailure v1 v2 = do
  t1 <- valueToTerm Map.empty v1
  t2 <- valueToTerm Map.empty v2
  runtimeErrorS $
    "unification failure: cannot unify "
      ++ prettyTerm t1
      ++ " with "
      ++ prettyTerm t2

-- | Call a host function. As in
-- 'YCHR.Internal.Runtime.Interpreter.invokeHostCall', an unregistered
-- name or any exception it throws becomes a 'RuntimeError' with a call
-- stack; control exceptions ('isControlException') pass through.
hostCall :: Maybe HostCallFn -> Text -> [Value] -> Chr Value
hostCall (Just (HostCallFn f)) name args = do
  env <- ask
  result <- liftIO (try @SomeException (runReaderT (f args) env))
  case result of
    Right v -> pure v
    Left exc
      | isControlException exc -> liftIO (throwIO exc)
      | otherwise ->
          runtimeErrorS $
            "host call " ++ T.unpack name ++ ": " ++ displayException exc
hostCall Nothing name _ =
  runtimeErrorS $ "Unknown host function: " ++ T.unpack name

-- | Query-side unification, mirroring the interpreter's @BUnify@: unify,
-- enqueue observers, trace on success (operands snapshotted before the
-- unify), raise on failure, drain the reactivation queue.
queryUnify :: Value -> Value -> Chr ()
queryUnify v1 v2 = do
  env <- ask
  mh <- liftIO (readIORef env.traceHandler)
  case mh of
    Nothing -> do
      (ok, observers) <- unify v1 v2
      void (enqueueObservers observers)
      unless ok (raiseUnifyFailure v1 v2)
      drainReactivation
    Just _ -> do
      t1 <- snapshotValue v1
      t2 <- snapshotValue v2
      (ok, observers) <- unify v1 v2
      enqueued <- enqueueObservers observers
      if ok
        then do
          emitTrace (pure (TEUnify t1 t2 enqueued))
          drainReactivation
        else raiseUnifyFailure v1 v2

-- | 'termToValue' for a 'D.Expr': builds the value structurally, no call
-- evaluation.
exprToValue :: D.Expr -> QueryM Value
exprToValue = termToValue . R.exprToTerm

-- | Evaluate an expression in the query context: calls run, constructors
-- build structurally (children still evaluated), @quote\/1@ is opaque.
evalNestedExpr :: D.Expr -> QueryM Value
evalNestedExpr (R.IntExpr n) = pure (VInt n)
evalNestedExpr (R.FloatExpr n) = pure (VFloat n)
evalNestedExpr (R.TextExpr s) = pure (VText s)
evalNestedExpr R.WildcardExpr = liftChr newVar
evalNestedExpr (R.VarExpr v) = do
  varMap <- get
  case Map.lookup v varMap of
    Just val -> liftChr (deref val)
    Nothing -> do
      fresh <- liftChr newVar
      modify (Map.insert v fresh)
      pure fresh
evalNestedExpr (R.CallExpr qn args) = do
  argVals <- traverse evalNestedExpr args
  let funcName = Types.qualifiedToName qn
  liftChr (callProc (funcProcName funcName (length argVals)) (map CVal argVals))
evalNestedExpr (R.ApplyExpr f args) = do
  fAndArgVals <- traverse evalNestedExpr (f : args)
  let n = length args
      dispatchName = Name ("call_" <> T.pack (show n))
  liftChr (callProc dispatchName (map CVal fAndArgVals))
evalNestedExpr (R.HostExpr f args) = do
  argVals <- traverse evalNestedExpr args
  env <- liftChr ask
  liftChr (hostCall (Map.lookup (Name f) env.hostCalls) f argVals)
-- @quote(X)@: inner value as data, no nested-call evaluation.
evalNestedExpr (R.CtorExpr (Types.Unqualified "quote") [arg]) = exprToValue arg
-- Mirrors 'Compile.compileExpr': 'VBool', as compiled rules produce.
evalNestedExpr (R.CtorExpr name []) | Just b <- Types.preludeBool name = pure (VBool b)
-- 0-arity ctors collapse to atoms at the runtime layer.
evalNestedExpr (R.CtorExpr name@(Types.Qualified _ _) []) =
  pure (VAtom (vmName name).unName)
evalNestedExpr (R.CtorExpr (Types.Unqualified n) []) = pure (VAtom n)
evalNestedExpr (R.CtorExpr name args) =
  -- 'evalNestedExpr', not 'exprToValue': nested calls must evaluate
  -- before the compound is built, as in 'Compile.compileExpr'.
  VTerm (vmName name).unName <$> traverse evalNestedExpr args
evalNestedExpr e@(R.FunRefExpr _ _) = exprToValue e
evalNestedExpr (R.LambdaExpr _ _) =
  error "Run.evalNestedExpr: LambdaExpr survived lambda lifting"

-- | Compile lifted query lambdas. The error channel is dropped: the
-- lambdas were lifted from a program that compiled and type-checked, so
-- an error here is a compiler bug.
compileQueryLambdas :: [D.Function] -> [Procedure]
compileQueryLambdas lambdas =
  let (procs, _errs) = runWriter $ traverse compileFunctionDef lambdas
   in procs
