{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Top-level orchestration: compile a program, then run goals or
-- multi-goal queries against it. The CHR session machinery lives in
-- "YCHR.Internal.Runtime.Session"; the compilation pipeline lives in
-- "YCHR.Internal.Compile.Pipeline". This module ties the two together and
-- adds the query-time goal evaluator used by 'runProgramWithQuery'
-- and the live REPL session in "YCHR.Internal.Repl".
module YCHR.Run
  ( -- * Compilation (re-exported from "YCHR.Internal.Compile.Pipeline")
    Error (..),
    GoalRejection (..),
    Warning (..),
    CompiledProgram,
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
    PreparedQuery (..),
    prepareQuery,
    executePreparedQuery,
    withCHRExtraTraced,
    toSessionInput,
  )
where

import Control.Exception
  ( SomeAsyncException,
    SomeException,
    displayException,
    fromException,
    handle,
    throwIO,
    try,
  )
import Control.Monad (unless, void, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ask, runReaderT)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, modify)
import Control.Monad.Trans.Writer.CPS (runWriter)
import Data.IORef (readIORef)
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
import YCHR.Internal.Rename (renameQueryArgsWith, renameQueryGoalsWith)
import YCHR.Internal.Resolve (ResolveError, termToExpr)
import YCHR.Internal.Resolved qualified as R
import YCHR.Internal.Runtime.Error (RuntimeErrorThrown (..), runtimeErrorS)
import YCHR.Internal.Runtime.Interpreter
  ( HostCallFn (..),
    HostCallRegistry,
    callProc,
    constraintTypeLabel,
    deepEvalValue,
    emitTrace,
    snapshotValue,
    snapshotValues,
    suspensionView,
  )
import YCHR.Internal.Runtime.Monad (Chr, SessionEnv (..))
import YCHR.Internal.Runtime.Reactivation (drainQueue, enqueueObservers)
import YCHR.Internal.Runtime.Session
  ( tellConstraint,
    toSessionInput,
    withCHR,
    withCHRExtra,
    withCHRExtraTraced,
    withTraceHandler,
  )
import YCHR.Internal.Runtime.Store (aliveConstraint)
import YCHR.Internal.Runtime.Trace (TraceEvent (..))
import YCHR.Internal.Runtime.Types (CallVal (..), Value (..), VarId)
import YCHR.Internal.Runtime.Var (deref, equal, getVarId, newVar, unify)
import YCHR.Internal.TypeCheck (TypeCheckResult (..), typeCheckGoals)
import YCHR.Internal.Types (Constraint (..), Term (..))
import YCHR.Internal.Types qualified as Types
import YCHR.Internal.VM (Name (..), Procedure (..))

-- ---------------------------------------------------------------------------
-- Single-goal API
-- ---------------------------------------------------------------------------

-- | Resolve a query constraint against the export map. The resolved
-- form is a 'Types.QualifiedConstraint' since name resolution always
-- produces a fully-qualified name. On failure, returns a structured
-- 'GoalRejection' so 'resolveQueryTellOrThrow' can surface a
-- @YCHR-NNNNN@-coded diagnostic. The rejection only covers
-- name-resolution failures; the post-resolution check that the
-- resolved name actually refers to a constraint (and not a function)
-- lives in 'resolveQueryTellOrThrow', which has the desugared program
-- in hand.
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
  Either GoalRejection ((Types.QualifiedName, [R.Expr]), [Diagnostic ResolveError])
resolveQueryTell cp c = do
  qc <- resolveQueryConstraint cp c
  let (exprs, errs) =
        runWriter
          (traverse (termToExpr cp.queryFunctionVisibility queryLoc queryOrigin) qc.args)
  pure ((qc.name, exprs), errs)

-- | Run a single host-built CHR constraint against a compiled program.
-- Returns the per-query variable bindings.
--
-- The goal's arguments are canonicalized with 'prepareGoalTerm' first,
-- exactly as the surface-text path does: a host-built @red@ has to
-- reach the runtime in the same qualified form (@m:red@) the compiled
-- head patterns were compiled to, or the rule silently never fires.
-- Rename /errors/ are thrown as 'Error', like every other failure here.
--
-- Goal-argument warnings are discarded, which is what the typed
-- wrappers in "YCHR.Convert" and "YCHR.DSL" need — their result types
-- have no warning channel. They are worth reading, though: an
-- undeclared or non-exported constructor in a goal argument warns
-- (@YCHR-20101@) and then quietly fails to match. Use
-- 'runProgramWithGoalDSLWithWarnings' to see them.
runProgramWithGoalDSL ::
  CompiledProgram ->
  HostCallRegistry ->
  Constraint ->
  IO (Map Text Term)
runProgramWithGoalDSL cp hostCalls constraint =
  fst <$> runProgramWithGoalDSLWithWarnings cp hostCalls constraint

-- | 'runProgramWithGoalDSL', but also returning the warnings raised
-- while canonicalizing the goal's arguments — the pair 'prepareGoal'
-- returns for a surface-text goal, and the only way for an embedder to
-- see them.
--
-- Render them with 'displayWarning'. A non-empty list is worth
-- surfacing even when the run succeeds: @YCHR-20101@ on a goal argument
-- means that argument did not canonicalize, so any rule matching on it
-- did not fire.
--
-- > (bindings, ws) <- runProgramWithGoalDSLWithWarnings cp hostCalls goal
-- > mapM_ (hPutStr stderr . displayWarning) ws
runProgramWithGoalDSLWithWarnings ::
  CompiledProgram ->
  HostCallRegistry ->
  Constraint ->
  IO (Map Text Term, [Warning])
runProgramWithGoalDSLWithWarnings cp hostCalls constraint = do
  (prepared, ws) <- prepareGoalTerm cp constraint
  bindings <- runGoalConstraint cp hostCalls prepared
  pure (bindings, ws)

-- | Run an already-prepared goal constraint: no renaming, no type
-- checking. Callers that have run 'prepareGoal' \/ 'prepareGoalTerm'
-- themselves use this so the goal is not renamed twice.
--
-- The goal /must/ have come from one of those: passing a raw host-built
-- 'Constraint' here leaves its bare data-constructor references
-- unqualified, so they do not match the compiled head patterns and the
-- rules silently never fire. Use 'runProgramWithGoalDSL' unless you are
-- deliberately staging the work yourself.
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

-- | Resolve a goal and throw on any failure. Used by both
-- 'runGoalConstraint' and 'runPreparedGoal'.
--
-- A name-resolution failure (or a name that resolves to a function
-- rather than a constraint) becomes 'GoalNotAConstraint', so the CLI's
-- single-constraint goal surface surfaces a @YCHR-20013@ diagnostic
-- with a hint pointing at the REPL.
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
-- The staged internals behind 'runProgramWithGoal' and
-- 'runProgramWithQuery': resolve a goal, prepare it, then execute it.
-- They exist so the REPL can interleave its own work between the
-- stages, and are exported for the same reason the @YCHR.Internal@
-- modules are.
--
-- __These are not covered by the package version policy.__ Several of
-- them mention types from @YCHR.Internal.*@ in their signatures, which
-- is the giveaway. Use 'runProgramWithGoal', 'runProgramWithQuery', or
-- the typed wrappers in "YCHR.Convert" unless you specifically need to
-- drive the stages yourself.

-- | Render an 'Error' the way the @ychr@ command-line tool does:
-- @file:line:col:@ prefix, the @YCHR-NNNNN@ code, the message, and the
-- offending source line where one is available.
--
-- Prefer this to 'show': the derived 'Show' instance dumps the internal
-- diagnostic representation, whereas this is the supported, stable
-- rendering. The @YCHR-NNNNN@ codes are covered by the package version
-- policy and catalogued in
-- <https://github.com/lortabac/ychr/blob/master/docs/reference/errors.md>.
--
-- The result is a 'String' (not 'Data.Text.Text') because it is meant to
-- go straight to a handle:
--
-- > case compileModules True mods of
-- >   Left err -> hPutStr stderr (displayError err)
-- >   Right (cp, ws) -> mapM_ (hPutStr stderr . displayWarning) ws >> ...
--
-- __The result contains ANSI colour escapes__, unconditionally — there is
-- no terminal detection and no @NO_COLOR@ handling yet. That suits a
-- terminal, but strip them before putting the string in a log file, a JSON
-- payload, or a test assertion.
displayError :: Error -> String
displayError = displayMsg

-- | Render a 'Warning' in the same format as 'displayError'.
displayWarning :: Warning -> String
displayWarning = displayMsg

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
  Right parsed -> case either goalShapeConstraint Right parsed of
    Left validErr -> throwIO (ParseValidationErrors [validErr])
    Right constraint -> prepareGoalTerm cp constraint

-- | 'prepareGoal' minus the parse step: canonicalize the arguments of a
-- goal 'Constraint' that is already in term form (built by the host
-- through "YCHR.Convert" or "YCHR.DSL", or recovered from a parse).
-- Throws 'RenameErrors' on failure.
prepareGoalTerm :: CompiledProgram -> Constraint -> IO (Constraint, [Warning])
prepareGoalTerm cp (Constraint cname cargs) = do
  (renamedArgs, ws) <-
    either
      (throwIO . RenameErrors)
      pure
      (renameQueryArgsWith cp.queryRenameEnv cargs)
  let warnings = [RenameWarnings ws | not (null ws)]
  pure (Constraint cname renamedArgs, warnings)

-- | Recover a 'Constraint' from a goal-parse validation error.
-- 'convertConstraint' rejects goals that are not constraint-shaped (a
-- bare literal, variable, or wildcard) with 'MalformedConstraint'. For a
-- /goal/ (unlike a rule head) this is the same failure category as
-- @1 + 1@ or @a, b@: synthesize a 0-arity goal name from the offending
-- term so the normal name-resolution path rejects it as
-- 'NoSuchConstraint' (YCHR-20013) at the same stage and with the same
-- code as other non-constraint goals — mirroring how the bare-atom goal
-- @true@ renders as @Goal \'true\/0\'@ — instead of the YCHR-15003
-- 'MalformedConstraint' reserved for malformed rule heads. The catch-all
-- keeps any other validation error (none are emitted today) on its
-- original path.
goalShapeConstraint ::
  AnnP ParseValidationError -> Either (AnnP ParseValidationError) Constraint
goalShapeConstraint (AnnP MalformedConstraint _ pexpr) =
  Right (Constraint (Types.Unqualified (T.pack (prettyPExprSrc pexpr))) [])
goalShapeConstraint other = Left other

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
      | null errs -> do
          -- Only the errors are consumed here: this entry point has
          -- no warning channel, and the one warning the checker can
          -- emit (YCHR-20104) needs a guard, which a goal never has.
          -- Should a goal-level warning ever be added, this call
          -- needs one — 'prepareQuery', the multi-goal entry point,
          -- already surfaces them.
          result <-
            typeCheckGoals
              cp.desugaredProgram
              queryLoc
              (Just "query")
              [D.BodyTell qn exprs]
          pure result.errors
    -- Skip type-checking if name resolution failed or termToExpr
    -- raised diagnostics; the runtime path will surface the same
    -- errors with the same messages.
    _ -> pure []
  unless (null tcErrs) (throwIO (TypeErrors tcErrs))
  -- 'original' came from 'prepareGoal', so its arguments are already
  -- canonicalized; go straight to the runner instead of renaming again.
  runGoalConstraint cp hostCalls original

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
      progForCheck =
        D.Program
          { rules = cdp.rules,
            functions = cdp.functions ++ lambdas,
            constraintTypes = cdp.constraintTypes,
            constraintBounds = cdp.constraintBounds,
            typeDefinitions = cdp.typeDefinitions
          }
  tcResult <- typeCheckGoals progForCheck queryLoc (Just "query") lifted
  unless (null tcResult.errors) (throwIO (TypeErrors tcResult.errors))
  let allFuns = cp.allFunctions ++ lambdas
      queryProcs = compileQueryLambdas lambdas
      queryDispatches = genCallFunDispatches allFuns
      warnings =
        [RenameWarnings renameWs | not (null renameWs)]
          ++ [TypeCheckWarnings tcResult.warnings | not (null tcResult.warnings)]
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
termToValue (TextTerm s) = pure (VText s)
termToValue Wildcard = pure VWildcard
-- Native-bool fast path. Mirrors 'Compile.compileTerm' for
-- @prelude:true@/@prelude:false@: the @=@-operand lowering must
-- produce 'VBool' so structural unification with comparison results
-- (which return 'VBool' directly) succeeds.
termToValue (CompoundTerm name []) | Just b <- Types.preludeBool name = pure (VBool b)
-- 0-arity ctors collapse to atoms at the runtime layer. Qualified
-- 0-arity uses the @vmName@-mangled @m__n@ form; unqualified 0-arity
-- (user-quoted atoms, undeclared bare names) keeps the raw name.
-- See 'YCHR.Internal.Compile.compileTerm' for the rationale.
termToValue (CompoundTerm name@(Types.Qualified _ _) []) =
  pure (VAtom (vmName name).unName)
termToValue (CompoundTerm (Types.Unqualified n) []) = pure (VAtom n)
termToValue (CompoundTerm name ts) = VTerm (vmName name).unName <$> traverse termToValue ts

-- | Execute a single desugared body goal in the query context.
executeBodyGoal :: D.BodyGoal -> QueryM ()
executeBodyGoal D.BodyTrue = pure ()
executeBodyGoal (D.BodyUnify l r) = do
  v1 <- exprToValue l
  v2 <- exprToValue r
  lift (queryUnify v1 v2)
executeBodyGoal (D.BodyHostStmt f args) = do
  argVals <- traverse evalNestedExpr args
  env <- lift ask
  result <- lift (hostCall (Map.lookup (Name f) env.hostCalls) f argVals)
  lift $
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
    R.VarExpr _ -> lift (deepEvalValue raw)
    _ -> pure raw
  varMap <- get
  case Map.lookup v varMap of
    Just existing -> lift (queryUnify existing result)
    Nothing -> modify (Map.insert v result)
executeBodyGoal (D.BodyTell qn args) = do
  argVals <- traverse evalNestedExpr args
  lift (tellConstraint (Types.qualifiedToName qn) argVals)
executeBodyGoal (D.BodyCall qn args) = do
  argVals <- traverse evalNestedExpr args
  let funcName = Types.qualifiedToName qn
  _ <- lift (callProc (funcProcName funcName (length argVals)) (map CVal argVals))
  pure ()
executeBodyGoal (D.BodyApply f args) = do
  fAndArgVals <- traverse evalNestedExpr (f : args)
  let n = length args
      dispatchName = Name ("call_" <> T.pack (show n))
  _ <- lift (callProc dispatchName (map CVal fAndArgVals))
  pure ()

-- | Raise a runtime error describing a failed unification.
raiseUnifyFailure :: Value -> Value -> Chr ()
raiseUnifyFailure v1 v2 = do
  t1 <- valueToTerm Map.empty v1
  t2 <- valueToTerm Map.empty v2
  runtimeErrorS $
    "unification failure: cannot unify "
      ++ prettyTerm t1
      ++ " with "
      ++ prettyTerm t2

-- | Call a host function, failing with a coded runtime error if it is not
-- registered or if it throws.
--
-- Mirrors 'YCHR.Internal.Runtime.Interpreter.invokeHostCall': an
-- arbitrary exception out of a host function (an 'IOException' from a
-- user 'YCHR.Convert.hostFnValues' handler, a parse failure inside a
-- built-in) is re-raised through 'runtimeErrorS' so it reaches the caller
-- as 'Error''s 'RuntimeError' with a call stack, rather than escaping raw.
-- Async and already-coded exceptions keep their identity.
--
-- Unlike 'invokeHostCall' there is no @ControlFlow@ case: that exception
-- is interpreter-internal, is caught by 'callProc' before control
-- returns, and is not exported — so no 'HostCallFn' reachable from here,
-- built-in or user-supplied, can raise it.
hostCall :: Maybe HostCallFn -> Text -> [Value] -> Chr Value
hostCall (Just (HostCallFn f)) name args = do
  env <- ask
  result <- liftIO (try @SomeException (runReaderT (f args) env))
  case result of
    Right v -> pure v
    Left exc
      | Just (ae :: SomeAsyncException) <- fromException exc ->
          liftIO (throwIO ae)
      | Just (rte :: RuntimeErrorThrown) <- fromException exc ->
          liftIO (throwIO rte)
      | otherwise ->
          runtimeErrorS $
            "host call " ++ T.unpack name ++ ": " ++ displayException exc
hostCall Nothing name _ =
  runtimeErrorS $ "Unknown host function: " ++ T.unpack name

-- | Drain the reactivation queue, dispatching each constraint.
-- Mirrors the VM's 'DrainReactivationQueue' statement, including
-- the per-suspension 'TEReactivate' event for the tracer.
drainReactivation :: Chr ()
drainReactivation =
  drainQueue $ \sid -> do
    alive <- aliveConstraint sid
    when alive $ do
      emitTrace $ do
        (ct, vs) <- suspensionView sid
        ctName <- constraintTypeLabel ct
        ts <- snapshotValues vs
        pure (TEReactivate sid ctName ts)
      void $ callProc (Name "reactivate_dispatch") [CId sid]

-- | Run a query-side unification, mirroring the interpreter's
-- 'evalBoolExpr (BUnify ...)' branch: snapshot the operand terms
-- /before/ the unify mutates anything (only when tracing is on),
-- run the unify, enqueue observers, emit a 'TEUnify' event on
-- success with the number of observers reactivated, raise on
-- failure, then drain the reactivation queue. The trace event is
-- skipped on failure for consistency with the interpreter path.
queryUnify :: Value -> Value -> Chr ()
queryUnify v1 v2 = do
  env <- ask
  mh <- liftIO (readIORef env.traceHandler)
  case mh of
    Nothing -> do
      (ok, observers) <- unify v1 v2
      enqueueObservers observers
      unless ok (raiseUnifyFailure v1 v2)
      drainReactivation
    Just _ -> do
      t1 <- snapshotValue v1
      t2 <- snapshotValue v2
      (ok, observers) <- unify v1 v2
      enqueueObservers observers
      if ok
        then do
          emitTrace (pure (TEUnify t1 t2 (length observers)))
          drainReactivation
        else raiseUnifyFailure v1 v2

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
-- 'CtorExpr' (and the @quote\/1@ quoting form) build values
-- structurally without re-evaluating their children.
evalNestedExpr :: D.Expr -> QueryM Value
evalNestedExpr (R.IntExpr n) = pure (VInt n)
evalNestedExpr (R.FloatExpr n) = pure (VFloat n)
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
-- @quote(X)@ short-circuit: build the inner value as data, no
-- nested-call evaluation. Mirrors the legacy 'termToValue arg' path.
evalNestedExpr (R.CtorExpr (Types.Unqualified "quote") [arg]) = exprToValue arg
-- Native-bool fast path. Mirrors 'Compile.compileExpr' for
-- @prelude:true@/@prelude:false@: queries must produce 'VBool' just
-- like compiled rules, so a REPL @is@ RHS or tell-side argument
-- agrees with comparison results (which return 'VBool' directly).
evalNestedExpr (R.CtorExpr name []) | Just b <- Types.preludeBool name = pure (VBool b)
-- 0-arity ctors collapse to atoms at the runtime layer.
evalNestedExpr (R.CtorExpr name@(Types.Qualified _ _) []) =
  pure (VAtom (vmName name).unName)
evalNestedExpr (R.CtorExpr (Types.Unqualified n) []) = pure (VAtom n)
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
