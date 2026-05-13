{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Haskell interpreter for CHR VM programs.
--
-- Executes VM programs directly using the 'Chr' runtime monad. The
-- 'Chr' monad reads a 'SessionEnv' that bundles the constraint store,
-- propagation history, reactivation queue, unification-variable
-- counter, interpreter call stack, the procedure map and the host-call
-- registry. Per-procedure-call local variables ('Env') live in a
-- mutable 'IORef' read through a thin 'ReaderT' layer so exception-driven
-- non-local jumps preserve state across catches.
--
-- Non-local control flow ('Return', labelled 'Continue', 'Break') is
-- implemented with real 'Control.Exception' exceptions thrown in 'IO':
-- 'try' delimits each procedure invocation and each 'Foreach' body.
module YCHR.Runtime.Interpreter
  ( -- * Public API
    interpret,
    HostCallFn (..),
    HostCallRegistry,
    baseHostCallRegistry,

    -- * Internal (for testing)
    callProc,
    bindParams,
    unit,
  )
where

import Control.Exception
  ( Exception,
    SomeAsyncException,
    SomeException,
    bracket,
    displayException,
    fromException,
    throwIO,
    try,
  )
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ReaderT, ask, runReaderT)
import Data.Foldable (toList, traverse_)
import Data.IORef (IORef, atomicModifyIORef', modifyIORef', newIORef, readIORef, writeIORef)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import YCHR.Meta (valueToTerm)
import YCHR.Pretty (prettyTerm)
import YCHR.Runtime.Error (RuntimeErrorThrown, runtimeError', runtimeErrorS)
import YCHR.Runtime.History (addHistory, notInHistory)
import YCHR.Runtime.Monad
  ( Chr,
    HostCallFn (..),
    HostCallRegistry,
    SessionEnv (..),
    initSessionEnv,
    runChr,
  )
import YCHR.Runtime.Reactivation (drainQueue, enqueue)
import YCHR.Runtime.Registry
  ( baseHostCallRegistry,
    unit,
  )
import YCHR.Runtime.Store
  ( Suspension (..),
    aliveConstraint,
    createConstraint,
    getConstraintArg,
    getConstraintType,
    getStoreSnapshot,
    idEqual,
    isConstraintType,
    isSuspAlive,
    killConstraint,
    storeConstraint,
    suspArg,
  )
import YCHR.Runtime.Types (CallVal (..), SuspensionId, Value (..))
import YCHR.Runtime.Var
  ( deref,
    equal,
    getArg,
    makeTerm,
    matchTerm,
    newVar,
    unify,
  )
import YCHR.VM

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

-- | Local variable environment for a procedure call. Split by kind:
-- value-bound names live in 'envValues', id-bound names in 'envIds'.
-- The IR ensures each name appears in only one map.
data Env = Env
  { envValues :: !(Map Name Value),
    envIds :: !(Map Name SuspensionId)
  }

emptyEnv :: Env
emptyEnv = Env Map.empty Map.empty

insertVal :: Name -> Value -> Env -> Env
insertVal n v e = e {envValues = Map.insert n v e.envValues}

insertId :: Name -> SuspensionId -> Env -> Env
insertId n s e = e {envIds = Map.insert n s e.envIds}

-- | Maximum number of call stack frames to keep.
maxCallStackDepth :: Int
maxCallStackDepth = 10

-- | Non-local control flow signals. Thrown as exceptions to escape
-- the current procedure or 'Foreach' loop and caught at the matching
-- boundary. 'CFReturn' is caught by 'callProc'; 'CFContinue' / 'CFBreak'
-- by 'execForeach' on its labelled loop.
data ControlFlow
  = CFReturn Value
  | CFContinue Label
  | CFBreak Label

instance Show ControlFlow where
  show (CFReturn _) = "CFReturn <val>"
  show (CFContinue l) = "CFContinue " ++ T.unpack l.unLabel
  show (CFBreak l) = "CFBreak " ++ T.unpack l.unLabel

instance Exception ControlFlow

-- | The interpreter's local stack: an 'IORef Env' threaded above 'Chr'.
-- Using a ref lets exception-driven jumps preserve any state changes
-- made before the jump, matching the original effectful-static-Local
-- 'runError'-with-outer-state semantics.
type InterpM = ReaderT (IORef Env) Chr

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

-- | Interpret a VM program by calling a named procedure with the given
-- value arguments. Builds a fresh 'SessionEnv' for the program and
-- runs the call inside it.
interpret :: Program -> HostCallRegistry -> Name -> [Value] -> IO Value
interpret prog hostCalls entryName args = do
  let procMap = Map.fromList [(p.name, p) | p <- prog.procedures]
  env <- initSessionEnv prog.typeNames procMap hostCalls Map.empty mempty
  runChr (callProc entryName (map CVal args)) env

-- ---------------------------------------------------------------------------
-- Env helpers
-- ---------------------------------------------------------------------------

getEnv :: InterpM Env
getEnv = do
  ref <- ask
  liftIO (readIORef ref)

modifyEnv :: (Env -> Env) -> InterpM ()
modifyEnv f = do
  ref <- ask
  liftIO (modifyIORef' ref f)

withFreshEnv :: Env -> InterpM a -> Chr a
withFreshEnv env action = do
  ref <- liftIO (newIORef env)
  runReaderT action ref

-- ---------------------------------------------------------------------------
-- Session helpers
-- ---------------------------------------------------------------------------

lookupProc :: Name -> Chr (Maybe Procedure)
lookupProc name = do
  SessionEnv {procMap} <- ask
  pm <- liftIO (readIORef procMap)
  pure (Map.lookup name pm)

lookupHostCall :: Name -> Chr (Maybe HostCallFn)
lookupHostCall name = do
  SessionEnv {hostCalls} <- ask
  pure (Map.lookup name hostCalls)

pushFrame :: StackFrame -> Chr ()
pushFrame frame = do
  SessionEnv {callStack} <- ask
  liftIO $
    atomicModifyIORef' callStack $ \stack ->
      (take maxCallStackDepth (frame : stack), ())

-- | Save the call stack, run @action@, and restore the saved frames
-- on the way out — whether @action@ returns normally or throws. The
-- restore-on-throw matters because the REPL's outer @try@ may catch
-- a 'RuntimeErrorThrown' that escapes a procedure call; without
-- bracketing, frames pushed during the failed call would leak into
-- the next operation that observes the same 'SessionEnv'.
withSavedCallStack :: Chr a -> Chr a
withSavedCallStack action = do
  env@SessionEnv {callStack} <- ask
  liftIO $
    bracket
      (readIORef callStack)
      (writeIORef callStack)
      (\_ -> runChr action env)

-- | Catch a 'ControlFlow' exception thrown inside a 'Chr' action.
-- Uses 'try' at the 'IO' layer so the action's state changes (in
-- 'SessionEnv' refs and in any 'InterpM' env ref currently in scope)
-- survive the catch.
tryControlFlow :: Chr a -> Chr (Either ControlFlow a)
tryControlFlow m = do
  env <- ask
  liftIO (try (runChr m env))

-- ---------------------------------------------------------------------------
-- Core interpreter
-- ---------------------------------------------------------------------------

-- | Call a procedure. Creates a fresh local 'Env' with parameter
-- bindings, executes the body, and catches 'CFReturn'. Default
-- return: 'VBool False'.
callProc :: Name -> [CallVal] -> Chr Value
callProc name args = do
  mproc <- lookupProc name
  case mproc of
    Nothing -> runtimeError' "callProc: unknown procedure " name.unName
    Just proc -> do
      env <- case bindParams name proc.params args of
        Right e -> pure e
        Left msg -> runtimeErrorS msg
      withSavedCallStack $ do
        result <- tryControlFlow (withFreshEnv env (execStmts proc.body))
        case result of
          Right () -> pure (VBool False)
          Left (CFReturn v) -> pure v
          Left (CFContinue l) -> runtimeError' "callProc: uncaught Continue " l.unLabel
          Left (CFBreak l) -> runtimeError' "callProc: uncaught Break " l.unLabel

-- | Bind procedure parameters into the appropriate environment slot
-- based on the runtime tag of each argument.
bindParams :: Name -> [Name] -> [CallVal] -> Either String Env
bindParams pname params args
  | length params /= length args =
      Left $
        "bindParams: arity mismatch in "
          ++ T.unpack pname.unName
          ++ ": "
          ++ show (length params)
          ++ " params, "
          ++ show (length args)
          ++ " args"
  | otherwise = Right (foldl' step emptyEnv (zip params args))
  where
    step e (p, CVal v) = insertVal p v e
    step e (p, CId s) = insertId p s e

-- | Execute a list of statements sequentially.
execStmts :: [Stmt] -> InterpM ()
execStmts = traverse_ execStmt

-- | Execute a single statement.
execStmt :: Stmt -> InterpM ()
execStmt (LetVal name expr) = do
  v <- evalValExpr expr
  modifyEnv (insertVal name v)
execStmt (LetId name expr) = do
  s <- evalIdExpr expr
  modifyEnv (insertId name s)
execStmt (AssignVal name expr) = do
  v <- evalValExpr expr
  modifyEnv (insertVal name v)
execStmt (AssignId name expr) = do
  s <- evalIdExpr expr
  modifyEnv (insertId name s)
execStmt (If cond thenBranch elseBranch) = do
  b <- evalBoolExpr cond
  if b then execStmts thenBranch else execStmts elseBranch
execStmt (Foreach lbl cType suspVar conditions body) = do
  snapshot <- lift (getStoreSnapshot cType)
  let susps = toList snapshot
  execForeach lbl suspVar conditions body susps
execStmt (Continue lbl) = liftIO (throwIO (CFContinue lbl))
execStmt (Break lbl) = liftIO (throwIO (CFBreak lbl))
execStmt (Return expr) = do
  v <- evalValExpr expr
  liftIO (throwIO (CFReturn v))
execStmt (ExprStmt expr) = do
  _ <- evalValExpr expr
  pure ()
execStmt (BoolExprStmt expr) = do
  _ <- evalBoolExpr expr
  pure ()
execStmt (Store expr) = do
  sid <- evalIdExpr expr
  lift (storeConstraint sid)
execStmt (Kill expr) = do
  sid <- evalIdExpr expr
  lift (killConstraint sid)
execStmt (AddHistory ruleId exprs) = do
  sids <- traverse evalIdExpr exprs
  lift (addHistory ruleId sids)
execStmt (DrainReactivationQueue suspVar body) = do
  envRef <- ask
  lift $
    drainQueue $ \sid -> do
      alive <- aliveConstraint sid
      if alive
        then do
          liftIO (modifyIORef' envRef (insertId suspVar sid))
          runReaderT (execStmts body) envRef
        else pure ()
execStmt (PushFrame frame) = lift (pushFrame frame)

-- ---------------------------------------------------------------------------
-- Foreach implementation
-- ---------------------------------------------------------------------------

execForeach ::
  Label ->
  Name ->
  [(ArgIndex, ValExpr)] ->
  [Stmt] ->
  [Suspension] ->
  InterpM ()
execForeach _ _ _ _ [] = pure ()
execForeach lbl suspVar conditions body (susp : rest) = do
  alive <- lift (isSuspAlive susp)
  if not alive
    then execForeach lbl suspVar conditions body rest
    else do
      ok <- checkConditions susp conditions
      if not ok
        then execForeach lbl suspVar conditions body rest
        else do
          modifyEnv (insertId suspVar susp.suspId)
          envRef <- ask
          result <- lift (tryControlFlow (runReaderT (execStmts body) envRef))
          case result of
            Right () -> execForeach lbl suspVar conditions body rest
            Left (CFContinue l)
              | l == lbl -> execForeach lbl suspVar conditions body rest
              | otherwise -> liftIO (throwIO (CFContinue l))
            Left (CFBreak l)
              | l == lbl -> pure ()
              | otherwise -> liftIO (throwIO (CFBreak l))
            Left cf@(CFReturn _) -> liftIO (throwIO cf)

checkConditions :: Suspension -> [(ArgIndex, ValExpr)] -> InterpM Bool
checkConditions _ [] = pure True
checkConditions susp ((ArgIndex i, expr) : rest) = do
  v <- evalValExpr expr
  let argVal = suspArg susp i
  eq <- lift (equal v argVal)
  if eq
    then checkConditions susp rest
    else pure False

-- ---------------------------------------------------------------------------
-- Value-expression evaluator (normal mode)
-- ---------------------------------------------------------------------------

evalValExpr :: ValExpr -> InterpM Value
evalValExpr (Var name) = do
  env <- getEnv
  case Map.lookup name env.envValues of
    Just v -> pure v
    Nothing -> lift (runtimeError' "evalValExpr: unbound variable " name.unName)
evalValExpr (Lit (IntLit n)) = pure (VInt n)
evalValExpr (Lit (FloatLit n)) = pure (VFloat n)
evalValExpr (Lit (AtomLit s)) = pure (VAtom s)
evalValExpr (Lit (TextLit s)) = pure (VText s)
evalValExpr (Lit (BoolLit b)) = pure (VBool b)
evalValExpr (Lit WildcardLit) = pure VWildcard
evalValExpr (CallExpr name args) = do
  argVals <- traverse evalCallArg args
  lift (callProc name argVals)
evalValExpr (HostCall name args) = do
  argVals <- traverse evalValExpr args
  derefedVals <- lift (traverse deref argVals)
  lift (invokeHostCall name derefedVals)
evalValExpr NewVar = lift newVar
evalValExpr (MakeTerm functor args) = do
  argVals <- traverse evalValExpr args
  pure $ makeTerm functor.unName argVals
evalValExpr (GetArg expr idx) = do
  v <- evalValExpr expr
  lift (getArg v idx)
evalValExpr (FieldArg expr (ArgIndex i)) = do
  sid <- evalIdExpr expr
  lift (getConstraintArg sid i)
evalValExpr (FieldType expr) = do
  sid <- evalIdExpr expr
  ct <- lift (getConstraintType sid)
  pure (VInt ct.unConstraintType)
evalValExpr (EvalDeep expr) = evalValExprDeep expr

-- ---------------------------------------------------------------------------
-- Bool-expression evaluator (normal mode)
-- ---------------------------------------------------------------------------

evalBoolExpr :: BoolExpr -> InterpM Bool
evalBoolExpr (BLit b) = pure b
evalBoolExpr (BNot e) = not <$> evalBoolExpr e
evalBoolExpr (BAnd e1 e2) = do
  b1 <- evalBoolExpr e1
  if b1 then evalBoolExpr e2 else pure False
evalBoolExpr (BOr e1 e2) = do
  b1 <- evalBoolExpr e1
  if b1 then pure True else evalBoolExpr e2
evalBoolExpr (BMatchTerm expr functor arity) = do
  v <- evalValExpr expr
  lift (matchTerm v functor.unName arity)
evalBoolExpr (BEqual e1 e2) = do
  v1 <- evalValExpr e1
  v2 <- evalValExpr e2
  lift (equal v1 v2)
evalBoolExpr (BIdEqual e1 e2) = do
  s1 <- evalIdExpr e1
  s2 <- evalIdExpr e2
  pure (idEqual s1 s2)
evalBoolExpr (BAlive expr) = do
  sid <- evalIdExpr expr
  lift (aliveConstraint sid)
evalBoolExpr (BIsConstraintType expr cType) = do
  sid <- evalIdExpr expr
  lift (isConstraintType sid cType)
evalBoolExpr (BNotInHistory ruleId args) = do
  sids <- traverse evalIdExpr args
  lift (notInHistory ruleId sids)
evalBoolExpr (BUnify e1 e2) = do
  v1 <- evalValExpr e1
  v2 <- evalValExpr e2
  (ok, observers) <- lift (unify v1 v2)
  lift (enqueue observers)
  if ok
    then pure True
    else do
      t1 <- lift (valueToTerm Map.empty v1)
      t2 <- lift (valueToTerm Map.empty v2)
      lift $
        runtimeErrorS $
          "unification failure: cannot unify "
            ++ prettyTerm t1
            ++ " with "
            ++ prettyTerm t2
evalBoolExpr (BFromVal expr) = do
  v <- evalValExpr expr
  case v of
    VBool b -> pure b
    _ -> lift (runtimeErrorS "BFromVal: expected boolean")
evalBoolExpr (BEvalDeep expr) = evalBoolExprDeep expr

-- ---------------------------------------------------------------------------
-- Id-expression evaluator
-- ---------------------------------------------------------------------------

evalIdExpr :: IdExpr -> InterpM SuspensionId
evalIdExpr (IdVar name) = do
  env <- getEnv
  case Map.lookup name env.envIds of
    Just s -> pure s
    Nothing -> lift (runtimeError' "evalIdExpr: unbound id variable " name.unName)
evalIdExpr (CreateConstraint cType args) = do
  argVals <- traverse evalValExpr args
  lift (createConstraint cType argVals)

-- ---------------------------------------------------------------------------
-- Call-arg evaluator
-- ---------------------------------------------------------------------------

evalCallArg :: CallArg -> InterpM CallVal
evalCallArg (AVal e) = CVal <$> evalValExpr e
evalCallArg (AId e) = CId <$> evalIdExpr e

-- ---------------------------------------------------------------------------
-- Host call dispatch
-- ---------------------------------------------------------------------------

invokeHostCall :: Name -> [Value] -> Chr Value
invokeHostCall name argVals = do
  mfn <- lookupHostCall name
  case mfn of
    Just (HostCallFn f) -> do
      env <- ask
      -- Only synchronous, non-control-flow exceptions thrown by the
      -- host call body get wrapped as runtime errors. 'ControlFlow'
      -- (interpreter-internal: Return/Continue/Break) and async
      -- exceptions (Ctrl+C, thread kill) must keep their identity so
      -- they reach their intended handler; 'RuntimeErrorThrown' is
      -- re-thrown verbatim so nested host calls preserve the original
      -- message and stack frames.
      result <- liftIO (try @SomeException (runChr (f argVals) env))
      case result of
        Right v -> pure v
        Left exc
          | Just (cf :: ControlFlow) <- fromException exc ->
              liftIO (throwIO cf)
          | Just (ae :: SomeAsyncException) <- fromException exc ->
              liftIO (throwIO ae)
          | Just (rte :: RuntimeErrorThrown) <- fromException exc ->
              liftIO (throwIO rte)
          | otherwise ->
              runtimeErrorS $
                "host call " ++ T.unpack name.unName ++ ": " ++ displayException exc
    Nothing -> runtimeError' "evalValExpr: unknown host call " name.unName

-- ---------------------------------------------------------------------------
-- Value-expression evaluator (deep deref mode)
-- ---------------------------------------------------------------------------

-- | Evaluate a value expression with automatic dereferencing: variable
-- references follow binding chains before use, and this mode propagates
-- into sub-expressions. Used to implement 'EvalDeep' (guards and @is@ RHS).
evalValExprDeep :: ValExpr -> InterpM Value
evalValExprDeep (Var name) = do
  v <- evalValExpr (Var name)
  lift (deref v)
evalValExprDeep (HostCall name args) = do
  argVals <- traverse evalValExprDeep args
  lift (invokeHostCall name argVals)
evalValExprDeep (CallExpr name args) = do
  argVals <- traverse evalCallArgDeep args
  lift (callProc name argVals)
evalValExprDeep (MakeTerm functor args) = do
  argVals <- traverse evalValExprDeep args
  pure $ makeTerm functor.unName argVals
evalValExprDeep expr = evalValExpr expr

evalCallArgDeep :: CallArg -> InterpM CallVal
evalCallArgDeep (AVal e) = CVal <$> evalValExprDeep e
evalCallArgDeep (AId e) = CId <$> evalIdExpr e

-- ---------------------------------------------------------------------------
-- Bool-expression evaluator (deep deref mode)
-- ---------------------------------------------------------------------------

-- | Deep-deref evaluation for 'BoolExpr'. Mirrors 'evalValExprDeep':
-- propagates deep mode into 'ValExpr' and 'IdExpr' payloads.
evalBoolExprDeep :: BoolExpr -> InterpM Bool
evalBoolExprDeep (BNot e) = not <$> evalBoolExprDeep e
evalBoolExprDeep (BAnd e1 e2) = do
  b1 <- evalBoolExprDeep e1
  if b1 then evalBoolExprDeep e2 else pure False
evalBoolExprDeep (BOr e1 e2) = do
  b1 <- evalBoolExprDeep e1
  if b1 then pure True else evalBoolExprDeep e2
evalBoolExprDeep (BMatchTerm expr functor arity) = do
  v <- evalValExprDeep expr
  lift (matchTerm v functor.unName arity)
evalBoolExprDeep (BEqual e1 e2) = do
  v1 <- evalValExprDeep e1
  v2 <- evalValExprDeep e2
  lift (equal v1 v2)
evalBoolExprDeep (BUnify e1 e2) = do
  v1 <- evalValExprDeep e1
  v2 <- evalValExprDeep e2
  (ok, observers) <- lift (unify v1 v2)
  lift (enqueue observers)
  if ok
    then pure True
    else do
      t1 <- lift (valueToTerm Map.empty v1)
      t2 <- lift (valueToTerm Map.empty v2)
      lift $
        runtimeErrorS $
          "unification failure: cannot unify "
            ++ prettyTerm t1
            ++ " with "
            ++ prettyTerm t2
evalBoolExprDeep (BFromVal expr) = do
  v <- evalValExprDeep expr
  case v of
    VBool b -> pure b
    _ -> lift (runtimeErrorS "BFromVal: expected boolean")
evalBoolExprDeep (BEvalDeep expr) = evalBoolExprDeep expr
evalBoolExprDeep expr = evalBoolExpr expr
