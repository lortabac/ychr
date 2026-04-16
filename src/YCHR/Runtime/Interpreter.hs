{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

-- | Haskell interpreter for CHR VM programs.
--
-- Executes VM programs directly using the Haskell runtime effects
-- (Unify, CHRStore, PropHistory, ReactQueue). This enables testing
-- the compilation scheme end-to-end before building JS/Scheme backends.
module YCHR.Runtime.Interpreter
  ( -- * Public API
    interpret,
    HostCallFn (..),
    HostCallRegistry,
    baseHostCallRegistry,

    -- * Internal (for testing)
    callProc,
    unit,
  )
where

import Control.Exception (SomeException, displayException)
import Data.Foldable (toList, traverse_)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Effectful
import Effectful.Error.Static (Error, runError, throwError)
import Effectful.Exception qualified as Eff
import Effectful.State.Static.Local (State, evalState, get, modify, put)
import Effectful.Writer.Static.Local (Writer, listen, runWriter)
import System.Exit (exitFailure)
import System.IO (hPutStr, stderr)
import YCHR.Meta (valueToTerm)
import YCHR.Pretty (prettyTerm)
import YCHR.Runtime.Error (displayRuntimeError)
import YCHR.Runtime.History (PropHistory, addHistory, notInHistory, runPropHistory)
import YCHR.Runtime.Reactivation (ReactQueue, drainQueue, enqueue, runReactQueue)
import YCHR.Runtime.Registry (HostCallFn (..), HostCallRegistry, baseHostCallRegistry, toValue, unit)
import YCHR.Runtime.Store
  ( CHRStore,
    Suspension (..),
    aliveConstraint,
    createConstraint,
    getConstraintArg,
    getConstraintType,
    getStoreSnapshot,
    idEqual,
    isConstraintType,
    isSuspAlive,
    killConstraint,
    runCHRStore,
    storeConstraint,
    suspArg,
  )
import YCHR.Runtime.Types (RuntimeVal (..), SuspensionId (..), Value (..))
import YCHR.Runtime.Var (Unify, deref, equal, getArg, makeTerm, matchTerm, newVar, runUnify, unify)
import YCHR.VM

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

-- | Map from procedure name to procedure definition.
type ProcMap = Map Name Procedure

-- | Local variable environment for a procedure call.
type Env = Map Name RuntimeVal

-- | Maximum number of call stack frames to keep.
maxCallStackDepth :: Int
maxCallStackDepth = 10

-- | Runtime call stack for error reporting (newest first).
type CallStack = [StackFrame]

-- | Non-local control flow signals. We use 'Effectful.Error.Static.Error'
-- as an exception mechanism: 'Return' exits a procedure, 'Continue' and
-- 'Break' target labeled 'Foreach' loops.
data ControlFlow
  = CFReturn RuntimeVal
  | CFContinue Label
  | CFBreak Label

instance Show ControlFlow where
  show (CFReturn _) = "CFReturn <val>"
  show (CFContinue l) = "CFContinue " ++ T.unpack l.unLabel
  show (CFBreak l) = "CFBreak " ++ T.unpack l.unLabel

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

-- | Interpret a VM program by calling a named procedure with the given arguments.
interpret :: Program -> HostCallRegistry -> Name -> [Value] -> IO RuntimeVal
interpret prog hostCalls entryName args = do
  let procMap = Map.fromList [(p.name, p) | p <- prog.procedures]
      argVals = map RVal args
  runEff
    . runUnifyWithWriter
    . runCHRStoreEff
    . runPropHistoryEff
    . runReactQueueEff
    . evalState @CallStack []
    $ callProc procMap hostCalls entryName argVals
  where
    -- Run Unify with a Writer layer for observer collection.
    -- The Writer is run inside Unify so it's available to unify calls.
    runUnifyWithWriter m =
      YCHR.Runtime.Var.runUnify
        . fmap fst
        . runWriter @[SuspensionId]
        $ m
    runCHRStoreEff = YCHR.Runtime.Store.runCHRStore prog.typeNames
    runPropHistoryEff = YCHR.Runtime.History.runPropHistory
    runReactQueueEff = YCHR.Runtime.Reactivation.runReactQueue

-- ---------------------------------------------------------------------------
-- Core interpreter
-- ---------------------------------------------------------------------------

-- | The effect constraints needed by the interpreter.
type InterpEffects es =
  ( IOE :> es,
    Writer [SuspensionId] :> es,
    Unify :> es,
    CHRStore :> es,
    PropHistory :> es,
    ReactQueue :> es,
    State CallStack :> es
  )

-- | Call a procedure. Creates a fresh environment with parameter bindings,
-- executes the body, and catches CFReturn. Default return: RVal (VBool False).
callProc ::
  (InterpEffects es) =>
  ProcMap -> HostCallRegistry -> Name -> [RuntimeVal] -> Eff es RuntimeVal
callProc procMap hostCalls name args = do
  case Map.lookup name procMap of
    Nothing -> runtimeError' "callProc: unknown procedure " name.unName
    Just proc -> do
      let env = Map.fromList (zip proc.params args)
      savedStack <- get @CallStack
      result <-
        evalState env
          . runError @ControlFlow
          $ execStmts procMap hostCalls proc.body
      put @CallStack savedStack
      case result of
        Right () -> pure (RVal (VBool False))
        Left (_, CFReturn v) -> pure v
        Left (_, CFContinue l) -> runtimeError' "callProc: uncaught Continue " l.unLabel
        Left (_, CFBreak l) -> runtimeError' "callProc: uncaught Break " l.unLabel

-- | Execute a list of statements sequentially.
execStmts ::
  (InterpEffects es, State Env :> es, Error ControlFlow :> es) =>
  ProcMap -> HostCallRegistry -> [Stmt] -> Eff es ()
execStmts procMap hostCalls = traverse_ (execStmt procMap hostCalls)

-- | Execute a single statement.
execStmt ::
  (InterpEffects es, State Env :> es, Error ControlFlow :> es) =>
  ProcMap -> HostCallRegistry -> Stmt -> Eff es ()
execStmt pm hc (Let name expr) = do
  v <- evalVmExpr pm hc expr
  modify (Map.insert name v)
execStmt pm hc (Assign name expr) = do
  v <- evalVmExpr pm hc expr
  modify (Map.insert name v)
execStmt pm hc (If cond thenBranch elseBranch) = do
  c <- evalVmExpr pm hc cond
  case c of
    RVal (VBool True) -> execStmts pm hc thenBranch
    RVal (VBool False) -> execStmts pm hc elseBranch
    _ -> runtimeErrorS "If: condition is not a boolean"
execStmt pm hc (Foreach lbl cType suspVar conditions body) = do
  snapshot <- getStoreSnapshot cType
  let susps = toList snapshot
  execForeach pm hc lbl suspVar conditions body susps
execStmt _ _ (Continue lbl) = throwError (CFContinue lbl)
execStmt _ _ (Break lbl) = throwError (CFBreak lbl)
execStmt pm hc (Return expr) = do
  v <- evalVmExpr pm hc expr
  throwError (CFReturn v)
execStmt pm hc (ExprStmt expr) = do
  _ <- evalVmExpr pm hc expr
  pure ()
execStmt pm hc (Store expr) = do
  v <- evalVmExpr pm hc expr
  case v of
    RConstraint sid -> storeConstraint sid
    _ -> runtimeErrorS "Store: expected constraint identifier"
execStmt pm hc (Kill expr) = do
  v <- evalVmExpr pm hc expr
  case v of
    RConstraint sid -> killConstraint sid
    _ -> runtimeErrorS "Kill: expected constraint identifier"
execStmt pm hc (AddHistory ruleId exprs) = do
  ids <- traverse (evalVmExpr pm hc) exprs
  sids <- traverse expectConstraintId ids
  addHistory ruleId sids
execStmt pm hc (DrainReactivationQueue suspVar body) = do
  drainQueue $ \sid -> do
    alive <- aliveConstraint sid
    if alive
      then do
        modify (Map.insert suspVar (RConstraint sid))
        execStmts pm hc body
      else pure ()
execStmt _ _ (PushFrame frame) = do
  modify @CallStack $ \stack ->
    take maxCallStackDepth (frame : stack)

-- ---------------------------------------------------------------------------
-- Runtime errors
-- ---------------------------------------------------------------------------

-- | Raise a runtime error with the current call stack.
-- Prints the formatted error to stderr and exits.
runtimeError' ::
  (IOE :> es, State CallStack :> es) =>
  String -> T.Text -> Eff es a
runtimeError' prefix detail = do
  stack <- get @CallStack
  liftIO $ do
    hPutStr stderr $ displayRuntimeError (prefix ++ T.unpack detail) stack
    exitFailure

-- | Raise a runtime error with the current call stack (String-only variant).
-- Prints the formatted error to stderr and exits.
runtimeErrorS ::
  (IOE :> es, State CallStack :> es) =>
  String -> Eff es a
runtimeErrorS msg = do
  stack <- get @CallStack
  liftIO $ do
    hPutStr stderr $ displayRuntimeError msg stack
    exitFailure

-- | Extract a constraint identifier from a runtime value, or raise a runtime error.
expectConstraintId ::
  (IOE :> es, State CallStack :> es) =>
  RuntimeVal -> Eff es SuspensionId
expectConstraintId (RConstraint s) = pure s
expectConstraintId _ = runtimeErrorS "expected constraint identifier"

-- ---------------------------------------------------------------------------
-- Foreach implementation
-- ---------------------------------------------------------------------------

execForeach ::
  (InterpEffects es, State Env :> es, Error ControlFlow :> es) =>
  ProcMap ->
  HostCallRegistry ->
  Label ->
  Name ->
  [(ArgIndex, Expr)] ->
  [Stmt] ->
  [Suspension] ->
  Eff es ()
execForeach _ _ _ _ _ _ [] = pure ()
execForeach pm hc lbl suspVar conditions body (susp : rest) = do
  alive <- isSuspAlive susp
  if not alive
    then execForeach pm hc lbl suspVar conditions body rest
    else do
      -- Check index conditions
      ok <- checkConditions pm hc susp conditions
      if not ok
        then execForeach pm hc lbl suspVar conditions body rest
        else do
          let Suspension {suspId = sid} = susp
          modify (Map.insert suspVar (RConstraint sid))
          result <- runError @ControlFlow $ execStmts pm hc body
          case result of
            Right () ->
              execForeach pm hc lbl suspVar conditions body rest
            Left (_, CFContinue l)
              | l == lbl -> execForeach pm hc lbl suspVar conditions body rest
              | otherwise -> throwError (CFContinue l)
            Left (_, CFBreak l)
              | l == lbl -> pure () -- exit loop
              | otherwise -> throwError (CFBreak l)
            Left (_, cf@(CFReturn _)) -> throwError cf

checkConditions ::
  (InterpEffects es, State Env :> es, Error ControlFlow :> es) =>
  ProcMap -> HostCallRegistry -> Suspension -> [(ArgIndex, Expr)] -> Eff es Bool
checkConditions _ _ _ [] = pure True
checkConditions pm hc susp ((ArgIndex i, expr) : rest) = do
  v <- evalVmExpr pm hc expr
  let argVal = suspArg susp i
  eq <- equal (toValue v) argVal
  if eq
    then checkConditions pm hc susp rest
    else pure False

-- ---------------------------------------------------------------------------
-- Expression evaluator
-- ---------------------------------------------------------------------------

evalVmExpr ::
  (InterpEffects es, State Env :> es, Error ControlFlow :> es) =>
  ProcMap -> HostCallRegistry -> Expr -> Eff es RuntimeVal
evalVmExpr _ _ (Var name) = do
  env <- get
  case Map.lookup name env of
    Just v -> pure v
    Nothing -> runtimeError' "evalVmExpr: unbound variable " name.unName
evalVmExpr _ _ (Lit (IntLit n)) = pure (RVal (VInt n))
evalVmExpr _ _ (Lit (AtomLit s)) = pure (RVal (VAtom s))
evalVmExpr _ _ (Lit (TextLit s)) = pure (RVal (VText s))
evalVmExpr _ _ (Lit (BoolLit b)) = pure (RVal (VBool b))
evalVmExpr _ _ (Lit WildcardLit) = pure (RVal VWildcard)
evalVmExpr pm hc (CallExpr name args) = do
  argVals <- traverse (evalVmExpr pm hc) args
  callProc pm hc name argVals
evalVmExpr pm hc (HostCall name args) = do
  argVals <- traverse (evalVmExpr pm hc) args
  derefedVals <- traverse derefRV argVals
  case Map.lookup name hc of
    Just (HostCallFn f) -> do
      result <- Eff.try @SomeException (f derefedVals)
      case result of
        Right v -> pure v
        Left exc -> runtimeErrorS $ "host call " ++ T.unpack name.unName ++ ": " ++ displayException exc
    Nothing -> runtimeError' "evalVmExpr: unknown host call " name.unName
  where
    derefRV (RVal v) = RVal <$> deref v
    derefRV rc = pure rc
evalVmExpr pm hc (Not expr) = do
  v <- evalVmExpr pm hc expr
  case v of
    RVal (VBool b) -> pure (RVal (VBool (not b)))
    _ -> runtimeErrorS "Not: expected boolean"
evalVmExpr pm hc (And e1 e2) = do
  v1 <- evalVmExpr pm hc e1
  case v1 of
    RVal (VBool False) -> pure (RVal (VBool False))
    RVal (VBool True) -> evalVmExpr pm hc e2
    _ -> runtimeErrorS "And: expected boolean"
evalVmExpr pm hc (Or e1 e2) = do
  v1 <- evalVmExpr pm hc e1
  case v1 of
    RVal (VBool True) -> pure (RVal (VBool True))
    RVal (VBool False) -> evalVmExpr pm hc e2
    _ -> runtimeErrorS "Or: expected boolean"
evalVmExpr _ _ NewVar = RVal <$> newVar
evalVmExpr pm hc (MakeTerm functor args) = do
  argVals <- traverse (evalVmExpr pm hc) args
  pure $ RVal $ makeTerm functor.unName (map toValue argVals)
evalVmExpr pm hc (MatchTerm expr functor arity) = do
  v <- evalVmExpr pm hc expr
  RVal . VBool <$> matchTerm (toValue v) functor.unName arity
evalVmExpr pm hc (GetArg expr idx) = do
  v <- evalVmExpr pm hc expr
  RVal <$> getArg (toValue v) idx
evalVmExpr pm hc (CreateConstraint cType args) = do
  argVals <- traverse (evalVmExpr pm hc) args
  sid <- createConstraint cType (map toValue argVals)
  pure (RConstraint sid)
evalVmExpr pm hc (Alive expr) = do
  v <- evalVmExpr pm hc expr
  case v of
    RConstraint sid -> RVal . VBool <$> aliveConstraint sid
    _ -> runtimeErrorS "Alive: expected constraint identifier"
evalVmExpr pm hc (IdEqual e1 e2) = do
  v1 <- evalVmExpr pm hc e1
  v2 <- evalVmExpr pm hc e2
  case (v1, v2) of
    (RConstraint s1, RConstraint s2) -> pure (RVal (VBool (idEqual s1 s2)))
    _ -> runtimeErrorS "IdEqual: expected constraint identifiers"
evalVmExpr pm hc (IsConstraintType expr cType) = do
  v <- evalVmExpr pm hc expr
  case v of
    RConstraint sid -> RVal . VBool <$> isConstraintType sid cType
    _ -> runtimeErrorS "IsConstraintType: expected constraint identifier"
evalVmExpr pm hc (NotInHistory ruleId args) = do
  argVals <- traverse (evalVmExpr pm hc) args
  sids <- traverse expectConstraintId argVals
  RVal . VBool <$> notInHistory ruleId sids
evalVmExpr pm hc (Unify e1 e2) = do
  v1 <- evalVmExpr pm hc e1
  v2 <- evalVmExpr pm hc e2
  let val1 = toValue v1
      val2 = toValue v2
  (ok, observers) <- listen (unify val1 val2)
  enqueue observers
  if ok
    then pure (RVal (VBool True))
    else do
      t1 <- valueToTerm "_" val1
      t2 <- valueToTerm "_" val2
      runtimeErrorS $
        "unification failure: cannot unify "
          ++ prettyTerm t1
          ++ " with "
          ++ prettyTerm t2
evalVmExpr pm hc (Equal e1 e2) = do
  v1 <- evalVmExpr pm hc e1
  v2 <- evalVmExpr pm hc e2
  RVal . VBool <$> equal (toValue v1) (toValue v2)
evalVmExpr pm hc (FieldGet expr field) = do
  v <- evalVmExpr pm hc expr
  case v of
    RConstraint sid -> case field of
      FieldId -> pure (RConstraint sid)
      FieldArg (ArgIndex i) -> RVal <$> getConstraintArg sid i
      FieldType -> (\ct -> RVal (VInt ct.unConstraintType)) <$> getConstraintType sid
    _ -> runtimeErrorS "FieldGet: expected constraint identifier"
evalVmExpr pm hc (EvalDeep expr) = evalExpr pm hc expr

-- ---------------------------------------------------------------------------
-- evalExpr
-- ---------------------------------------------------------------------------

-- | Evaluate an expression with automatic dereferencing: variable
-- references follow binding chains before use, and this mode propagates
-- into sub-expressions. Used to implement 'EvalDeep' (guards and @is@ RHS).
evalExpr ::
  (InterpEffects es, State Env :> es, Error ControlFlow :> es) =>
  ProcMap -> HostCallRegistry -> Expr -> Eff es RuntimeVal
evalExpr pm hc (Var name) = do
  v <- evalVmExpr pm hc (Var name)
  case v of
    RVal val -> RVal <$> deref val
    rv -> pure rv
evalExpr pm hc (HostCall name args) = do
  argVals <- traverse (evalExpr pm hc) args
  case Map.lookup name hc of
    Just (HostCallFn f) -> do
      result <- Eff.try @SomeException (f argVals)
      case result of
        Right v -> pure v
        Left exc -> runtimeErrorS $ "host call " ++ T.unpack name.unName ++ ": " ++ displayException exc
    Nothing -> runtimeError' "evalExpr: unknown host call " name.unName
evalExpr pm hc (CallExpr name args) = do
  argVals <- traverse (evalExpr pm hc) args
  callProc pm hc name argVals
evalExpr pm hc (MakeTerm functor args) = do
  argVals <- traverse (evalExpr pm hc) args
  pure $ RVal $ makeTerm functor.unName (map toValue argVals)
evalExpr pm hc expr = evalVmExpr pm hc expr
