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
    bindParams,
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
import YCHR.Meta (valueToTerm)
import YCHR.Pretty (prettyTerm)
import YCHR.Runtime.Error (CallStack, runtimeError', runtimeErrorS)
import YCHR.Runtime.History (PropHistory, addHistory, notInHistory, runPropHistory)
import YCHR.Runtime.Reactivation (ReactQueue, drainQueue, enqueue, runReactQueue)
import YCHR.Runtime.Registry
  ( HostCallFn (..),
    HostCallRegistry,
    baseHostCallRegistry,
    unit,
  )
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
import YCHR.Runtime.Types (CallVal (..), SuspensionId (..), Value (..))
import YCHR.Runtime.Var
  ( Unify,
    deref,
    equal,
    getArg,
    makeTerm,
    matchTerm,
    newVar,
    runUnify,
    unify,
  )
import YCHR.VM

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

-- | Map from procedure name to procedure definition.
type ProcMap = Map Name Procedure

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

-- | Non-local control flow signals. We use 'Effectful.Error.Static.Error'
-- as an exception mechanism: 'Return' exits a procedure, 'Continue' and
-- 'Break' target labeled 'Foreach' loops.
data ControlFlow
  = CFReturn Value
  | CFContinue Label
  | CFBreak Label

instance Show ControlFlow where
  show (CFReturn _) = "CFReturn <val>"
  show (CFContinue l) = "CFContinue " ++ T.unpack l.unLabel
  show (CFBreak l) = "CFBreak " ++ T.unpack l.unLabel

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

-- | Interpret a VM program by calling a named procedure with the given
-- value arguments. Entry-point arguments are always values; procedures
-- that require a constraint id at this layer use a different entry
-- point (e.g. @reactivate_dispatch@) called via 'callProc' directly.
interpret :: Program -> HostCallRegistry -> Name -> [Value] -> IO Value
interpret prog hostCalls entryName args = do
  let procMap = Map.fromList [(p.name, p) | p <- prog.procedures]
      argVals = map CVal args
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
-- executes the body, and catches CFReturn. Default return: VBool False.
callProc ::
  (InterpEffects es) =>
  ProcMap -> HostCallRegistry -> Name -> [CallVal] -> Eff es Value
callProc procMap hostCalls name args = do
  case Map.lookup name procMap of
    Nothing -> runtimeError' "callProc: unknown procedure " name.unName
    Just proc -> do
      env <- case bindParams name proc.params args of
        Right e -> pure e
        Left msg -> runtimeErrorS msg
      savedStack <- get @CallStack
      result <-
        evalState env
          . runError @ControlFlow
          $ execStmts procMap hostCalls proc.body
      put @CallStack savedStack
      case result of
        Right () -> pure (VBool False)
        Left (_, CFReturn v) -> pure v
        Left (_, CFContinue l) -> runtimeError' "callProc: uncaught Continue " l.unLabel
        Left (_, CFBreak l) -> runtimeError' "callProc: uncaught Break " l.unLabel

-- | Bind procedure parameters into the appropriate environment slot
-- based on the runtime tag of each argument. Returns 'Left' with a
-- diagnostic message on arity mismatch, which is a compiler-invariant
-- violation: every 'CallExpr' the compiler emits must match the called
-- procedure's parameter list in length.
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
execStmts ::
  (InterpEffects es, State Env :> es, Error ControlFlow :> es) =>
  ProcMap -> HostCallRegistry -> [Stmt] -> Eff es ()
execStmts procMap hostCalls = traverse_ (execStmt procMap hostCalls)

-- | Execute a single statement.
execStmt ::
  (InterpEffects es, State Env :> es, Error ControlFlow :> es) =>
  ProcMap -> HostCallRegistry -> Stmt -> Eff es ()
execStmt pm hc (LetVal name expr) = do
  v <- evalValExpr pm hc expr
  modify (insertVal name v)
execStmt pm hc (LetId name expr) = do
  s <- evalIdExpr pm hc expr
  modify (insertId name s)
execStmt pm hc (AssignVal name expr) = do
  v <- evalValExpr pm hc expr
  modify (insertVal name v)
execStmt pm hc (AssignId name expr) = do
  s <- evalIdExpr pm hc expr
  modify (insertId name s)
execStmt pm hc (If cond thenBranch elseBranch) = do
  c <- evalValExpr pm hc cond
  case c of
    VBool True -> execStmts pm hc thenBranch
    VBool False -> execStmts pm hc elseBranch
    _ -> runtimeErrorS "If: condition is not a boolean"
execStmt pm hc (Foreach lbl cType suspVar conditions body) = do
  snapshot <- getStoreSnapshot cType
  let susps = toList snapshot
  execForeach pm hc lbl suspVar conditions body susps
execStmt _ _ (Continue lbl) = throwError (CFContinue lbl)
execStmt _ _ (Break lbl) = throwError (CFBreak lbl)
execStmt pm hc (Return expr) = do
  v <- evalValExpr pm hc expr
  throwError (CFReturn v)
execStmt pm hc (ExprStmt expr) = do
  _ <- evalValExpr pm hc expr
  pure ()
execStmt pm hc (Store expr) = do
  sid <- evalIdExpr pm hc expr
  storeConstraint sid
execStmt pm hc (Kill expr) = do
  sid <- evalIdExpr pm hc expr
  killConstraint sid
execStmt pm hc (AddHistory ruleId exprs) = do
  sids <- traverse (evalIdExpr pm hc) exprs
  addHistory ruleId sids
execStmt pm hc (DrainReactivationQueue suspVar body) = do
  drainQueue $ \sid -> do
    alive <- aliveConstraint sid
    if alive
      then do
        modify (insertId suspVar sid)
        execStmts pm hc body
      else pure ()
execStmt _ _ (PushFrame frame) = do
  modify @CallStack $ \stack ->
    take maxCallStackDepth (frame : stack)

-- ---------------------------------------------------------------------------
-- Foreach implementation
-- ---------------------------------------------------------------------------

execForeach ::
  (InterpEffects es, State Env :> es, Error ControlFlow :> es) =>
  ProcMap ->
  HostCallRegistry ->
  Label ->
  Name ->
  [(ArgIndex, ValExpr)] ->
  [Stmt] ->
  [Suspension] ->
  Eff es ()
execForeach _ _ _ _ _ _ [] = pure ()
execForeach pm hc lbl suspVar conditions body (susp : rest) = do
  alive <- isSuspAlive susp
  if not alive
    then execForeach pm hc lbl suspVar conditions body rest
    else do
      ok <- checkConditions pm hc susp conditions
      if not ok
        then execForeach pm hc lbl suspVar conditions body rest
        else do
          let Suspension {suspId = sid} = susp
          modify (insertId suspVar sid)
          result <- runError @ControlFlow $ execStmts pm hc body
          case result of
            Right () ->
              execForeach pm hc lbl suspVar conditions body rest
            Left (_, CFContinue l)
              | l == lbl -> execForeach pm hc lbl suspVar conditions body rest
              | otherwise -> throwError (CFContinue l)
            Left (_, CFBreak l)
              | l == lbl -> pure ()
              | otherwise -> throwError (CFBreak l)
            Left (_, cf@(CFReturn _)) -> throwError cf

checkConditions ::
  (InterpEffects es, State Env :> es, Error ControlFlow :> es) =>
  ProcMap -> HostCallRegistry -> Suspension -> [(ArgIndex, ValExpr)] -> Eff es Bool
checkConditions _ _ _ [] = pure True
checkConditions pm hc susp ((ArgIndex i, expr) : rest) = do
  v <- evalValExpr pm hc expr
  let argVal = suspArg susp i
  eq <- equal v argVal
  if eq
    then checkConditions pm hc susp rest
    else pure False

-- ---------------------------------------------------------------------------
-- Value-expression evaluator (normal mode)
-- ---------------------------------------------------------------------------

evalValExpr ::
  (InterpEffects es, State Env :> es, Error ControlFlow :> es) =>
  ProcMap -> HostCallRegistry -> ValExpr -> Eff es Value
evalValExpr _ _ (Var name) = do
  env <- get @Env
  case Map.lookup name env.envValues of
    Just v -> pure v
    Nothing -> runtimeError' "evalValExpr: unbound variable " name.unName
evalValExpr _ _ (Lit (IntLit n)) = pure (VInt n)
evalValExpr _ _ (Lit (FloatLit n)) = pure (VFloat n)
evalValExpr _ _ (Lit (AtomLit s)) = pure (VAtom s)
evalValExpr _ _ (Lit (TextLit s)) = pure (VText s)
evalValExpr _ _ (Lit (BoolLit b)) = pure (VBool b)
evalValExpr _ _ (Lit WildcardLit) = pure VWildcard
evalValExpr pm hc (CallExpr name args) = do
  argVals <- traverse (evalCallArg pm hc) args
  callProc pm hc name argVals
evalValExpr pm hc (HostCall name args) = do
  argVals <- traverse (evalValExpr pm hc) args
  derefedVals <- traverse deref argVals
  invokeHostCall hc name derefedVals
evalValExpr pm hc (Not expr) = do
  v <- evalValExpr pm hc expr
  case v of
    VBool b -> pure (VBool (not b))
    _ -> runtimeErrorS "Not: expected boolean"
evalValExpr pm hc (And e1 e2) = do
  v1 <- evalValExpr pm hc e1
  case v1 of
    VBool False -> pure (VBool False)
    VBool True -> evalValExpr pm hc e2
    _ -> runtimeErrorS "And: expected boolean"
evalValExpr pm hc (Or e1 e2) = do
  v1 <- evalValExpr pm hc e1
  case v1 of
    VBool True -> pure (VBool True)
    VBool False -> evalValExpr pm hc e2
    _ -> runtimeErrorS "Or: expected boolean"
evalValExpr _ _ NewVar = newVar
evalValExpr pm hc (MakeTerm functor args) = do
  argVals <- traverse (evalValExpr pm hc) args
  pure $ makeTerm functor.unName argVals
evalValExpr pm hc (MatchTerm expr functor arity) = do
  v <- evalValExpr pm hc expr
  VBool <$> matchTerm v functor.unName arity
evalValExpr pm hc (GetArg expr idx) = do
  v <- evalValExpr pm hc expr
  getArg v idx
evalValExpr pm hc (Alive expr) = do
  sid <- evalIdExpr pm hc expr
  VBool <$> aliveConstraint sid
evalValExpr pm hc (IdEqual e1 e2) = do
  s1 <- evalIdExpr pm hc e1
  s2 <- evalIdExpr pm hc e2
  pure (VBool (idEqual s1 s2))
evalValExpr pm hc (IsConstraintType expr cType) = do
  sid <- evalIdExpr pm hc expr
  VBool <$> isConstraintType sid cType
evalValExpr pm hc (NotInHistory ruleId args) = do
  sids <- traverse (evalIdExpr pm hc) args
  VBool <$> notInHistory ruleId sids
evalValExpr pm hc (Unify e1 e2) = do
  v1 <- evalValExpr pm hc e1
  v2 <- evalValExpr pm hc e2
  (ok, observers) <- listen (unify v1 v2)
  enqueue observers
  if ok
    then pure (VBool True)
    else do
      t1 <- valueToTerm "_" v1
      t2 <- valueToTerm "_" v2
      runtimeErrorS $
        "unification failure: cannot unify "
          ++ prettyTerm t1
          ++ " with "
          ++ prettyTerm t2
evalValExpr pm hc (Equal e1 e2) = do
  v1 <- evalValExpr pm hc e1
  v2 <- evalValExpr pm hc e2
  VBool <$> equal v1 v2
evalValExpr pm hc (FieldArg expr (ArgIndex i)) = do
  sid <- evalIdExpr pm hc expr
  getConstraintArg sid i
evalValExpr pm hc (FieldType expr) = do
  sid <- evalIdExpr pm hc expr
  (\ct -> VInt ct.unConstraintType) <$> getConstraintType sid
evalValExpr pm hc (EvalDeep expr) = evalValExprDeep pm hc expr

-- ---------------------------------------------------------------------------
-- Id-expression evaluator
-- ---------------------------------------------------------------------------

evalIdExpr ::
  (InterpEffects es, State Env :> es, Error ControlFlow :> es) =>
  ProcMap -> HostCallRegistry -> IdExpr -> Eff es SuspensionId
evalIdExpr _ _ (IdVar name) = do
  env <- get @Env
  case Map.lookup name env.envIds of
    Just s -> pure s
    Nothing -> runtimeError' "evalIdExpr: unbound id variable " name.unName
evalIdExpr pm hc (CreateConstraint cType args) = do
  argVals <- traverse (evalValExpr pm hc) args
  createConstraint cType argVals

-- ---------------------------------------------------------------------------
-- Call-arg evaluator
-- ---------------------------------------------------------------------------

evalCallArg ::
  (InterpEffects es, State Env :> es, Error ControlFlow :> es) =>
  ProcMap -> HostCallRegistry -> CallArg -> Eff es CallVal
evalCallArg pm hc (AVal e) = CVal <$> evalValExpr pm hc e
evalCallArg pm hc (AId e) = CId <$> evalIdExpr pm hc e

-- ---------------------------------------------------------------------------
-- Host call dispatch
-- ---------------------------------------------------------------------------

invokeHostCall ::
  (InterpEffects es) =>
  HostCallRegistry -> Name -> [Value] -> Eff es Value
invokeHostCall hc name argVals =
  case Map.lookup name hc of
    Just (HostCallFn f) -> do
      result <- Eff.try @SomeException (f argVals)
      case result of
        Right v -> pure v
        Left exc ->
          runtimeErrorS $
            "host call " ++ T.unpack name.unName ++ ": " ++ displayException exc
    Nothing -> runtimeError' "evalValExpr: unknown host call " name.unName

-- ---------------------------------------------------------------------------
-- Value-expression evaluator (deep deref mode)
-- ---------------------------------------------------------------------------

-- | Evaluate a value expression with automatic dereferencing: variable
-- references follow binding chains before use, and this mode propagates
-- into sub-expressions. Used to implement 'EvalDeep' (guards and @is@ RHS).
evalValExprDeep ::
  (InterpEffects es, State Env :> es, Error ControlFlow :> es) =>
  ProcMap -> HostCallRegistry -> ValExpr -> Eff es Value
evalValExprDeep pm hc (Var name) = do
  v <- evalValExpr pm hc (Var name)
  deref v
evalValExprDeep pm hc (HostCall name args) = do
  argVals <- traverse (evalValExprDeep pm hc) args
  invokeHostCall hc name argVals
evalValExprDeep pm hc (CallExpr name args) = do
  argVals <- traverse (evalCallArgDeep pm hc) args
  callProc pm hc name argVals
evalValExprDeep pm hc (MakeTerm functor args) = do
  argVals <- traverse (evalValExprDeep pm hc) args
  pure $ makeTerm functor.unName argVals
evalValExprDeep pm hc expr = evalValExpr pm hc expr

evalCallArgDeep ::
  (InterpEffects es, State Env :> es, Error ControlFlow :> es) =>
  ProcMap -> HostCallRegistry -> CallArg -> Eff es CallVal
evalCallArgDeep pm hc (AVal e) = CVal <$> evalValExprDeep pm hc e
evalCallArgDeep pm hc (AId e) = CId <$> evalIdExpr pm hc e
