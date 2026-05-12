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

import Control.Exception (SomeException, displayException, fromException)
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
import YCHR.Runtime.Error (CallStack, RuntimeErrorThrown, runtimeError', runtimeErrorS)
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
  b <- evalBoolExpr pm hc cond
  if b then execStmts pm hc thenBranch else execStmts pm hc elseBranch
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
execStmt pm hc (BoolExprStmt expr) = do
  _ <- evalBoolExpr pm hc expr
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
evalValExpr _ _ NewVar = newVar
evalValExpr pm hc (MakeTerm functor args) = do
  argVals <- traverse (evalValExpr pm hc) args
  pure $ makeTerm functor.unName argVals
evalValExpr pm hc (GetArg expr idx) = do
  v <- evalValExpr pm hc expr
  getArg v idx
evalValExpr pm hc (FieldArg expr (ArgIndex i)) = do
  sid <- evalIdExpr pm hc expr
  getConstraintArg sid i
evalValExpr pm hc (FieldType expr) = do
  sid <- evalIdExpr pm hc expr
  (\ct -> VInt ct.unConstraintType) <$> getConstraintType sid
evalValExpr pm hc (EvalDeep expr) = evalValExprDeep pm hc expr

-- ---------------------------------------------------------------------------
-- Bool-expression evaluator (normal mode)
-- ---------------------------------------------------------------------------

evalBoolExpr ::
  (InterpEffects es, State Env :> es, Error ControlFlow :> es) =>
  ProcMap -> HostCallRegistry -> BoolExpr -> Eff es Bool
evalBoolExpr _ _ (BLit b) = pure b
evalBoolExpr pm hc (BNot e) = not <$> evalBoolExpr pm hc e
evalBoolExpr pm hc (BAnd e1 e2) = do
  b1 <- evalBoolExpr pm hc e1
  if b1 then evalBoolExpr pm hc e2 else pure False
evalBoolExpr pm hc (BOr e1 e2) = do
  b1 <- evalBoolExpr pm hc e1
  if b1 then pure True else evalBoolExpr pm hc e2
evalBoolExpr pm hc (BMatchTerm expr functor arity) = do
  v <- evalValExpr pm hc expr
  matchTerm v functor.unName arity
evalBoolExpr pm hc (BEqual e1 e2) = do
  v1 <- evalValExpr pm hc e1
  v2 <- evalValExpr pm hc e2
  equal v1 v2
evalBoolExpr pm hc (BIdEqual e1 e2) = do
  s1 <- evalIdExpr pm hc e1
  s2 <- evalIdExpr pm hc e2
  pure (idEqual s1 s2)
evalBoolExpr pm hc (BAlive expr) = do
  sid <- evalIdExpr pm hc expr
  aliveConstraint sid
evalBoolExpr pm hc (BIsConstraintType expr cType) = do
  sid <- evalIdExpr pm hc expr
  isConstraintType sid cType
evalBoolExpr pm hc (BNotInHistory ruleId args) = do
  sids <- traverse (evalIdExpr pm hc) args
  notInHistory ruleId sids
evalBoolExpr pm hc (BUnify e1 e2) = do
  v1 <- evalValExpr pm hc e1
  v2 <- evalValExpr pm hc e2
  (ok, observers) <- listen (unify v1 v2)
  enqueue observers
  if ok
    then pure True
    else do
      t1 <- valueToTerm Map.empty v1
      t2 <- valueToTerm Map.empty v2
      runtimeErrorS $
        "unification failure: cannot unify "
          ++ prettyTerm t1
          ++ " with "
          ++ prettyTerm t2
evalBoolExpr pm hc (BFromVal expr) = do
  v <- evalValExpr pm hc expr
  case v of
    VBool b -> pure b
    _ -> runtimeErrorS "BFromVal: expected boolean"
evalBoolExpr pm hc (BEvalDeep expr) = evalBoolExprDeep pm hc expr

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
        Left exc -> case fromException exc :: Maybe RuntimeErrorThrown of
          -- A 'RuntimeErrorThrown' from a nested host call already carries
          -- a fully-formatted message and the call stack at its throw site;
          -- re-throwing it preserves both. Wrapping with 'runtimeErrorS'
          -- would 'show'-encode the inner exception into the outer message
          -- and discard the inner stack.
          Just rte -> Eff.throwIO rte
          Nothing ->
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

-- ---------------------------------------------------------------------------
-- Bool-expression evaluator (deep deref mode)
-- ---------------------------------------------------------------------------

-- | Deep-deref evaluation for 'BoolExpr'. Mirrors 'evalValExprDeep':
-- propagates deep mode into 'ValExpr' and 'IdExpr' payloads, while
-- recursing through the boolean structure of 'BNot'/'BAnd'/'BOr' and
-- 'BEvalDeep' itself.
evalBoolExprDeep ::
  (InterpEffects es, State Env :> es, Error ControlFlow :> es) =>
  ProcMap -> HostCallRegistry -> BoolExpr -> Eff es Bool
evalBoolExprDeep pm hc (BNot e) = not <$> evalBoolExprDeep pm hc e
evalBoolExprDeep pm hc (BAnd e1 e2) = do
  b1 <- evalBoolExprDeep pm hc e1
  if b1 then evalBoolExprDeep pm hc e2 else pure False
evalBoolExprDeep pm hc (BOr e1 e2) = do
  b1 <- evalBoolExprDeep pm hc e1
  if b1 then pure True else evalBoolExprDeep pm hc e2
evalBoolExprDeep pm hc (BMatchTerm expr functor arity) = do
  v <- evalValExprDeep pm hc expr
  matchTerm v functor.unName arity
evalBoolExprDeep pm hc (BEqual e1 e2) = do
  v1 <- evalValExprDeep pm hc e1
  v2 <- evalValExprDeep pm hc e2
  equal v1 v2
evalBoolExprDeep pm hc (BUnify e1 e2) = do
  v1 <- evalValExprDeep pm hc e1
  v2 <- evalValExprDeep pm hc e2
  (ok, observers) <- listen (unify v1 v2)
  enqueue observers
  if ok
    then pure True
    else do
      t1 <- valueToTerm Map.empty v1
      t2 <- valueToTerm Map.empty v2
      runtimeErrorS $
        "unification failure: cannot unify "
          ++ prettyTerm t1
          ++ " with "
          ++ prettyTerm t2
evalBoolExprDeep pm hc (BFromVal expr) = do
  v <- evalValExprDeep pm hc expr
  case v of
    VBool b -> pure b
    _ -> runtimeErrorS "BFromVal: expected boolean"
evalBoolExprDeep pm hc (BEvalDeep expr) = evalBoolExprDeep pm hc expr
evalBoolExprDeep pm hc expr = evalBoolExpr pm hc expr
