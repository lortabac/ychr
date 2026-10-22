-- | CHR Virtual Machine — re-exports from "YCHR.Internal.VM.Types".
module YCHR.Internal.VM
  ( -- * Program structure
    Program (..),
    Procedure (..),
    ProcKind (..),
    Evaluable (..),
    EvaluableKey (..),
    Callable (..),
    CallableKey (..),
    Tellable (..),
    TellableKey (..),
    TellableResolution (..),
    funRefFunctor,
    lambdaClosureFunctor,

    -- * Statements
    Stmt (..),
    IndexCondition (..),

    -- * Expressions
    ValExpr (..),
    IdExpr (..),
    BoolExpr (..),
    CallArg (..),

    -- * Runtime call stack frames
    StackFrame (..),

    -- * Supporting types
    ConstraintType (..),
    RuleId (..),
    HistoryIds,
    mkHistoryIds,
    historyIdsList,
    historyIdsFromSerialized,
    Literal (..),
    ArgIndex (..),
    Name (..),
    Label (..),
  )
where

import YCHR.Internal.VM.Types
