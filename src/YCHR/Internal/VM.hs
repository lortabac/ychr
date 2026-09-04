-- | CHR Virtual Machine — re-exports from "YCHR.Internal.VM.Types".
module YCHR.Internal.VM
  ( -- * Program structure
    Program (..),
    Procedure (..),
    ProcKind (..),
    EvaluableKey (..),

    -- * Statements
    Stmt (..),

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
