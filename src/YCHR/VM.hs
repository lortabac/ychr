-- | CHR Virtual Machine — re-exports from "YCHR.VM.Types".
module YCHR.VM
  ( -- * Program structure
    Program (..),
    Procedure (..),
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
    Literal (..),
    ArgIndex (..),
    Name (..),
    Label (..),
  )
where

import YCHR.VM.Types
