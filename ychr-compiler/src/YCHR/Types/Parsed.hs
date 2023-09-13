{-# LANGUAGE DeriveDataTypeable #-}

module YCHR.Types.Parsed where

import Data.Data (Data)
import Data.Text (Text)
import YCHR.Types.Common

-- | Parsed module
type PsModule = Module Variable PsName

-- | Parsed term
type PsTerm = Term Variable

-- | Parsed name
data PsName
  = PsName Text
  | PsQualifiedName QualifiedName
  deriving (Eq, Show, Data)

-- | Parsed rule
type PsRule = Rule Variable PsName

-- | Parsed head
type PsHead = Head Variable PsName

-- | Parsed removed constraints
-- (the constraints that appear after the \ in a simpagation rule)
type PsRemove = Remove Variable PsName

-- | Parsed guard
type PsGuard = Guard Variable PsName

-- | Parsed rule body
type PsBody = Body Variable PsName

-- | Parsed CHR constraint
type PsChrConstraint = ChrConstraint Variable PsName

-- | Parsed host constraint
type PsHostConstraint = HostConstraint Variable

-- | Parsed constraint
type PsConstraint = Constraint Variable PsName
