{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module YCHR.Types.Parsed where

import Data.Data (Data)
import Data.String (IsString)
import Data.Text (Text)
import YCHR.Types.Common

-- | Parsed module
type PsModule = Module Variable PsName

-- | Textual variable
newtype Variable = Variable {getVariable :: Text}
  deriving stock (Eq, Show, Ord, Data)
  deriving newtype (IsString)

-- | Parsed term
type PsTerm = Term Variable

-- | Parsed name
data PsName
  = PsName Text
  | PsQualifiedName Text Text
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
