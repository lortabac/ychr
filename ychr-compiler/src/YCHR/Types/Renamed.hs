module YCHR.Types.Renamed where

import Data.Text (Text)
import YCHR.Types.Common
import YCHR.Types.Parsed

-- | Renamed module
type RnModule = Module Variable QualifiedName

-- | Renamed rule
type RnRule = Rule Variable QualifiedName

-- | Renamed head
type RnHead = Head Variable QualifiedName

-- | Renamed removed constraints
-- (the constraints that appear after the \ in a simpagation rule)
type RnRemove = Remove Variable QualifiedName

-- | Renamed guard
type RnGuard = Guard Variable QualifiedName

-- | Renamed rule body
type RnBody = Body Variable QualifiedName

-- | Renamed CHR constraint
type RnChrConstraint = ChrConstraint Variable QualifiedName

-- | Renamed constraint
type RnConstraint = Constraint Variable QualifiedName

-- | Qualified name (module name and identifier)
data QualifiedName = QualifiedName Text Text
  deriving (Eq, Show, Ord)
