module YCHR.Types.Normalized where

import YCHR.Types.Common
import YCHR.Types.Parsed
import YCHR.Types.Renamed

type NmHead = Head Variable QualifiedName

type NmRemove = Remove Variable QualifiedName

type NmGuard = Guard Variable QualifiedName

type NmBody = Body Variable QualifiedName

type NmChrConstraint = ChrConstraint Variable QualifiedName

-- | Normalized constraint
type NmConstraint = Constraint Variable QualifiedName

data NormalRule = NormalRule
  { head :: NmHead,
    remove :: NmRemove,
    guard :: NmGuard,
    body :: NmBody
  }
  deriving (Eq, Show)
