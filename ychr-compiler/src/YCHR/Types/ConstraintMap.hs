module YCHR.Types.ConstraintMap
  ( ConstraintMap,
    lookupConstraintId,
    assignConstraintIds,
  )
where

import Data.List (nub)
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import YCHR.Types.Normalized
import YCHR.Types.Prepared

newtype ConstraintMap = ConstraintMap {getConstraintMap :: Map NmChrConstraint ConstraintId}
  deriving (Eq, Show)

lookupConstraintId :: NmChrConstraint -> ConstraintMap -> Maybe ConstraintId
lookupConstraintId constr (ConstraintMap m) = Map.lookup constr m

assignConstraintIds :: [NmChrConstraint] -> ConstraintMap
assignConstraintIds = ConstraintMap . Map.fromList . flip zip [ConstraintId 0 ..] . nub
