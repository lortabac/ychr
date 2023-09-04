module YCHR.Types.VariableMap
  ( VariableMap,
    lookupVariableId,
    assignVariableIds,
  )
where

import Data.List (nub)
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import YCHR.Types.Parsed
import YCHR.Types.Prepared

newtype VariableMap = VariableMap {getVariableMap :: Map Variable VariableId}
  deriving (Eq, Show)

lookupVariableId :: Variable -> VariableMap -> Maybe VariableId
lookupVariableId constr (VariableMap m) = Map.lookup constr m

assignVariableIds :: [Variable] -> VariableMap
assignVariableIds = VariableMap . Map.fromList . flip zip [VariableId 0 ..] . nub
