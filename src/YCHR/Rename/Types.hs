{-# LANGUAGE OverloadedStrings #-}

module YCHR.Rename.Types
  ( GlobalEnv,
    makeGlobalEnv,
    lookupGlobal,
    toListGlobal,
    LocalEnv,
    makeLocalEnv,
    lookupLocal,
    ReservedSymbols,
    isReserved,
    reservedSymbols,
  )
where

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)

newtype GlobalEnv = GlobalEnv (Map.Map (Text, Int) [Text])

makeGlobalEnv :: [((Text, Int), [Text])] -> GlobalEnv
makeGlobalEnv = GlobalEnv . Map.fromListWith (++)

lookupGlobal :: (Text, Int) -> GlobalEnv -> [Text]
lookupGlobal k (GlobalEnv m) = Map.findWithDefault [] k m

toListGlobal :: GlobalEnv -> [((Text, Int), [Text])]
toListGlobal (GlobalEnv m) = Map.toList m

newtype LocalEnv = LocalEnv (Map.Map (Text, Int) [Text])

makeLocalEnv :: [((Text, Int), [Text])] -> LocalEnv
makeLocalEnv = LocalEnv . Map.fromListWith (++)

lookupLocal :: (Text, Int) -> LocalEnv -> [Text]
lookupLocal k (LocalEnv m) = Map.findWithDefault [] k m

newtype ReservedSymbols = ReservedSymbols (Set.Set Text)

isReserved :: Text -> ReservedSymbols -> Bool
isReserved t (ReservedSymbols s) = Set.member t s

reservedSymbols :: ReservedSymbols
reservedSymbols = ReservedSymbols $ Set.fromList ["true", "=", "is"]
