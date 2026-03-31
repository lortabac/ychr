{-# LANGUAGE OverloadedStrings #-}

module YCHR.Rename.Types
  ( ExportEnv,
    makeExportEnv,
    lookupExport,
    toListExport,
    DeclEnv,
    makeDeclEnv,
    lookupDecl,
    ReservedSymbols,
    isReserved,
    reservedSymbols,
  )
where

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)

newtype ExportEnv = ExportEnv (Map.Map (Text, Int) [Text])

makeExportEnv :: [((Text, Int), [Text])] -> ExportEnv
makeExportEnv = ExportEnv . Map.fromListWith (++)

lookupExport :: (Text, Int) -> ExportEnv -> [Text]
lookupExport k (ExportEnv m) = Map.findWithDefault [] k m

toListExport :: ExportEnv -> [((Text, Int), [Text])]
toListExport (ExportEnv m) = Map.toList m

newtype DeclEnv = DeclEnv (Map.Map (Text, Int) [Text])

makeDeclEnv :: [((Text, Int), [Text])] -> DeclEnv
makeDeclEnv = DeclEnv . Map.fromListWith (++)

lookupDecl :: (Text, Int) -> DeclEnv -> [Text]
lookupDecl k (DeclEnv m) = Map.findWithDefault [] k m

newtype ReservedSymbols = ReservedSymbols (Set.Set Text)

isReserved :: Text -> ReservedSymbols -> Bool
isReserved t (ReservedSymbols s) = Set.member t s

reservedSymbols :: ReservedSymbols
reservedSymbols = ReservedSymbols $ Set.fromList ["true", "=", "is"]
