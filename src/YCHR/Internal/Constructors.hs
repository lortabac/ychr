{-# LANGUAGE OverloadedStrings #-}

-- | Data-constructor lookup.
--
-- A map built from a program's @:- chr_type@ declarations, answering
-- which declared constructor a use-site name refers to ('lookupCon').
-- The renamer already qualifies every constructor use it can resolve,
-- so a name that is still bare here is unknown or ambiguous. Used by
-- "YCHR.Internal.Exhaustiveness".
module YCHR.Internal.Constructors
  ( ConEnv (..),
    buildConEnv,
    buildConMap,
    lookupCon,
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import YCHR.Internal.Types
  ( DataConstructor (..),
    Name (..),
    TypeDefinition (..),
    typeConstructors,
  )

-- | Constructor-resolution maps derived from a program's type
-- definitions.
data ConEnv = ConEnv
  { -- | Map from constructor name to the declared constructor.
    constructors :: Map Name DataConstructor
  }

-- | Build a 'ConEnv' from a program's type definitions.
buildConEnv :: [TypeDefinition] -> ConEnv
buildConEnv tds =
  ConEnv
    { constructors = buildConMap tds
    }

-- | Build the constructor-name index consulted by 'lookupCon'.
buildConMap :: [TypeDefinition] -> Map Name DataConstructor
buildConMap tds =
  Map.fromList
    [ (dc.conName, dc)
    | td <- tds,
      dc <- typeConstructors td
    ]

-- | Look up a constructor name in 'constructors'.
lookupCon :: ConEnv -> Name -> Maybe DataConstructor
lookupCon env name = Map.lookup name env.constructors
