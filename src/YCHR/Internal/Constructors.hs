{-# LANGUAGE OverloadedStrings #-}

-- | Data-constructor resolution.
--
-- Maps built from a program's @:- chr_type@ declarations. They answer
-- two questions about a use-site constructor name: which declared type
-- and constructor it refers to ('lookupCon'), and what its canonical
-- qualified form is ('canonicalizeCon'). Used by
-- "YCHR.Internal.Exhaustiveness".
--
-- The subtle part is 'buildConAlias': an unqualified name is resolved
-- to its declaration only when exactly one declared constructor uses
-- it. Ambiguous names (declared in more than one module) are dropped,
-- so callers treat the use site as unknown rather than guess.
module YCHR.Internal.Constructors
  ( ConEnv (..),
    buildConEnv,
    buildConMap,
    buildConAlias,
    canonicalizeCon,
    lookupCon,
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import YCHR.Internal.Types
  ( DataConstructor (..),
    Name (..),
    TypeDefinition (..),
    typeConstructors,
    unqualifiedText,
  )

-- | Constructor-resolution maps derived from a program's type
-- definitions.
data ConEnv = ConEnv
  { -- | Map from constructor name to its parent type definition and
    -- constructor info.
    constructors :: Map Name (TypeDefinition, DataConstructor),
    -- | Resolves a use-site unqualified name to its declaration's
    -- qualified name when exactly one constructor matches. See
    -- 'buildConAlias'.
    aliases :: Map Text Name
  }

-- | Build a 'ConEnv' from a program's type definitions.
buildConEnv :: [TypeDefinition] -> ConEnv
buildConEnv tds =
  ConEnv
    { constructors = buildConMap tds,
      aliases = buildConAlias tds
    }

-- | Build the constructor-name index consulted by 'lookupCon'.
buildConMap :: [TypeDefinition] -> Map Name (TypeDefinition, DataConstructor)
buildConMap tds =
  Map.fromList
    [ (dc.conName, (td, dc))
    | td <- tds,
      dc <- typeConstructors td
    ]

-- | Build the use-site → declaration alias map, keyed by unqualified name.
-- A name is included only when exactly one declared constructor uses it;
-- ambiguous names (same unqualified name declared in more than one module)
-- are dropped so 'canonicalizeCon' falls through and the caller treats the
-- use site as unknown rather than guessing.
buildConAlias :: [TypeDefinition] -> Map Text Name
buildConAlias tds =
  Map.mapMaybe single $
    Map.fromListWith
      (++)
      [ (unqualifiedText dc.conName, [dc.conName])
      | td <- tds,
        dc <- typeConstructors td
      ]
  where
    single [n] = Just n
    single _ = Nothing

-- | Map a use-site constructor name to its declared, qualified form when a
-- unique match exists. 'Qualified' names pass through unchanged;
-- 'Unqualified' names are resolved through 'aliases'. When no unique
-- match exists the name is returned as-is.
canonicalizeCon :: ConEnv -> Name -> Name
canonicalizeCon _ name@(Qualified _ _) = name
canonicalizeCon env (Unqualified n) =
  Map.findWithDefault (Unqualified n) n env.aliases

-- | Look up a (possibly already canonical) constructor name in
-- 'constructors'. Returns the parent type definition and the constructor.
lookupCon :: ConEnv -> Name -> Maybe (TypeDefinition, DataConstructor)
lookupCon env name = Map.lookup name env.constructors
