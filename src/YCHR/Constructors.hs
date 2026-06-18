{-# LANGUAGE OverloadedStrings #-}

-- | Shared data-constructor resolution.
--
-- Maps from a program's @:- chr_type@ declarations that let any phase
-- (the type checker, the exhaustiveness checker) answer two questions
-- about a use-site constructor name: which declared type and
-- constructor does it refer to ('lookupCon'), and what is its canonical
-- qualified form ('canonicalizeCon').
--
-- The subtle part is 'buildConAlias': an unqualified name is resolved
-- to its declaration only when exactly one declared constructor uses
-- it. Ambiguous names (declared in more than one module) are dropped so
-- callers fall through and treat the use site as unknown rather than
-- guessing. Keeping this logic in one place stops the type checker and
-- the exhaustiveness checker from diverging on that rule.
module YCHR.Constructors
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
import YCHR.Types
  ( DataConstructor (..),
    Name (..),
    TypeDefinition (..),
    typeConstructors,
  )

-- | Constructor-resolution maps derived from a program's type
-- definitions.
data ConEnv = ConEnv
  { -- | Map from constructor name to its parent type definition and
    -- constructor info.
    conMap :: Map Name (TypeDefinition, DataConstructor),
    -- | Resolves a use-site unqualified name to its declaration's
    -- qualified name when exactly one constructor matches. See
    -- 'buildConAlias'.
    conAlias :: Map Text Name
  }

-- | Build a 'ConEnv' from a program's type definitions.
buildConEnv :: [TypeDefinition] -> ConEnv
buildConEnv tds =
  ConEnv
    { conMap = buildConMap tds,
      conAlias = buildConAlias tds
    }

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
    unqualifiedText (Unqualified t) = t
    unqualifiedText (Qualified _ t) = t

-- | Map a use-site constructor name to its declared, qualified form when a
-- unique match exists. 'Qualified' names pass through unchanged;
-- 'Unqualified' names are resolved through 'conAlias'. When no unique
-- match exists the name is returned as-is.
canonicalizeCon :: ConEnv -> Name -> Name
canonicalizeCon _ name@(Qualified _ _) = name
canonicalizeCon env (Unqualified n) =
  Map.findWithDefault (Unqualified n) n env.conAlias

-- | Look up a (possibly already canonical) constructor name in the
-- 'conMap'. Returns the parent type definition and the constructor.
lookupCon :: ConEnv -> Name -> Maybe (TypeDefinition, DataConstructor)
lookupCon env name = Map.lookup name env.conMap
