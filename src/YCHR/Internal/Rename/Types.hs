{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Internal.Rename.Types
-- Description : Environment types shared by the renamer.
--
-- The renamer (see "YCHR.Internal.Rename") consults two kinds of global environments
-- when resolving a surface name to a fully-qualified one:
--
-- * 'DeclEnv' — where each @(name, arity)@ is /declared/. Used to resolve
--   references to the module a rule belongs to (\"what does this module
--   itself provide?\") and to validate already-qualified references.
-- * 'ExportEnv' — where each @(name, arity)@ is /exported/. Used to resolve
--   references to imported modules (\"what do the modules I import give
--   me?\").
--
-- Both wrap a @Map (name, arity) [module]@ because a single identifier can
-- resolve to several modules (which triggers an ambiguity error). They are
-- kept as distinct newtypes so that callers can't accidentally use a
-- declaration map in place of an export map.
module YCHR.Internal.Rename.Types
  ( -- * Export environment
    ExportEnv,
    makeExportEnv,
    lookupExport,
    toListExport,

    -- * Declaration environment
    DeclEnv,
    makeDeclEnv,
    lookupDecl,
    toListDecl,

    -- * Reserved names
    isReserved,
  )
where

import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)

-- | All names exported by each module, indexed by @(name, arity)@. For a
-- module without an explicit @module@ directive, every declaration is
-- considered exported.
newtype ExportEnv = ExportEnv (Map.Map (Text, Int) [Text])

-- | Build an export environment from @((name, arity), providers)@ pairs;
-- several modules under one key accumulate into one entry.
makeExportEnv :: [((Text, Int), [Text])] -> ExportEnv
makeExportEnv = ExportEnv . Map.fromListWith (++)

-- | The modules exporting @(name, arity)@; @[]@ when none do.
lookupExport :: (Text, Int) -> ExportEnv -> [Text]
lookupExport k (ExportEnv m) = Map.findWithDefault [] k m

-- | Every @(name, arity)@ entry with its providers, in ascending key order.
toListExport :: ExportEnv -> [((Text, Int), [Text])]
toListExport (ExportEnv m) = Map.toList m

-- | All names declared anywhere in the program, indexed by @(name, arity)@.
-- Unlike 'ExportEnv', this ignores export lists: it answers \"is this name
-- visible within its own declaring module?\".
newtype DeclEnv = DeclEnv (Map.Map (Text, Int) [Text])

-- | Build a declaration environment from @((name, arity), declaringModules)@
-- pairs; several declarations under one key accumulate into one entry.
makeDeclEnv :: [((Text, Int), [Text])] -> DeclEnv
makeDeclEnv = DeclEnv . Map.fromListWith (++)

-- | The modules declaring @(name, arity)@; @[]@ when none do.
lookupDecl :: (Text, Int) -> DeclEnv -> [Text]
lookupDecl k (DeclEnv m) = Map.findWithDefault [] k m

-- | Every @(name, arity)@ entry with its declaring modules, in ascending
-- key order.
toListDecl :: DeclEnv -> [((Text, Int), [Text])]
toListDecl (DeclEnv m) = Map.toList m

-- | Names that must stay 'YCHR.Types.Unqualified' even in resolving
-- contexts. These are desugaring-level keywords (@true@, @=@, @is@,
-- @->@, @;@, @$call@, @quote@, @fun@) that the desugarer matches by
-- name; qualifying them would break that dispatch. @;@ is also here for
-- the runtime: the search driver recognizes a disjunctive goal by the
-- bare functor (\"YCHR.Internal.Runtime.Goal\").
--
-- Most of these forms are handled by dedicated shape-matching cases in
-- 'YCHR.Internal.Rename.renameTerm'. This set is the fallback for shapes that don't
-- match those cases (e.g. @is/3@).
reservedSymbolSet :: Set Text
reservedSymbolSet = Set.fromList ["true", "=", "is", "->", ";", "$call", "quote", "fun"]

-- | Whether @t@ is one of the names in 'reservedSymbolSet'.
isReserved :: Text -> Bool
isReserved t = Set.member t reservedSymbolSet
