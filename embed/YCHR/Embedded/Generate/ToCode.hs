{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

-- | Turning values into 'Code'.
--
-- 'ToCode' is the emitter's one class. Every type the generated
-- resources contain has an instance: the product\/sum plumbing comes
-- from 'GHC.Generics' ("YCHR.Embedded.Generate.Instances" derives it per
-- type), and the leaves — scalars, text, the container types — are
-- written out here so that each one renders as the constructor
-- application MicroHs should read rather than as an internal
-- representation.
--
-- Generic programming is otherwise avoided in this codebase
-- (@dev-docs\/STYLE.md@, "Mind compilation times"); it is used here
-- because this module is not part of the shipped library — only the
-- generator and the test suite compile it — and because the alternative
-- is a hand-written instance per constructor of the AST, which would
-- silently drop a constructor added to a type instead of failing the
-- build.
module YCHR.Embedded.Generate.ToCode
  ( -- * The class
    ToCode (..),
    genericToCode,

    -- * Generic plumbing
    GToCode,
    GSum,
    GFields,
  )
where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Generics
import YCHR.Embedded.Generate.Code

-- | Types whose values the emitter can render as Haskell source.
class ToCode a where
  toCode :: a -> Code

-- | 'toCode' for any type with a 'Generic' instance. The instances in
-- "YCHR.Embedded.Generate.Instances" are all written as
-- @instance ToCode T where toCode = genericToCode@.
genericToCode :: (Generic a, GToCode (Rep a)) => a -> Code
genericToCode = gToCode . from

-- ---------------------------------------------------------------------------
-- Generic plumbing
-- ---------------------------------------------------------------------------

-- | A datatype in the generic representation: supplies its defining
-- module so that each constructor can be qualified with that module's
-- import alias.
class GToCode f where
  gToCode :: f p -> Code

-- | A sum of constructors, given the defining module name.
class GSum f where
  gSum :: String -> f p -> Code

-- | The fields of one constructor, in declaration order.
class GFields f where
  gFields :: f p -> [Code]

instance (Datatype d, GSum f) => GToCode (M1 D d f) where
  gToCode x = gSum (moduleName x) (unM1 x)

instance (GSum f, GSum g) => GSum (f :+: g) where
  gSum m (L1 x) = gSum m x
  gSum m (R1 x) = gSum m x

instance (Constructor c, GFields f) => GSum (M1 C c f) where
  gSum m x = CApp (CName (qualify m (conName x))) (gFields (unM1 x))

-- | A datatype with no constructors has no values to render; the arm
-- exists so that the ''M1' 'D' instance is total for every 'Rep'.
instance GSum V1 where
  gSum _ _ = error "ychr-codegen: cannot render a value of an empty datatype"

instance GFields U1 where
  gFields _ = []

instance (GFields f, GFields g) => GFields (f :*: g) where
  gFields (x :*: y) = gFields x ++ gFields y

instance (ToCode a) => GFields (K1 i a) where
  gFields (K1 x) = [toCode x]

instance (GFields f) => GFields (M1 S s f) where
  gFields = gFields . unM1

-- | Qualify a constructor name with its defining module's import alias.
qualify :: String -> String -> String
qualify m c = case aliasForModule m of
  Just alias -> alias ++ "." ++ c
  Nothing ->
    error
      ( "ychr-codegen: no import alias for the module "
          ++ show m
          ++ " defining "
          ++ show c
          ++ "; add it to YCHR.Embedded.Generate.Code.aliasTable"
      )

-- ---------------------------------------------------------------------------
-- Leaves
-- ---------------------------------------------------------------------------

instance ToCode Int where
  toCode = CInt . toInteger

instance ToCode Integer where
  toCode = CInt

instance ToCode Bool where
  toCode b = CName (if b then "True" else "False")

instance ToCode Double where
  toCode = CDouble

instance ToCode Char where
  toCode = CChar

-- | @String@ is emitted as one string literal rather than as a list of
-- 'Char' literals: 'YCHR.Internal.Loc.SourceLoc' carries a file name and
-- every annotation carries a location, so the list form would dominate
-- the generated source. @OverloadedStrings@ in the generated module
-- makes the same literal work for 'Text'.
instance {-# OVERLAPPING #-} ToCode String where
  toCode = CString

instance ToCode Text where
  toCode = CString . T.unpack

instance {-# OVERLAPPABLE #-} (ToCode a) => ToCode [a] where
  toCode = CList . map toCode

instance (ToCode a) => ToCode (Maybe a) where
  toCode Nothing = CName "Nothing"
  toCode (Just x) = CApp (CName "Just") [toCode x]

instance (ToCode a, ToCode b) => ToCode (a, b) where
  toCode (a, b) = CTuple [toCode a, toCode b]

instance (ToCode a) => ToCode (NonEmpty a) where
  toCode = CApp (CName "NE.fromList") . pure . toCode . NE.toList

-- The container instances rebuild through the type's own @fromList@
-- rather than a serialized representation, which is what makes the
-- generated module portable: MicroHs's containers package is not
-- required to share GHC's internal structure.
instance (ToCode k, ToCode v) => ToCode (Map k v) where
  toCode = CApp (CName "Map.fromList") . pure . CList . map pair . Map.toList

instance (ToCode v) => ToCode (IntMap v) where
  toCode = CApp (CName "IntMap.fromList") . pure . CList . map pair . IntMap.toList

instance (ToCode v) => ToCode (Set v) where
  toCode = CApp (CName "Set.fromList") . pure . CList . map toCode . Set.toList

instance ToCode IntSet where
  toCode =
    CApp (CName "IntSet.fromList")
      . pure
      . CList
      . map (CInt . toInteger)
      . IntSet.toList

pair :: (ToCode a, ToCode b) => (a, b) -> Code
pair (a, b) = CTuple [toCode a, toCode b]
