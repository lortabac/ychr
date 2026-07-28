{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | GHC-only Generic derivation for the "YCHR.Convert" classes.
--
-- Deriving 'GHC.Generics.Generic' on a data type is enough to get
-- 'YCHR.Convert.ToTerm' / 'YCHR.Convert.FromTerm' instances via the two
-- helpers here — no hand-written instance body required:
--
-- > import GHC.Generics (Generic)
-- > import YCHR.Convert (ToTerm (..), FromTerm (..))
-- > import YCHR.Convert.Generic (genericToTerm, genericFromTerm)
-- >
-- > data Color = Red | Green | Blue deriving (Show, Generic)
-- >
-- > instance ToTerm   Color where toTerm   = genericToTerm    -- Red -> atom "red"
-- > instance FromTerm Color where fromTerm = genericFromTerm
--
-- = Encoding
--
-- A constructor becomes a compound whose functor is the constructor name
-- with its first character lowercased (Haskell constructors are uppercase;
-- CHR functor atoms are lowercase). Fields become positional arguments in
-- declaration order; a nullary constructor becomes an atom. Record field
-- names are ignored (positional encoding), so a generic-derived instance
-- agrees with a hand-written one.
--
-- This module depends on "GHC.Generics", which MicroHS cannot compile, so
-- it is built only under GHC (see @if impl(ghc)@ in @ychr.cabal@). The core
-- "YCHR.Convert" is Generics-free and works on every backend.
module YCHR.Convert.Generic
  ( genericToTerm,
    genericFromTerm,
  )
where

import Data.Char (toLower)
import Data.Text (Text)
import Data.Text qualified as Text
import GHC.Generics
import YCHR.Convert
  ( ConvertError,
    FromTerm (..),
    ToTerm (..),
    argAt,
    compound,
    decodeSum,
  )
import YCHR.Types (Term)

-- | Encode any 'Generic' value as a 'Term'. See the module header for the
-- constructor-to-functor convention.
genericToTerm :: (Generic a, GToTerm (Rep a)) => a -> Term
genericToTerm = gToTerm . from

-- | Decode a 'Term' into any 'Generic' value. The inverse of
-- 'genericToTerm': dispatches on functor and arity across the type's
-- constructors.
genericFromTerm :: forall a. (Generic a, GFromTerm (Rep a)) => Term -> Either ConvertError a
genericFromTerm t = to <$> decodeSum (gRows @(Rep a)) t

-- | The functor atom for a constructor name: lowercase the first character
-- only. @Red -> "red"@, @MkPoint -> "mkPoint"@.
functorName :: String -> Text
functorName [] = ""
functorName (c : cs) = Text.pack (toLower c : cs)

-- ---------------------------------------------------------------------------
-- ToTerm side
-- ---------------------------------------------------------------------------

-- | Encode a generic representation as a whole 'Term' (datatype, sum, and
-- constructor levels).
class GToTerm f where
  gToTerm :: f p -> Term

-- | Encode a generic product as a positional argument list.
class GProdTo f where
  gProdTo :: f p -> [Term]

instance (GToTerm f) => GToTerm (M1 D d f) where
  gToTerm (M1 x) = gToTerm x

instance (GToTerm f, GToTerm g) => GToTerm (f :+: g) where
  gToTerm (L1 x) = gToTerm x
  gToTerm (R1 y) = gToTerm y

instance (Constructor c, GProdTo f) => GToTerm (M1 C c f) where
  gToTerm m@(M1 x) = compound (functorName (conName m)) (gProdTo x)

instance (GProdTo f, GProdTo g) => GProdTo (f :*: g) where
  gProdTo (a :*: b) = gProdTo a ++ gProdTo b

instance (GProdTo f) => GProdTo (M1 S s f) where
  gProdTo (M1 x) = gProdTo x

instance (ToTerm c) => GProdTo (K1 R c) where
  gProdTo (K1 x) = [toTerm x]

instance GProdTo U1 where
  gProdTo U1 = []

-- ---------------------------------------------------------------------------
-- FromTerm side
-- ---------------------------------------------------------------------------

-- | Rows describing each constructor of a generic representation:
-- @(functor, arity, build-from-args)@. Fed to 'decodeSum'.
class GFromTerm f where
  gRows :: [(Text, Int, [Term] -> Either ConvertError (f p))]

-- | Build a generic product from a positional argument list, and report how
-- many arguments it consumes.
class GProdFrom f where
  gArity :: Int
  gBuild :: [Term] -> Either ConvertError (f p)

instance (GFromTerm f) => GFromTerm (M1 D d f) where
  gRows = map (\(n, ar, h) -> (n, ar, fmap M1 . h)) (gRows @f)

instance (GFromTerm f, GFromTerm g) => GFromTerm (f :+: g) where
  gRows =
    map (\(n, ar, h) -> (n, ar, fmap L1 . h)) (gRows @f)
      ++ map (\(n, ar, h) -> (n, ar, fmap R1 . h)) (gRows @g)

instance (Constructor c, GProdFrom f) => GFromTerm (M1 C c f) where
  gRows =
    [ ( functorName (conName (undefined :: M1 C c f p)),
        gArity @f,
        \args -> M1 <$> gBuild args
      )
    ]

instance (GProdFrom f, GProdFrom g) => GProdFrom (f :*: g) where
  gArity = gArity @f + gArity @g
  gBuild args =
    let (la, lb) = splitAt (gArity @f) args
     in (:*:) <$> gBuild la <*> gBuild lb

instance (GProdFrom f) => GProdFrom (M1 S s f) where
  gArity = gArity @f
  gBuild args = M1 <$> gBuild args

instance (FromTerm c) => GProdFrom (K1 R c) where
  gArity = 1
  gBuild args = K1 <$> argAt 0 args

instance GProdFrom U1 where
  gArity = 0
  gBuild _ = Right U1
