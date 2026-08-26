{-# LANGUAGE OverloadedStrings #-}

-- | The invariant part of every generated module: the fixed algebraic
-- types and the predicate library guards may call.
--
-- The source text and the Haskell-side tables that describe it live
-- together here because they have to agree; see 'preamble'.
module YCHR.TypeSoundness.Preamble
  ( colorDef,
    shapeDef,
    fixedAdts,
    baseTys,
    gInt,
    gBool,
    gList,
    gAdt,
    libFnSig,
    libFnName,
    preamble,
  )
where

import Data.List.NonEmpty (NonEmpty (..))
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.TypeSoundness.Types

-- | @color@ from the fixed preamble, as an 'AdtDef' so generated code
-- can use it exactly like a generated type.
colorDef :: AdtDef
colorDef =
  AdtDef
    { adtName = "color",
      adtParams = [],
      adtCtors =
        CtorDef "red" [] :| [CtorDef "green" [], CtorDef "blue" []]
    }

-- | @shape@ from the fixed preamble.
shapeDef :: AdtDef
shapeDef =
  AdtDef
    { adtName = "shape",
      adtParams = [],
      adtCtors =
        CtorDef "circle" [DCon CInt []]
          :| [CtorDef "rect" [DCon CInt [], DCon CInt []]]
    }

fixedAdts :: [AdtDef]
fixedAdts = [colorDef, shapeDef]

gInt :: GTy
gInt = GTy CInt []

gBool :: GTy
gBool = GTy CBool []

gList :: GTy -> GTy
gList t = GTy CList [t]

gAdt :: AdtDef -> [GTy] -> GTy
gAdt def args = GTy (CAdt def) args

-- | The ground types every program starts from, before the generated
-- definitions widen the universe.
baseTys :: [GTy]
baseTys = [gInt, gBool, gList gInt, gAdt colorDef [], gAdt shapeDef []]

-- | Argument and result types of each library predicate. Every one is
-- monomorphic: the polymorphism under test comes from generated
-- declarations, not from the fixture.
libFnSig :: LibFn -> ([GTy], GTy)
libFnSig fn = case fn of
  FnLt -> ([gInt, gInt], gBool)
  FnLte -> ([gInt, gInt], gBool)
  FnSameInt -> ([gInt, gInt], gBool)
  FnIsZero -> ([gInt], gBool)
  FnIsNil -> ([gList gInt], gBool)
  FnLen -> ([gList gInt], gInt)
  FnIsRed -> ([gAdt colorDef []], gBool)
  FnArea -> ([gAdt shapeDef []], gInt)

libFnName :: LibFn -> Text
libFnName fn = case fn of
  FnLt -> "lt"
  FnLte -> "lte"
  FnSameInt -> "same_int"
  FnIsZero -> "is_zero"
  FnIsNil -> "is_nil"
  FnLen -> "len"
  FnIsRed -> "is_red"
  FnArea -> "area"

-- | The invariant part of every generated module: the predicate
-- library that guards may call. @color@ and @shape@ are rendered from
-- 'colorDef' and 'shapeDef' by 'YCHR.TypeSoundness.Render.renderAdt',
-- the same path generated types take, so the values the generator
-- reasons with and the source it emits cannot drift apart.
--
-- Every predicate here is total and fully typed. That is what lets the
-- oracle stay strict: the only partial functions a generated module
-- could contain would be its own, and it has none, so a
-- \"no matching equation\" at run time is a value outside every
-- equation's pattern set rather than instrumentation noise. It is also
-- why a generated module emits no warnings at all — the oracle treats
-- any warning as a failure.
--
-- Runtime type checking is /not/ done here. It is done by the host
-- observer ("YCHR.TypeSoundness.Observe"), which sees the raw runtime
-- 'YCHR.Internal.Runtime.Types.Value' rather than having to be
-- expressible as a CHR predicate — so it works at positions no
-- in-language assertion could describe, a rigid one above all.
--
-- The signatures here are restated in 'libFnSig' \/ 'libFnName', which
-- is what the generator consults when it emits a call. Keep the two in
-- step.
preamble :: Text
preamble =
  T.unlines
    [ ":- function lt(int, int) -> bool.",
      "lt(X, Y) -> (X < Y).",
      ":- function lte(int, int) -> bool.",
      "lte(X, Y) -> (X =< Y).",
      ":- function same_int(int, int) -> bool.",
      "same_int(X, Y) -> (X == Y).",
      ":- function is_zero(int) -> bool.",
      "is_zero(X) -> (X == 0).",
      ":- function is_nil(list(int)) -> bool.",
      "is_nil([]) -> true.",
      "is_nil([_|_]) -> false.",
      ":- function len(list(int)) -> int.",
      "len([]) -> 0.",
      "len([_|Xs]) -> (1 + len(Xs)).",
      ":- function is_red(color) -> bool.",
      "is_red(red) -> true.",
      "is_red(_) -> false.",
      ":- function area(shape) -> int.",
      "area(circle(R)) -> (R * R).",
      "area(rect(W, H)) -> (W * H)."
    ]
