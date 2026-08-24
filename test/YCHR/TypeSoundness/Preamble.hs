{-# LANGUAGE OverloadedStrings #-}

-- | The invariant part of every generated module: the fixed algebraic
-- types, the predicate library guards may call, and the runtime type
-- assertions.
--
-- The source text and the Haskell-side tables that describe it live
-- together here because they have to agree; see 'preamble'.
module YCHR.TypeSoundness.Preamble
  ( colorDef,
    shapeDef,
    fixedAdts,
    baseTys,
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
      ctors = CtorDef "red" [] :| [CtorDef "green" [], CtorDef "blue" []]
    }

-- | @shape@ from the fixed preamble.
shapeDef :: AdtDef
shapeDef =
  AdtDef
    { adtName = "shape",
      ctors = CtorDef "circle" [TInt] :| [CtorDef "rect" [TInt, TInt]]
    }

fixedAdts :: [AdtDef]
fixedAdts = [colorDef, shapeDef]

baseTys :: [Ty]
baseTys = [TInt, TBool, TListInt]

-- | Argument and result types of each library predicate.
libFnSig :: LibFn -> ([Ty], Ty)
libFnSig fn = case fn of
  FnLt -> ([TInt, TInt], TBool)
  FnLte -> ([TInt, TInt], TBool)
  FnSameInt -> ([TInt, TInt], TBool)
  FnIsZero -> ([TInt], TBool)
  FnIsNil -> ([TListInt], TBool)
  FnLen -> ([TListInt], TInt)
  FnIsRed -> ([TAdt colorDef], TBool)
  FnArea -> ([TAdt shapeDef], TInt)

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
-- library guards may call, and the runtime type assertions for the
-- non-algebraic types. @color@ and @shape@ — declaration /and/
-- assertion predicate — are rendered from 'colorDef' and 'shapeDef' by
-- 'YCHR.TypeSoundness.Render.renderAdt', the same path generated types
-- take, so the values the generator reasons with and the source it
-- emits cannot drift apart.
--
-- Each @assert_τ@ deep-checks a value against @τ@ and has /no/
-- catch-all equation, so a value outside @τ@ raises \"no matching
-- equation\" (YCHR-60001) instead of quietly passing. Field checks live
-- in equation guards, which are ask-semantics conjunctions: a nested
-- assert either returns @true@ or raises.
--
-- The missing catch-alls are also why every generated module emits
-- non-exhaustive-pattern warnings (YCHR-20103) for the guarded
-- assertion predicates. That is by design — the partiality /is/ the
-- oracle — and the property only annotates warnings, never fails on
-- them.
--
-- The @assert_int@ leaf leans on the prelude's @integer\/1@, whose
-- signature is @any -> bool@. That is instrumentation, not part of the
-- fragment under test; the generated program proper never mentions
-- @any@, and the assertion functions themselves are declared at
-- concrete types.
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
      "area(rect(W, H)) -> (W * H).",
      "",
      ":- function assert_int(int) -> bool.",
      "assert_int(X) | integer(X) -> true.",
      ":- function assert_bool(bool) -> bool.",
      "assert_bool(true) -> true.",
      "assert_bool(false) -> true.",
      ":- function assert_list_int(list(int)) -> bool.",
      "assert_list_int([]) -> true.",
      "assert_list_int([X|Xs]) | assert_int(X), assert_list_int(Xs) -> true."
    ]
