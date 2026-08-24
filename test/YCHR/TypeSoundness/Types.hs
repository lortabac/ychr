{-# LANGUAGE OverloadedStrings #-}

-- | The core AST the type-soundness generator works in, and the pure
-- helpers over it.
--
-- This module deliberately imports no Hedgehog: it is the vocabulary
-- the generator, the instrumentation, the renderer and the oracle all
-- share, and the gradual-guarantee property is meant to reuse it (see
-- 'Ann').
module YCHR.TypeSoundness.Types
  ( -- * Types
    Ty (..),
    Ann (..),
    CtorDef (..),
    AdtDef (..),
    Sig (..),

    -- * Terms
    Lit (..),
    Pat (..),
    ArithOp (..),
    CmpOp (..),
    LibFn (..),
    Expr (..),
    STerm (..),
    BodyItem (..),

    -- * Rules, goals, programs
    HeadC (..),
    RuleHead (..),
    Rule (..),
    Probe (..),
    Goal (..),
    Program (..),

    -- * Helpers
    tshow,
    renderTy,
    sigArgTys,
    findCtor,
    ruleHeadList,
    ruleHeads,
    minHeadStratum,
    patVars,
    headVars,
    isTell,
    ruleVars,
    assertFn,
  )
where

import Data.List (find, nubBy)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Text (Text)
import Data.Text qualified as T

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

-- | A type of the fragment under test. @float@ and @string@ are left
-- out of v1; @list(int)@ is the one recursive shape, which is enough to
-- exercise recursion without a depth budget on type definitions.
--
-- 'TAdt' carries the whole definition rather than a name, so every
-- lookup a generator or the conformance checker needs is already in
-- hand and no partial name resolution is required. Generated ADTs only
-- ever mention /earlier/ definitions, so the value is finite.
data Ty
  = TInt
  | TBool
  | TListInt
  | TAdt AdtDef
  deriving (Eq, Show)

-- | A constraint-argument annotation. 'declared' is the type the
-- generator picks and reasons with throughout; 'erased' renders the
-- position as @any@ instead.
--
-- The soundness property never erases — the fragment under test is
-- fully typed by definition — but the gradual-guarantee property works
-- by flipping exactly this field, so it is retained as data here rather
-- than collapsed into 'Ty'.
data Ann = Ann {declared :: Ty, erased :: Bool}
  deriving (Eq, Show)

data CtorDef = CtorDef {ctorName :: Text, fields :: [Ty]}
  deriving (Eq, Show)

data AdtDef = AdtDef {adtName :: Text, ctors :: NonEmpty CtorDef}
  deriving (Eq, Show)

-- | A constraint declaration. 'stratum' is the symbol's position in the
-- program's stratification: rule bodies may only tell strata strictly
-- below every stratum in their head, which is what makes every
-- generated program terminate (see @Note [Termination]@ in
-- "YCHR.TypeSoundness.Instrument").
data Sig = Sig {sigName :: Text, argAnns :: NonEmpty Ann, stratum :: Int}
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Terms
-- ---------------------------------------------------------------------------

data Lit = LInt Integer | LBool Bool
  deriving (Eq, Show)

data Pat
  = PVar Text Ty
  | PWild
  | PLit Lit
  | PCtor Text [Pat]
  | PNil
  | PCons Pat Pat
  deriving (Eq, Show)

data ArithOp = Add | Sub | Mul
  deriving (Eq, Show)

data CmpOp = CLt | CGt | CGe | CLe
  deriving (Eq, Show)

-- | The fixed hand-written predicate library the module preamble
-- defines (see "YCHR.TypeSoundness.Preamble"). Every one of them is
-- total and fully typed, which is what lets the oracle stay strict.
data LibFn
  = FnLt
  | FnLte
  | FnSameInt
  | FnIsZero
  | FnIsNil
  | FnLen
  | FnIsRed
  | FnArea
  deriving (Eq, Show)

-- | An expression in an /evaluated/ position: a tell argument, an @is@
-- right-hand side, a guard, or a goal probe.
--
-- Every form here has a known result type; nothing in it can widen to
-- @any@ (no host calls, no @quote@, no unknown constructors).
--
-- The 'Ty' carried by 'EVar' and 'EEq' — like the one on 'PVar' and
-- 'SVar' — is written but never read: with fully-typed declarations
-- every position's type is recoverable from the signature it sits
-- under. It is there for the gradual-guarantee property, where erased
-- positions make that positional recovery impossible and each variable
-- has to remember the type it was generated at.
data Expr
  = ELit Lit
  | EVar Text Ty
  | EListLit [Expr]
  | ECtor Text [Expr]
  | EArith ArithOp Expr Expr
  | ECmp CmpOp Expr Expr
  | EEq Ty Expr Expr
  | ENot Expr
  | ECall LibFn [Expr]
  deriving (Eq, Show)

-- | The right-hand side of @=@. Unlike 'Expr' this is /structural/:
-- @=@ evaluates neither operand, so an evaluable head here would build
-- a symbolic compound typed @any@ and leave the fragment.
data STerm
  = SLit Lit
  | SVar Text Ty
  | SNil
  | SCons STerm STerm
  | SCtor Text [STerm]
  deriving (Eq, Show)

data BodyItem
  = BTell Sig [Expr]
  | BIs Text Ty Expr
  | BUnify Text Ty STerm
  | -- | Instrumentation: @assert_τ(V)@ in body position, result
    -- discarded. Inserted by
    -- 'YCHR.TypeSoundness.Instrument.instrument', never generated
    -- directly.
    BAssert Text Ty
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Rules, goals, programs
-- ---------------------------------------------------------------------------

data HeadC = HeadC {headSig :: Sig, pats :: NonEmpty Pat}
  deriving (Eq, Show)

-- | The three CHR rule shapes. Kept as a sum rather than a pair of
-- possibly-empty lists so that \"no head at all\" is unrepresentable.
data RuleHead
  = HSimplify (NonEmpty HeadC)
  | HPropagate (NonEmpty HeadC)
  | HSimpagate (NonEmpty HeadC) (NonEmpty HeadC)
  deriving (Eq, Show)

data Rule = Rule
  { ruleName :: Text,
    ruleHead :: RuleHead,
    guards :: [Expr],
    body :: [BodyItem]
  }
  deriving (Eq, Show)

-- | A goal-level @R is E@ binding whose result the oracle inspects
-- directly, both in-language (an @assert_τ@ conjunct) and in Haskell
-- ('YCHR.TypeSoundness.Oracle.conforms' over the returned term).
data Probe = Probe {probeVar :: Text, probeTy :: Ty, probeExpr :: Expr}
  deriving (Eq, Show)

data Goal = Goal {tells :: NonEmpty (Sig, [Expr]), probes :: [Probe]}
  deriving (Eq, Show)

data Program = Program
  { adts :: [AdtDef],
    sigs :: NonEmpty Sig,
    rules :: [Rule],
    goal :: Goal
  }
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

tshow :: (Show a) => a -> Text
tshow = T.pack . show

-- | The source-syntax name of a type. It lives here rather than in
-- "YCHR.TypeSoundness.Render" because it is the only rendering a
-- 'Ty' needs and 'patVars' reports it in its error messages.
renderTy :: Ty -> Text
renderTy ty = case ty of
  TInt -> "int"
  TBool -> "bool"
  TListInt -> "list(int)"
  TAdt def -> def.adtName

sigArgTys :: Sig -> NonEmpty Ty
sigArgTys s = fmap (.declared) s.argAnns

findCtor :: AdtDef -> Text -> Maybe CtorDef
findCtor def n = find (\c -> c.ctorName == n) (NE.toList def.ctors)

ruleHeadList :: RuleHead -> NonEmpty HeadC
ruleHeadList rh = case rh of
  HSimplify hs -> hs
  HPropagate hs -> hs
  HSimpagate ks rs -> ks <> rs

ruleHeads :: Rule -> [HeadC]
ruleHeads r = NE.toList (ruleHeadList r.ruleHead)

minHeadStratum :: Rule -> Int
minHeadStratum r = minimum [h.headSig.stratum | h <- ruleHeads r]

-- | Every variable bound by a pattern, with its static type, in
-- left-to-right order. Names may repeat:
-- 'YCHR.TypeSoundness.Gen.maybeAlias' can rename one pattern variable
-- to another, which is the point of that pass. 'ruleVars' is the
-- deduplicating wrapper.
--
-- The type comes from the position, not from the variable's own 'Ty'
-- field, and an ill-shaped pattern is an 'error' rather than an empty
-- result: this is what decides which variables get an @assert_τ@, so
-- silently returning fewer would silently weaken the oracle.
patVars :: Ty -> Pat -> [(Text, Ty)]
patVars ty p = case p of
  PVar n _ -> [(n, ty)]
  PWild -> []
  PLit _ -> []
  PNil -> []
  PCons h t -> patVars TInt h ++ patVars TListInt t
  PCtor cn ps -> case ty of
    TAdt def -> case findCtor def cn of
      Just c
        | length c.fields == length ps -> concat (zipWith patVars c.fields ps)
        | otherwise -> error ("patVars: arity mismatch for " ++ T.unpack cn)
      Nothing ->
        error
          ( "patVars: "
              ++ T.unpack cn
              ++ " is not a constructor of "
              ++ T.unpack def.adtName
          )
    _ ->
      error
        ( "patVars: constructor pattern at non-algebraic type "
            ++ T.unpack (renderTy ty)
        )

headVars :: HeadC -> [(Text, Ty)]
headVars h =
  concat (zipWith patVars (NE.toList (sigArgTys h.headSig)) (NE.toList h.pats))

isTell :: BodyItem -> Bool
isTell it = case it of
  BTell _ _ -> True
  _ -> False

ruleVars :: Rule -> [(Text, Ty)]
ruleVars r = nubBy (\a b -> fst a == fst b) (concatMap headVars (ruleHeads r))

-- | Name of the runtime assertion predicate for a type.
assertFn :: Ty -> Text
assertFn ty = case ty of
  TInt -> "assert_int"
  TBool -> "assert_bool"
  TListInt -> "assert_list_int"
  TAdt def -> "assert_" <> def.adtName
