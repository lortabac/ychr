{-# LANGUAGE OverloadedStrings #-}

-- | The core AST the type-soundness generator works in, and the pure
-- helpers over it.
--
-- This module deliberately imports no Hedgehog: it is the vocabulary
-- the generator, the instrumentation, the renderer and the oracle all
-- share, and the gradual-guarantee property is meant to reuse it (see
-- 'ArgSpec').
module YCHR.TypeSoundness.Types
  ( -- * Types
    TvName (..),
    Skolem (..),
    TyCon (..),
    GTy (..),
    DTy (..),
    STy (..),
    CtorDef (..),
    AdtDef (..),

    -- * Skolems
    SkolemEnv (..),
    PinSource (..),
    emptySkolems,
    freshSkolems,
    resolveSTy,
    mergeSTy,
    pinSkolem,
    groundOf,
    substD,
    groundD,
    skolemsOf,
    stripSTy,

    -- * Declarations
    ArgSpec (..),
    Sig (..),
    sigArgDTys,

    -- * Terms
    Lit (..),
    Pat (..),
    ArithOp (..),
    CmpOp (..),
    LibFn (..),
    TypePred (..),
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

    -- * Instrumentation
    ObsSite (..),
    ObsCheck (..),
    PosCheck (..),

    -- * Helpers
    tshow,
    renderGTy,
    renderDTy,
    renderSTy,
    findCtor,
    ctorFieldTys,
    ruleHeadList,
    ruleHeads,
    minHeadStratum,
    headArgTys,
    patVars,
    headVars,
    isTell,
    ruleVars,
    ruleVarsAtHead,
  )
where

import Data.IntMap.Strict (IntMap)
import Data.List (nubBy)
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

-- | A declaration's own type parameter, spelled as an uppercase
-- identifier in source.
newtype TvName = TvName Text
  deriving (Eq, Ord, Show)

-- | A rigid type variable: a declaration's type parameter at an
-- /implementation site/, where it stands for an arbitrary
-- store-chosen instance. Allocated fresh per rule-head occurrence,
-- because \"each rule-head occurrence allocates its own rigid
-- variables, even between two occurrences of the same constraint\"
-- (§Rigid and flexible type variables).
newtype Skolem = Skolem Int
  deriving (Eq, Ord, Show)

-- | A type constructor. 'CList' is @list\/1@; 'CAdt' carries the whole
-- definition rather than a name, so every lookup a generator or the
-- observer needs is already in hand and no name resolution is
-- required. Generated types only mention /earlier/ definitions, so the
-- value is finite.
data TyCon
  = CInt
  | CBool
  | CList
  | CAdt AdtDef
  deriving (Eq, Show)

-- | A ground type: no variables of any kind. What a /use/ site commits
-- to, and what the observer checks a runtime value against.
data GTy = GTy TyCon [GTy]
  deriving (Eq, Show)

-- | A declaration-level type: ground constructors over the
-- declaration's own parameters. What a signature is written in.
data DTy = DCon TyCon [DTy] | DVar TvName
  deriving (Eq, Show)

-- | A type at an /implementation site/: ground constructors over
-- per-occurrence skolems. The whole polymorphism model of the
-- generator is this type plus 'SkolemEnv'.
data STy = SCon TyCon [STy] | SSk Skolem
  deriving (Eq, Show)

data CtorDef = CtorDef {ctorName :: Text, ctorFields :: [DTy]}
  deriving (Eq, Show)

-- | A generated or fixed algebraic type. Parameters are distinct and
-- each is used by at least one field: an unused parameter is legal
-- (phantom types are allowed) but only creates instantiations nothing
-- can tell apart.
data AdtDef = AdtDef
  { adtName :: Text,
    adtParams :: [TvName],
    adtCtors :: NonEmpty CtorDef
  }
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Skolems
-- ---------------------------------------------------------------------------

{- Note [Skolems are one structural store]

The checker's rigid variables need three operations, and they are not
separable:

  * allocate a fresh skolem per implementation site;
  * merge two skolems when HNF emits a `GuardEqual` for a variable
    shared between head positions — "at every depth, not just at the
    top level" (§Evidence forms), so `list(T1)` merging with `list(T2)`
    has to merge `T1` with `T2`;
  * later (stage 4) pin a skolem to a constructor application whose
    parameters are themselves *fresh skolems* — `T := list(beta)` —
    which is what a `GuardMatch` at a rigid scrutinee does.

The third is why a flat union-find plus a `Skolem -> GTy` map is the
wrong shape: a pin creates skolems that a later merge has to reach
through. One `Map Skolem STy`, walked with an occurs check, does all
three, and is an ordinary structural unifier with skolems as its only
variables. It is not a type inference engine: there is no constraint
queue, no residual solving and no overload resolution, because the
generator *chooses* every instantiation rather than inferring it.
-}

data SkolemEnv = SkolemEnv
  { skBind :: Map Skolem STy,
    skNext :: Int,
    -- | How each pinned skolem came to be pinned. Coverage only —
    -- nothing in the generator dispatches on it — but the evidence
    -- forms differ enough that a label per source is the only way to
    -- tell which of them a run actually exercised.
    skPinned :: Map Skolem PinSource
  }
  deriving (Eq, Show)

-- | Which evidence form pinned a skolem.
--
-- The three that HNF emits from a head are guaranteed by matching
-- itself, so they hold before any user guard runs. 'PinTypePred' is a
-- user guard, so its fact holds only to the right of it — which is why
-- the two are observed at different points (see
-- 'YCHR.TypeSoundness.Instrument.instrument').
data PinSource
  = -- | A literal at a rigid position: @c(X, 5)@ at @c(T, T)@.
    PinLit
  | -- | A constructor or list pattern at a rigid scrutinee. Pins the
    -- skolem to that type constructor applied at /fresh rigid/
    -- parameters, not flexible ones.
    PinMatch
  | -- | A variable shared between a rigid position and a concretely
    -- typed one, which HNF turns into a @GuardEqual@.
    PinMergeConcrete
  | -- | An @integer(X)@ or @boolean(X)@ guard.
    PinTypePred
  deriving (Eq, Ord, Show)

emptySkolems :: SkolemEnv
emptySkolems =
  SkolemEnv {skBind = Map.empty, skNext = 0, skPinned = Map.empty}

freshSkolems :: Int -> SkolemEnv -> ([Skolem], SkolemEnv)
freshSkolems n env =
  ( [Skolem i | i <- [env.skNext .. env.skNext + n - 1]],
    env {skNext = env.skNext + n}
  )

-- | Follow bindings until the head is either an 'SCon' or an unbound
-- 'SSk'. Shallow: arguments are left alone.
resolveSTy :: SkolemEnv -> STy -> STy
resolveSTy env t = case t of
  SSk s -> case Map.lookup s env.skBind of
    Just t' -> resolveSTy env t'
    Nothing -> t
  _ -> t

-- | Resolve at every depth, so two structurally equal types compare
-- equal whatever bindings got them there.
stripSTy :: SkolemEnv -> STy -> STy
stripSTy env t = case resolveSTy env t of
  SCon c as -> SCon c (map (stripSTy env) as)
  other -> other

-- | Structural unification with skolems as the only variables, and an
-- occurs check.
--
-- 'Nothing' means the two types cannot be equal. The generator never
-- asks for a merge that would fail — it picks candidate pairs from
-- types it has already checked are mergeable — so a 'Nothing' reaching
-- a caller is a bug in the generator, not a program it could emit.
mergeSTy :: STy -> STy -> SkolemEnv -> Maybe SkolemEnv
mergeSTy a b env0 = go (resolveSTy env0 a) (resolveSTy env0 b) env0
  where
    go x y env = case (x, y) of
      (SSk s, SSk s') | s == s' -> Just env
      (SSk s, _) -> bind s y env
      (_, SSk s) -> bind s x env
      (SCon c as, SCon d bs)
        | c == d, length as == length bs -> foldMergeM as bs env
        | otherwise -> Nothing
    bind s t env
      | occurs env s t = Nothing
      | otherwise = Just env {skBind = Map.insert s t env.skBind}
    foldMergeM [] [] env = Just env
    foldMergeM (x : xs) (y : ys) env =
      mergeSTy x y env >>= foldMergeM xs ys
    foldMergeM _ _ _ = Nothing

-- | Bind a skolem to a type by /evidence/ rather than by unification.
--
-- The only sanctioned exception to the meet table's rigid rows: an
-- evidence form's operational success entails the fact, so code to its
-- right runs only in executions where the fact holds.
pinSkolem :: PinSource -> Skolem -> STy -> SkolemEnv -> Maybe SkolemEnv
pinSkolem src s t env
  | occurs env s t = Nothing
  | otherwise =
      Just
        env
          { skBind = Map.insert s t env.skBind,
            skPinned = Map.insert s src env.skPinned
          }

occurs :: SkolemEnv -> Skolem -> STy -> Bool
occurs env s t = case resolveSTy env t of
  SSk s' -> s == s'
  SCon _ as -> any (occurs env s) as

-- | Read an 'STy' back as a ground type, if nothing rigid is left.
groundOf :: SkolemEnv -> STy -> Maybe GTy
groundOf env t = case resolveSTy env t of
  SSk _ -> Nothing
  SCon c as -> GTy c <$> traverse (groundOf env) as

-- | Every skolem an 'STy' still mentions, resolved.
skolemsOf :: SkolemEnv -> STy -> [Skolem]
skolemsOf env t = case resolveSTy env t of
  SSk s -> [s]
  SCon _ as -> List.nub (concatMap (skolemsOf env) as)

-- | Instantiate a declaration type at an implementation site.
substD :: Map TvName STy -> DTy -> STy
substD sub t = case t of
  DVar v -> Map.findWithDefault (SCon CInt []) v sub
  DCon c as -> SCon c (map (substD sub) as)

-- | Instantiate a declaration type at a use site's ground
-- substitution.
groundD :: Map TvName GTy -> DTy -> GTy
groundD sub t = case t of
  DVar v -> Map.findWithDefault (GTy CInt []) v sub
  DCon c as -> GTy c (map (groundD sub) as)

-- ---------------------------------------------------------------------------
-- Declarations
-- ---------------------------------------------------------------------------

-- | A constraint-argument annotation. 'argTy' is the type the
-- generator picks and reasons with throughout; 'argErased' renders the
-- position as @any@ instead.
--
-- The soundness property never erases — the fragment under test is
-- fully typed by definition — but the gradual-guarantee property works
-- by flipping exactly this field, so it is retained as data here
-- rather than collapsed into 'DTy'.
data ArgSpec = ArgSpec {argTy :: DTy, argErased :: Bool}
  deriving (Eq, Show)

-- | A constraint declaration. 'stratum' is the symbol's position in the
-- program's stratification: rule bodies may only tell strata strictly
-- below every stratum in their head, which is what makes every
-- generated program terminate (see @Note [Termination]@ in
-- "YCHR.TypeSoundness.Instrument").
--
-- @sigTvs@ empty means monomorphic. Every parameter listed is used by
-- at least one argument.
data Sig = Sig
  { sigName :: Text,
    sigTvs :: [TvName],
    sigArgs :: NonEmpty ArgSpec,
    stratum :: Int
  }
  deriving (Eq, Show)

sigArgDTys :: Sig -> NonEmpty DTy
sigArgDTys s = fmap (.argTy) s.sigArgs

-- ---------------------------------------------------------------------------
-- Terms
-- ---------------------------------------------------------------------------

data Lit = LInt Integer | LBool Bool
  deriving (Eq, Show)

data Pat
  = PVar Text STy
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

-- | A prelude type predicate, which is an /evidence form/: its
-- success at run time entails that its argument has that type
-- (§Evidence forms). Only the two the fragment has types for;
-- @float@ and @string@ are outside it.
--
-- Distinct from 'ECall' because the argument is always a variable —
-- evidence attaches to a variable, not to an arbitrary expression —
-- and because the generator has to know which conjuncts change what is
-- known to their right.
data TypePred = PredInteger | PredBoolean
  deriving (Eq, Show)

-- | An expression in an /evaluated/ position: a tell argument, an @is@
-- right-hand side, a guard, or a goal probe.
--
-- Every form here has a known result type; nothing in it can widen to
-- @any@ (no host calls, no @quote@, no unknown constructors) except
-- 'EHostObs', which is instrumentation.
--
-- The 'STy' carried by 'EVar' and 'EEq' — like the one on 'PVar' and
-- 'SVar' — is written but never read: with fully-typed declarations
-- every position's type is recoverable from the signature it sits
-- under. It is there for the gradual-guarantee property, where erased
-- positions make that positional recovery impossible and each variable
-- has to remember the type it was generated at.
data Expr
  = ELit Lit
  | EVar Text STy
  | EListLit [Expr]
  | ECtor Text [Expr]
  | EArith ArithOp Expr Expr
  | ECmp CmpOp Expr Expr
  | EEq STy Expr Expr
  | ENot Expr
  | ECall LibFn [Expr]
  | -- | @integer(V)@ \/ @boolean(V)@ at a rigid-typed variable. The
    -- 'STy' is the variable's type /before/ the pin.
    EPred TypePred Text STy
  | -- | The prelude's @copy_term(A) -> A@. The one polymorphic
    -- function available at a rigid type without a @requiring@ clause,
    -- so it is how an expression can be built at a skolem target
    -- without being a bare variable (which @is@ would widen to @any@).
    ECopy Expr
  | -- | Instrumentation: @host:ts_obs(Code, V…)@. Inserted by
    -- 'YCHR.TypeSoundness.Instrument.instrument', never generated.
    -- Legal in guard position because a host call's result is @any@,
    -- which is consistent with @bool@; the observer always returns
    -- @true@, so a guard it sits in is unchanged.
    EHostObs Int [Expr]
  deriving (Eq, Show)

-- | The right-hand side of @=@. Unlike 'Expr' this is /structural/:
-- @=@ evaluates neither operand, so an evaluable head here would build
-- a symbolic compound typed @any@ and leave the fragment.
data STerm
  = SLit Lit
  | SVar Text STy
  | SNil
  | SCons STerm STerm
  | SCtor Text [STerm]
  deriving (Eq, Show)

data BodyItem
  = -- | A body tell, with the instantiation the generator committed to
    -- for the callee's type parameters.
    BTell Sig (Map TvName STy) [Expr]
  | BIs Text STy Expr
  | BUnify Text STy STerm
  | -- | Instrumentation: @host:ts_obs(Code, V…)@ in body position,
    -- result discarded.
    BObs Int [Expr]
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Rules, goals, programs
-- ---------------------------------------------------------------------------

-- | One head occurrence, with the rigid variables /it/ allocated.
data HeadC = HeadC
  { headSig :: Sig,
    headSkolems :: [Skolem],
    pats :: NonEmpty Pat
  }
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
    -- | Guards that establish a typing fact: a type predicate at a
    -- rigid variable. Kept apart from 'guards' because they change
    -- what is known /to their right/, so the observer has to be told
    -- where they end.
    ruleEvidence :: [Expr],
    guards :: [Expr],
    body :: [BodyItem],
    -- | The skolem state after head matching and its HNF-synthetic
    -- guards, before any user guard. This is what /matching alone/
    -- guarantees, and so what may be asserted of a candidate match
    -- that has not yet passed the rule's own guards.
    ruleSkHead :: SkolemEnv,
    -- | The skolem state this rule's generation ended in: which
    -- skolems it allocated and what merges it performed. Read by
    -- 'YCHR.TypeSoundness.Instrument.instrument' to decide which head
    -- positions have a ground type, and dumped into the counterexample
    -- (a rejected polymorphic rule is unreadable without it).
    ruleSk :: SkolemEnv
  }
  deriving (Eq, Show)

-- | A goal-level @R is E@ binding whose result the oracle inspects
-- directly, in Haskell ('YCHR.TypeSoundness.Oracle.conforms' over the
-- returned term).
data Probe = Probe {probeVar :: Text, probeTy :: GTy, probeExpr :: Expr}
  deriving (Eq, Show)

data Goal = Goal {tells :: NonEmpty (Sig, [Expr]), probes :: [Probe]}
  deriving (Eq, Show)

data Program = Program
  { adts :: [AdtDef],
    sigs :: NonEmpty Sig,
    rules :: [Rule],
    goal :: Goal,
    -- | Empty until 'YCHR.TypeSoundness.Instrument.instrument' fills
    -- it. Keyed by the code each 'EHostObs' \/ 'BObs' carries.
    obs :: IntMap ObsSite
  }
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Instrumentation
-- ---------------------------------------------------------------------------

-- | One instrumentation point.
data ObsSite = ObsSite
  { -- | Where it sits, for the counterexample text: @\"r3 head\"@,
    -- @\"r3 fired\"@, @\"r3 binds W0\"@.
    osWhere :: Text,
    osCheck :: ObsCheck
  }
  deriving (Eq, Show)

newtype ObsCheck = ExpectPos [PosCheck]
  deriving (Eq, Show)

-- | What the observer can say about the value at one position.
data PosCheck
  = -- | The position has a ground static type, so the value must
    -- inhabit it.
    MustInhabit GTy
  | -- | The position's type is a rigid variable, so there is no static
    -- type to compare against — the store chose the instance and the
    -- rule was checked for /every/ instance. All that can be asserted
    -- is that a value is there at all.
    --
    -- The obvious stronger check — that the values sharing one merged
    -- skolem agree in type — is not worth its cost: a merge only
    -- arises from a variable shared between head positions, HNF turns
    -- that into a @GuardEqual@, and ask-equality succeeds only on
    -- structurally /identical/ terms. So agreement of type is implied
    -- by something strictly stronger that the runtime already
    -- enforces before the rule can fire.
    MustBeBound
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

tshow :: (Show a) => a -> Text
tshow = T.pack . show

renderGTy :: GTy -> Text
renderGTy (GTy c as) = renderApp (tyConName c) (map renderGTy as)

renderDTy :: DTy -> Text
renderDTy t = case t of
  DVar (TvName v) -> v
  DCon c as -> renderApp (tyConName c) (map renderDTy as)

renderSTy :: STy -> Text
renderSTy t = case t of
  SSk (Skolem i) -> "T#" <> tshow i
  SCon c as -> renderApp (tyConName c) (map renderSTy as)

tyConName :: TyCon -> Text
tyConName c = case c of
  CInt -> "int"
  CBool -> "bool"
  CList -> "list"
  CAdt def -> def.adtName

renderApp :: Text -> [Text] -> Text
renderApp f [] = f
renderApp f as = f <> "(" <> T.intercalate ", " as <> ")"

findCtor :: AdtDef -> Text -> Maybe CtorDef
findCtor def n = List.find (\c -> c.ctorName == n) (NE.toList def.adtCtors)

-- | A constructor's field types at a given instantiation of its
-- type's parameters.
ctorFieldTys :: AdtDef -> [STy] -> CtorDef -> [STy]
ctorFieldTys def args c = map (substD sub) c.ctorFields
  where
    sub = Map.fromList (zip def.adtParams args)

ruleHeadList :: RuleHead -> NonEmpty HeadC
ruleHeadList rh = case rh of
  HSimplify hs -> hs
  HPropagate hs -> hs
  HSimpagate ks rs -> ks <> rs

ruleHeads :: Rule -> [HeadC]
ruleHeads r = NE.toList (ruleHeadList r.ruleHead)

minHeadStratum :: Rule -> Int
minHeadStratum r = minimum [h.headSig.stratum | h <- ruleHeads r]

-- | The implementation-site types of one head occurrence's argument
-- positions: the declaration's argument types at that occurrence's own
-- rigid variables.
headArgTys :: HeadC -> NonEmpty STy
headArgTys h = fmap (substD sub) (sigArgDTys h.headSig)
  where
    sub = Map.fromList (zip h.headSig.sigTvs (map SSk h.headSkolems))

-- | Every variable bound by a pattern, with its implementation-site
-- type, in left-to-right order. Names may repeat:
-- 'YCHR.TypeSoundness.Gen.maybeAlias' can rename one pattern variable
-- to another, which is the point of that pass. 'ruleVars' is the
-- deduplicating wrapper.
--
-- The type comes from the position, not from the variable's own 'STy'
-- field, and an ill-shaped pattern is an 'error' rather than an empty
-- result: this is what decides which variables get observed, so
-- silently returning fewer would silently weaken the oracle.
patVars :: SkolemEnv -> STy -> Pat -> [(Text, STy)]
patVars env ty p = case p of
  PVar n _ -> [(n, ty)]
  PWild -> []
  PLit _ -> []
  PNil -> []
  PCons h t -> case resolveSTy env ty of
    SCon CList [el] -> patVars env el h ++ patVars env ty t
    _ -> error ("patVars: cons pattern at " ++ T.unpack (renderSTy ty))
  PCtor cn ps -> case resolveSTy env ty of
    SCon (CAdt def) args -> case findCtor def cn of
      Just c
        | length c.ctorFields == length ps ->
            concat (zipWith (patVars env) (ctorFieldTys def args c) ps)
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
            ++ T.unpack (renderSTy ty)
        )

headVars :: SkolemEnv -> HeadC -> [(Text, STy)]
headVars env h =
  concat (zipWith (patVars env) (NE.toList (headArgTys h)) (NE.toList h.pats))

isTell :: BodyItem -> Bool
isTell it = case it of
  BTell {} -> True
  _ -> False

-- | Every head-bound variable of a rule, deduplicated by name, under
-- the rule's own final skolem state.
ruleVars :: Rule -> [(Text, STy)]
ruleVars r =
  nubBy (\a b -> fst a == fst b) (concatMap (headVars r.ruleSk) (ruleHeads r))

-- | As 'ruleVars', but under the state matching alone establishes.
ruleVarsAtHead :: Rule -> [(Text, STy)]
ruleVarsAtHead r =
  nubBy (\a b -> fst a == fst b) (concatMap (headVars r.ruleSkHead) (ruleHeads r))
