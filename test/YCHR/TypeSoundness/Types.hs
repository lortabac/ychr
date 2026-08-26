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
    isSkTy,
    CtorDef (..),
    AdtDef (..),

    -- * Skolems
    SkolemEnv (..),
    PinSource (..),
    emptySkolems,
    freshSkolems,
    resolveSTy,
    mergeSTy,
    eqUnifySTy,
    forceSTy,
    runtimeView,
    pinSkolem,
    groundOf,
    substD,
    groundD,
    groundDTy,
    skolemsOf,
    stripSTy,

    -- * Declarations
    Boundness (..),
    ArgSpec (..),
    Sig (..),
    sigArgDTys,
    TwoOrMore (..),
    twoOrMoreList,
    ClassFn (..),
    BoundSig (..),
    classInstances,

    -- * Terms
    Lit (..),
    Pat (..),
    ArithOp (..),
    CmpOp (..),
    LibFn (..),
    TypePred (..),
    ModePred (..),
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
    varBoundness,
    varBoundnessAtHead,
  )
where

import Control.Monad (foldM)
import Data.IntMap.Strict (IntMap)
import Data.List (nubBy)
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
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

-- | Is this type a bare skolem? Shallow on purpose: a constructor
-- application over skolems is /not/ one, which is what makes this the
-- shared test for a skolem-to-skolem merge in 'skBind' (used by the
-- generator's alias draw, its pin bookkeeping, and the coverage
-- labels — they must agree on it).
isSkTy :: STy -> Bool
isSkTy t = case t of
  SSk _ -> True
  SCon _ _ -> False

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
    skPinned :: Map Skolem PinSource,
    -- | Runtime-only identifications: bindings the shared /value/ of
    -- an alias forces on skolem instances that the checker derives
    -- nothing about — the parameter positions of a shared type
    -- constructor, and the fresh betas of a parametric pin
    -- (§What evidence does: at parameter depth equality evidence is
    -- vacuous for rigid variables). 'skBind' is the checker's
    -- knowledge and drives every typing decision downstream;
    -- 'skForce' is consulted only when a rule instance is grounded
    -- ('runtimeView'), so the store really holds values the alias
    -- can match.
    skForce :: Map Skolem STy
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
  SkolemEnv
    { skBind = Map.empty,
      skNext = 0,
      skPinned = Map.empty,
      skForce = Map.empty
    }

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

-- | The checker's model of a @GuardEqual@ between two head-position
-- types (§What evidence does), plus the runtime forcing the shared
-- value implies. What the /checker/ learns goes into 'skBind':
--
--   * skolem ~ skolem, whole types: the merge (alias one to the
--     other);
--   * skolem ~ non-parametric application: the exact pin;
--   * skolem ~ parametric application: a pin to that constructor at
--     __fresh__ skolems, unrelated to the partner's parameters;
--   * inside a shared constructor: nothing — a parameter-erasing
--     value may account for the equality.
--
-- What the /store/ must satisfy for the alias to actually fire — the
-- parameter identifications the checker deliberately does not assume
-- — goes into 'skForce' via 'forceSTy'. 'Nothing' means the
-- generator cannot arrange a firing instance (an outermost-
-- constructor mismatch, an occurs violation, or a forcing conflict);
-- such a pair is simply not aliased. The checker may accept shapes
-- the generator declines to build (a parameter mismatch is live via
-- a parameter-erasing witness), but the generator only emits aliases
-- whose firing it can arrange with plain value draws.
eqUnifySTy :: STy -> STy -> SkolemEnv -> Maybe SkolemEnv
eqUnifySTy a b env0 =
  case (resolveSTy env0 a, resolveSTy env0 b) of
    (SSk s, SSk s')
      | s == s' -> Just env0
      | otherwise -> bindStatic s (SSk s') env0
    (SSk s, t@(SCon _ [])) -> bindStatic s t env0
    (t@(SCon _ []), SSk s) -> bindStatic s t env0
    (SSk s, SCon c as) -> pinParametric s c as env0
    (SCon c as, SSk s) -> pinParametric s c as env0
    (x@(SCon c as), y@(SCon d bs))
      | c == d, length as == length bs -> forceSTy x y env0
      | otherwise -> Nothing
  where
    bindStatic s t env
      -- Occurs-checked under the runtime view: a cycle closed only
      -- through a forcing would make 'runtimeView' loop just as
      -- surely as one in 'skBind' alone.
      | occursRt env s t = Nothing
      | otherwise =
          -- An earlier link may have force-constrained this skolem's
          -- instance; the static pin narrows the same instance, so
          -- the two must be reconcilable or no store value satisfies
          -- both links.
          reconcileForce s t (env {skBind = Map.insert s t env.skBind})
    pinParametric s c as env =
      let (betas, env1) = freshSkolems (length as) env
          t = SCon c (map SSk betas)
       in do
            env2 <- bindStatic s t env1
            foldM (\e (bta, arg) -> forceSTy (SSk bta) arg e) env2 (zip betas as)
    reconcileForce s t env = case Map.lookup s env.skForce of
      Nothing -> Just env
      Just f -> forceSTy t f env

-- | Runtime-only unification: identify two skolem /instances/ without
-- teaching the checker model anything. Resolves through both maps and
-- writes new bindings into 'skForce'. Same contract as 'mergeSTy'
-- otherwise (occurs-checked; 'Nothing' means the two instances cannot
-- agree).
forceSTy :: STy -> STy -> SkolemEnv -> Maybe SkolemEnv
forceSTy a b env0 = go (resolveRt env0 a) (resolveRt env0 b) env0
  where
    go x y env = case (x, y) of
      (SSk s, SSk s') | s == s' -> Just env
      (SSk s, _) -> bind s y env
      (_, SSk s) -> bind s x env
      (SCon c as, SCon d bs)
        | c == d, length as == length bs -> foldForce as bs env
        | otherwise -> Nothing
    bind s t env
      | occursRt env s t = Nothing
      | otherwise = Just env {skForce = Map.insert s t env.skForce}
    foldForce [] [] env = Just env
    foldForce (x : xs) (y : ys) env =
      forceSTy x y env >>= foldForce xs ys
    foldForce _ _ _ = Nothing

-- | Resolve through the checker bindings /and/ the runtime forcings.
resolveRt :: SkolemEnv -> STy -> STy
resolveRt env t = case t of
  SSk s -> case Map.lookup s env.skBind of
    Just t' -> resolveRt env t'
    Nothing -> case Map.lookup s env.skForce of
      Just t' -> resolveRt env t'
      Nothing -> t
  _ -> t

occursRt :: SkolemEnv -> Skolem -> STy -> Bool
occursRt env s t = case resolveRt env t of
  SSk s' -> s == s'
  SCon _ as -> any (occursRt env s) as

-- | The environment a rule /instance/ is grounded under: the checker
-- bindings with the runtime forcings filled in behind them. Only
-- instance generation may look at this — every typing decision uses
-- the plain env, or the generator would rely on facts the checker
-- deliberately does not derive.
runtimeView :: SkolemEnv -> SkolemEnv
runtimeView env =
  env
    { skBind = Map.union env.skBind env.skForce,
      skForce = Map.empty
    }

-- | Bind a skolem to a type by /evidence/ rather than by unification.
--
-- The only sanctioned exception to the meet table's rigid rows: an
-- evidence form's operational success entails the fact, so code to its
-- right runs only in executions where the fact holds.
--
-- A skolem whose instance an alias has force-constrained ('skForce')
-- refuses a pin that the forcing cannot reconcile with: the guard
-- would test a value the store draw already fixed at another type, so
-- the rule could never fire.
pinSkolem :: PinSource -> Skolem -> STy -> SkolemEnv -> Maybe SkolemEnv
pinSkolem src s t env
  -- Runtime-view occurs check, like 'eqUnifySTy': a cycle through a
  -- forcing would hang instance grounding.
  | occursRt env s t = Nothing
  | otherwise = do
      env' <- case Map.lookup s env.skForce of
        Nothing -> Just env
        Just f -> forceSTy t f env
      Just
        env'
          { skBind = Map.insert s t env'.skBind,
            skPinned = Map.insert s src env'.skPinned
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

-- | A declaration type that mentions no type parameter, read as a
-- ground type.
--
-- Not 'groundD' with an empty substitution: that falls back to a
-- default for an unmapped parameter, so a position declared at a type
-- variable would come back looking like @int@. Two call sites needed
-- to know the difference and neither could get it from 'groundD'.
groundDTy :: DTy -> Maybe GTy
groundDTy t = case t of
  DVar _ -> Nothing
  DCon c as -> GTy c <$> traverse groundDTy as

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
data ArgSpec = ArgSpec
  { argTy :: DTy,
    argErased :: Bool,
    argBound :: Boundness
  }
  deriving (Eq, Show)

{- Note [Boundness is declared, not inferred]

Whether the generator may emit `X + 1` depends on whether `X` can be
unbound, which depends on the tells the generator is about to emit.
Inferring boundness by a fixpoint over the finished program therefore
arrives too late to steer generation.

So each constraint argument position CARRIES a boundness contract,
drawn when the signature is drawn. Generation reads it; the runtime
observer is told it, and tolerates a term holding no value yet exactly
where the contract allows one.

This is a *mode* discipline, not a typing one — the axis
`docs/reference/type-system.md` §No mode checking says YCHR does not
track. A `MayBeUnbound` position is what makes the store-interleaving
shapes reachable at all: something has to be willing to hold an unbound
value before another unit can bind it.
-}

-- | Whether a position may hold a term that is not bound yet.
--
-- Ordered so 'max' is the join: 'Ground' is the stronger claim.
data Boundness = Ground | MayBeUnbound
  deriving (Eq, Ord, Show)

-- | A list with at least two elements.
--
-- Not a convenience: a single-signature @:- class@ is partitioned by
-- signature /count/ rather than by declaration kind and is checked as
-- if it were a @:- function@ (@dev-docs\/BUGS.md@), so the generator
-- must never emit one. Making it unrepresentable is cheaper than
-- remembering not to.
data TwoOrMore a = TwoOrMore a a [a]
  deriving (Eq, Show)

twoOrMoreList :: TwoOrMore a -> [a]
twoOrMoreList (TwoOrMore x y zs) = x : y : zs

-- | A generated @:- class@: an overloaded predicate declared at two or
-- more ground instance types.
--
-- Every generated class has the shape @cls(tau) -> bool@. Unary on
-- purpose, and not only for brevity: a binary class needs /two/ values
-- at the argument type, and at a rigid type the second one has to come
-- from another variable at that same rigid type. A guard anchor is
-- required to be usable with itself out of scope, so a binary call at
-- a rigid anchor was excluded outright and the shape this whole
-- mechanism exists for landed in 1% of programs. Arity adds no
-- type-system coverage; reachability does.
--
-- The instance types are non-parametric so that each one can be
-- discriminated by a type predicate or a constructor pattern,
-- which is what makes the equations partial in exactly the declared
-- set (see 'YCHR.TypeSoundness.Render.renderClass').
data ClassFn = ClassFn
  { cfName :: Text,
    cfInstances :: TwoOrMore GTy,
    -- | Observation code for the catch-all equation, filled by
    -- 'YCHR.TypeSoundness.Instrument.instrument'. Reaching it means a
    -- bound-required operation was dispatched at a type with no
    -- declared instance, which is a violation.
    cfObsCode :: Int
  }
  deriving (Eq, Show)

classInstances :: ClassFn -> [GTy]
classInstances c = twoOrMoreList c.cfInstances

-- | One signature of a @requiring@ clause.
--
-- Always @cls(T, T) -> bool@ for one of the declaration's own type
-- parameters, matching the shape 'ClassFn' generates. Bounds always
-- name functions, never constraints.
data BoundSig = BoundSig {bsClass :: Text, bsTv :: TvName}
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
    -- | A @requiring@ clause. Each bound makes an overloaded operation
    -- available at the named parameter — at a rule head, as an
    -- /ambient/ signature the body may call through; at a use site, as
    -- an obligation the caller must discharge.
    sigBounds :: [BoundSig],
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

-- | A prelude /boundness/ predicate. Deliberately __not__ an evidence
-- form (§Non-forms): its success entails that a term holds a value,
-- which is a mode fact, not a typing one. It contributes nothing to
-- the skolem model and pins nothing.
--
-- What it does do is make the rest of the rule safe: a term the guard
-- has established is bound may be evaluated, which is the discipline
-- §No mode checking prescribes for a program that stores unbound
-- values.
data ModePred = PredNonvar | PredGround
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
  | -- | A call to a generated @:- class@. Renders exactly like
    -- 'ECall'; kept distinct because the /reason/ it type-checks
    -- differs — at a rigid argument it resolves only through an
    -- ambient signature contributed by a @requiring@ clause, which is
    -- the one route by which an overloaded operation reaches a rigid
    -- type at all.
    EClass Text [Expr]
  | -- | @integer(V)@ \/ @boolean(V)@ at a rigid-typed variable. The
    -- 'STy' is the variable's type /before/ the pin.
    EPred TypePred Text STy
  | -- | @nonvar(V)@ \/ @ground(V)@. Establishes that a term is bound,
    -- and nothing about its type.
    EModePred ModePred Text
  | -- | The prelude's @unifiable(any, any) -> bool@, used to gate a
    -- body @=@ so it cannot fail.
    --
    -- It is a /trailed trial unification/: it performs the
    -- unification, decides, and restores every cell it touched. So it
    -- decides exactly the question the body item will ask, and
    -- nothing between the guard and the body can change the answer.
    -- Without it a failed body unification is a hard runtime error,
    -- which the oracle would have to tolerate and could not tell from
    -- a real fault.
    EUnifiable Expr Expr
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
    -- | The variables that may hold no value yet /at head-match time/:
    -- those matched at a 'MayBeUnbound' position. This is what the
    -- head observation must be judged against, for the same reason it
    -- uses 'ruleSkHead' — the boundness guards have not run yet, and a
    -- candidate holding a free value there is exactly what they are
    -- there to reject.
    ruleTaintedHead :: Set Text,
    -- | The variables that may /still/ hold no value yet after the
    -- boundness guards: head variables no guard cleared, plus anything
    -- a structural @=@ bound from one.
    ruleTainted :: Set Text,
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

data Goal = Goal
  { tells :: NonEmpty (Sig, [Expr]),
    probes :: [Probe],
    -- | Query variables passed unbound into a 'MayBeUnbound' position,
    -- with the static type of the position they went into.
    --
    -- These come back in the goal's bindings, which makes them the
    -- cheapest possible check on the store-interleaving path: whatever
    -- the run eventually bound the variable to has to inhabit the type
    -- the declaration gave that position. A variable still free at the
    -- end is fine — that is the mode axis, not this one.
    unbounds :: [(Text, GTy)]
  }
  deriving (Eq, Show)

data Program = Program
  { adts :: [AdtDef],
    classes :: [ClassFn],
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

data ObsCheck
  = ExpectPos [PosCheck]
  | -- | This site must never be reached. Used for the catch-all
    -- equation of a generated class: arriving there means a
    -- bound-required operation was dispatched at a value whose type
    -- has no declared instance, so the bound the checker discharged
    -- did not hold.
    MustNotBeReached Text
  deriving (Eq, Show)

-- | What the observer can say about the value at one position.
data PosCheck
  = -- | The position has a ground static type, so the value must
    -- inhabit it — /if it is bound/. The 'Boundness' says whether a
    -- term holding no value yet is acceptable here.
    --
    -- This is the sharpened claim of §Soundness: every value that is
    -- bound is bound within its static type. A free variable is a
    -- statement about mode, and is a violation only where the
    -- position's contract said it would be ground.
    MustInhabit GTy Boundness
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
    --
    -- Carries its boundness for the same reason 'MustInhabit' does: at
    -- a 'MayBeUnbound' position there may be no value yet, and that is
    -- not a violation.
    MustBeBound Boundness
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

-- | Whether each of a rule's variables may hold no value yet.
varBoundness :: Rule -> Text -> Boundness
varBoundness r n
  | n `Set.member` r.ruleTainted = MayBeUnbound
  | otherwise = Ground

-- | As 'varBoundness', at head-match time.
varBoundnessAtHead :: Rule -> Text -> Boundness
varBoundnessAtHead r n
  | n `Set.member` r.ruleTaintedHead = MayBeUnbound
  | otherwise = Ground

-- | As 'ruleVars', but under the state matching alone establishes.
ruleVarsAtHead :: Rule -> [(Text, STy)]
ruleVarsAtHead r =
  nubBy (\a b -> fst a == fst b) (concatMap (headVars r.ruleSkHead) (ruleHeads r))
