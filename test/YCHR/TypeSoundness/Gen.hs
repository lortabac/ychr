{-# LANGUAGE OverloadedStrings #-}

-- | The generator: random well-typed programs in the core AST of
-- "YCHR.TypeSoundness.Types".
--
-- The polymorphism model in one sentence: __the generator picks every
-- instantiation, and the checker infers it__. At a /use/ site (a body
-- tell, a goal tell) the generator commits to a substitution for the
-- callee's type parameters and generates arguments at the substituted
-- types; at an /implementation/ site (a rule-head occurrence) it
-- allocates fresh skolems and generates only what is legal at a rigid
-- type. Nothing is inferred, so there is no constraint queue and no
-- residual solving here — only the structural unifier of
-- @Note [Skolems are one structural store]@, which merges skolems when
-- HNF would emit a @GuardEqual@.
module YCHR.TypeSoundness.Gen (Mode (..), genProgram, genProgramWith) where

import Control.Monad (foldM, replicateM)
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Hedgehog (Gen)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import YCHR.TypeSoundness.Preamble
import YCHR.TypeSoundness.Types

{- Note [Firing rates]

A program whose rules never fire runs none of the observations that
carry the property, so it costs a test iteration and observes nothing.
This note records why the goal- and guard-seeding below exists, and the
measurement that justified it.

The measurement predates the host observer. At the time, whether a rule
fired was a runtime fact nothing could see from Haskell, so it was
measured out of band with a canary: splice a body that always raises
(`Z = 1, Z = 2` — well-typed, and a failed body unification is a runtime
error) into the rules of interest, run, and count the programs that then
fail. A failure means those rules fired.

That method is retired. The observer's per-site hit counts make firing
directly assertable, so `coverRuntime` in the test module now carries
these rates as `cover` floors that CI enforces on every run, rather
than as a number someone has to remember to re-measure. Its haddock
records the cross-check: the observer reproduces the two program-level
rows below from inside the run to within a few points.

Measured across the size sweep, before and after the goal- and
guard-seeding described at `genGuard`, `patInstance` and
`genRuleInstance`. The program-level rows are over 200 programs in both
columns; the per-rule rows are over the 237 rules of 100 programs
before and the 436 rules of 200 programs after:

>                              before   after
> program fires some rule        42%     70%
> program vacuous               23%      8%
> individual rule fires          24%     41%
>   single-head propagation      44%     66%
>   two-head propagation         22%     34%
>   single-head simplification   23%     45%
>   two-head simplification      22%     35%
>   simpagation                  14%     37%
> rule with an aliased variable  12%     33%

"Vacuous" means the program neither fired a rule nor carried a goal
probe, so it observed nothing at all.

The three causes the fixes addressed were, in order of size: guards that
mentioned no variable and were therefore constant (64% of conjuncts,
about half of them constant-false; now 6%); head positions whose pattern
was only partly closed, which the goal-seed pool skipped entirely (38%
of structured positions); and joins and aliases, which needed two
independently drawn tells to coincide.

Anchoring a guard on a variable introduced a constant of its own, which
is worth knowing about before touching `genGuardOn`: the anchor was
drawn back out for the opposite operand, giving `V == V` and `V < V` in
15% of conjuncts. Deleting the anchor from the scope every non-anchor
operand is drawn from took that to 0.2%.

Remaining known dead weight, none of it addressed here: rules that
remove their own partners starve later rules on the same symbol, and
goal probes are closed expressions generated in an empty environment, so
they never observe a value the store or a rule body produced.
-}

-- ---------------------------------------------------------------------------
-- Generation context
-- ---------------------------------------------------------------------------

-- | Everything expression generation needs about where it is.
data Ctx = Ctx
  { ctxSk :: SkolemEnv,
    -- | In-scope variables at their implementation-site types.
    ctxScope :: Map Text STy,
    -- | The finite set of ground types this program's use sites draw
    -- instantiations from.
    ctxUniv :: [GTy],
    ctxAdts :: [AdtDef],
    ctxClasses :: [ClassFn],
    -- | Ambient signatures: a class name and the rigid type it is
    -- available at, contributed by a @requiring@ clause on a head
    -- occurrence's declaration.
    --
    -- This is the only route by which an overloaded operation reaches
    -- a rigid type. Without one, calling a class at a skolem is
    -- YCHR-60006 — which is precisely what makes bounded polymorphism
    -- worth generating: it is the mechanism that unblocks the
    -- downstream uses rigidity otherwise forbids.
    ctxAmbients :: [(Text, STy)],
    -- | Which rigid variables carry a bound, and from which class.
    -- Every pin is gated on this; see 'pinOk'.
    ctxBounded :: [(Skolem, Text)],
    -- | Variables that may hold no value yet, because they were bound
    -- by head matching at a 'MayBeUnbound' position.
    --
    -- They may appear only where a free variable is harmless: a
    -- structural @=@ operand, an ask-equality, a boundness or type
    -- predicate, or a bare argument at another 'MayBeUnbound'
    -- position. Everything else evaluates, and evaluation of a free
    -- variable is a runtime error the oracle would have to tolerate —
    -- see @Note [Which failures are benign now]@.
    ctxTainted :: Set Text
  }

-- | Which regime a program is generated for.
data Mode
  = -- | Every argument position is 'Ground': nothing unbound is ever
    -- stored, and the oracle can be at its strictest.
    Closed
  | -- | Some positions are 'MayBeUnbound', so a constraint may be
    -- stored holding a term that only a later unit binds. This is the
    -- store-interleaving regime §No mode checking describes.
    Open
  deriving (Eq, Show)

-- | The scope, with every type fully resolved, so comparisons do not
-- have to chase bindings.
scopeTys :: Ctx -> [(Text, STy)]
scopeTys ctx = [(n, stripSTy ctx.ctxSk t) | (n, t) <- Map.toList ctx.ctxScope]

-- | Variables usable in an /evaluated/ position: everything in scope
-- at that type except the possibly-unbound ones.
--
-- Evaluating a free variable is a runtime error, and one the oracle
-- must not have to tolerate — so the discipline is structural rather
-- than a classification after the fact.
varsAt :: Ctx -> STy -> [Expr]
varsAt ctx ty =
  [e | e@(EVar n _) <- varsAtAny ctx ty, not (n `Set.member` ctx.ctxTainted)]

-- | Variables usable where a free variable is harmless: a structural
-- @=@ operand, an ask-equality, a boundness or type predicate.
varsAtAny :: Ctx -> STy -> [Expr]
varsAtAny ctx ty =
  [EVar n t | (n, t) <- scopeTys ctx, t == stripSTy ctx.ctxSk ty]

-- | Can a value of this type be built here at all?
--
-- At a bare skolem the answer is \"only if a variable of that exact
-- rigid type is in scope\": there is no literal, no constructor and no
-- unbounded polymorphic function that produces one out of nothing.
-- Every caller picks its targets so that this holds, which is what
-- keeps the alternative lists in 'genExprAt' non-empty without a
-- filter.
inhabited :: Ctx -> STy -> Bool
inhabited ctx ty = case stripSTy ctx.ctxSk ty of
  SSk s -> not (null (varsAt ctx (SSk s)))
  SCon CInt [] -> True
  SCon CBool [] -> True
  SCon CList _ -> True
  SCon (CAdt def) args ->
    any (all (inhabited ctx) . ctorFieldTys def args) (NE.toList def.adtCtors)
  SCon _ _ -> False

-- | The rigid types this site actually holds a value of.
--
-- Restricting the rigid choices to types with an in-scope variable is
-- what makes every argument type built from them inhabited, by
-- induction over 'inhabited'. Restricted further to variables usable
-- in an /evaluated/ position, because that is what 'inhabited' will
-- look for: a rigid type whose only carrier may hold no value yet has
-- no inhabitant a use site could build, and offering it as an
-- instantiation target asks 'genExprAt' for something it cannot make.
rigidTargets :: Ctx -> [STy]
rigidTargets ctx =
  List.nub [t | EVar _ t <- allUntainted, isSk t]
  where
    allUntainted =
      concat [varsAt ctx t | (_, t) <- scopeTys ctx]
    isSk t = case t of
      SSk _ -> True
      _ -> False

-- | A type to instantiate a callee's parameter at, biased towards the
-- rigid ones.
--
-- Drawn uniformly, a rigid target is picked a few percent of the time:
-- the ground universe has dozens of members and a rule holds one or
-- two rigid types. That left "a body tell instantiates a parameter at
-- a rigid type" at 4%, which is the shape the polymorphic fragment
-- exists to exercise, so the draw is weighted instead.
pickTarget :: Ctx -> Gen STy
pickTarget ctx =
  Gen.frequency
    ( [(2, gToS <$> Gen.element ctx.ctxUniv)]
        ++ [(3, Gen.element rigid) | not (null rigid)]
    )
  where
    rigid = rigidTargets ctx

-- | The types a /bounded/ parameter may be instantiated at.
--
-- Only where the bound can actually be discharged: a ground instance
-- type of the named class, or a rigid type this site holds an ambient
-- signature for. Anything else is YCHR-60012 at the use site, and the
-- generator checks it here rather than letting the checker find out —
-- an unsatisfiable bound is a generator bug, not a program the
-- fragment contains.
--
-- The ground instances are always non-empty (a class has two or more),
-- so this can never come up empty.
boundedTargets :: Ctx -> [BoundSig] -> TvName -> [STy]
boundedTargets ctx bounds v = case [b | b <- bounds, b.bsTv == v] of
  [] -> instantiationTargets ctx
  bs ->
    [ t
    | t <- instantiationTargets ctx,
      all (dischargeable t) bs
    ]
  where
    dischargeable t b = case stripSTy ctx.ctxSk t of
      -- A rigid instance is covered only by an ambient at that very
      -- rigid variable: the bound travels with the occurrence that
      -- contributed it.
      SSk sk -> (b.bsClass, SSk sk) `elem` strippedAmbients ctx
      g -> case classNamed ctx b.bsClass of
        Nothing -> False
        Just c -> gToS `map` classInstances c & elem g
    (&) x f = f x

-- | Every ground and rigid type a parameter could be instantiated at
-- here, whether or not a bound allows it.
instantiationTargets :: Ctx -> [STy]
instantiationTargets ctx = map gToS ctx.ctxUniv ++ rigidTargets ctx

strippedAmbients :: Ctx -> [(Text, STy)]
strippedAmbients ctx =
  [(n, stripSTy ctx.ctxSk t) | (n, t) <- ctx.ctxAmbients]

classNamed :: Ctx -> Text -> Maybe ClassFn
classNamed ctx n = List.find (\c -> c.cfName == n) ctx.ctxClasses

-- | The classes callable at a type here: by ambient if it is rigid, by
-- declared instance if it is ground.
classesAt :: Ctx -> STy -> [Text]
classesAt ctx t = case stripSTy ctx.ctxSk t of
  SSk sk -> [n | (n, at) <- strippedAmbients ctx, at == SSk sk]
  g -> [c.cfName | c <- ctx.ctxClasses, g `elem` map gToS (classInstances c)]

-- | A body tell's instantiation for one parameter, respecting the
-- callee's bounds.
--
-- The rigid case is both rarer and more interesting: it is the only
-- shape in which a value crosses two declarations without either of
-- them learning which instance the store chose. Evidence pinning
-- competes for the same variables, so without the extra weight
-- ('pickFrom') the shape lands in a few percent of programs.
pickBounded :: Ctx -> Sig -> TvName -> Gen STy
pickBounded ctx s v = pickFrom (boundedTargets ctx s.sigBounds v) ctx

-- | Draw from a candidate set, leaning towards the rigid members.
pickFrom :: [STy] -> Ctx -> Gen STy
pickFrom cands ctx =
  Gen.frequency
    ( [(1, Gen.element ground) | not (null ground)]
        ++ [(4, Gen.element rigid) | not (null rigid)]
    )
  where
    (rigid, ground) = List.partition isRigid cands
    isRigid t = case stripSTy ctx.ctxSk t of
      SSk _ -> True
      _ -> False

gToS :: GTy -> STy
gToS (GTy c as) = SCon c (map gToS as)

gToD :: GTy -> DTy
gToD (GTy c as) = DCon c (map gToD as)

-- ---------------------------------------------------------------------------
-- Top level
-- ---------------------------------------------------------------------------

-- | Generate a well-typed core program. Each stage generates /from the
-- values/ of the earlier stages (types → signatures → rules → goal), so
-- hedgehog's integrated shrinking re-derives the later stages whenever
-- an earlier one shrinks and no reference is ever left dangling. All
-- cross-references are picked with 'Gen.element' over concrete
-- candidate lists — never by index into a list that shrinking can
-- shorten — and all names come from positional indices, so nothing
-- needs 'Gen.filter'.
genProgram :: Gen Program
genProgram = genProgramWith Closed

genProgramWith :: Mode -> Gen Program
genProgramWith mode = do
  defs <- genAdts
  let allAdts = fixedAdts ++ defs
      univ = groundUniverse allAdts
  cls <- genClasses univ
  sigList <- genSigs mode univ allAdts cls
  generated <- genRules univ allAdts cls sigList
  planted <- genPlantedBinder mode sigList
  let ruleList = generated ++ planted
  g <- genGoal univ allAdts cls sigList ruleList
  pure
    Program
      { adts = defs,
        classes = cls,
        sigs = sigList,
        rules = ruleList,
        goal = g,
        -- Filled by 'YCHR.TypeSoundness.Instrument.instrument', which
        -- runs after @forAllWith@ so that shrinking sees only what the
        -- generator drew.
        obs = mempty
      }

-- | The finite set of ground types in play, closed to depth 2.
--
-- Explicit and finite so that every instantiation can be drawn with
-- 'Gen.element'. Depth 2 is enough for the shapes that matter —
-- @list(t0(int))@, @t0(list(bool))@ — without the combinatorial blowup
-- a third level would bring.
groundUniverse :: [AdtDef] -> [GTy]
groundUniverse adts = List.nub (level0 ++ level1)
  where
    level0 = [gInt, gBool] ++ [gAdt d [] | d <- adts, null d.adtParams]
    level1 =
      [gList t | t <- level0]
        ++ [ gAdt d args
           | d <- adts,
             let n = length d.adtParams,
             n > 0,
             args <- combos n level0
           ]
    combos 0 _ = [[]]
    combos n xs = [x : rest | x <- xs, rest <- combos (n - 1) xs]

-- ---------------------------------------------------------------------------
-- Algebraic types
-- ---------------------------------------------------------------------------

-- | 0–2 algebraic types, each with 0–2 parameters. A definition may
-- only mention base types, @list@, the fixed types, /earlier/
-- generated types and its own parameters, so the definition graph is a
-- DAG, no depth budget is needed, and 'genClosedLeafAt' terminates.
--
-- Constructor names are globally unique (@k0@, @k1@, …) across all
-- generated types, and are positional so nothing has to be threaded
-- through the generator. They must also avoid punning on a prelude
-- function name, which the @k@ prefix guarantees.
--
-- A parameter no field mentions is dropped rather than kept: a phantom
-- parameter is legal but only creates instantiations nothing can tell
-- apart.
genAdts :: Gen [AdtDef]
genAdts = do
  n <- Gen.int (Range.constant 0 2)
  go n 0 0 []
  where
    go :: Int -> Int -> Int -> [AdtDef] -> Gen [AdtDef]
    go 0 _ _ acc = pure (reverse acc)
    go k tyIx ctorIx acc = do
      nParams <- Gen.frequency [(2, pure 0), (3, pure 1), (2, pure 2)]
      let params = take nParams [TvName "A", TvName "B"]
          earlier = fixedAdts ++ reverse acc
      (cs, ctorIx') <- genCtors earlier params ctorIx
      let used = [p | p <- params, any (mentionsTv p) (concatMap (.ctorFields) (NE.toList cs))]
          def =
            AdtDef
              { adtName = "t" <> tshow tyIx,
                adtParams = used,
                adtCtors = cs
              }
      go (k - 1) (tyIx + 1) ctorIx' (def : acc)

mentionsTv :: TvName -> DTy -> Bool
mentionsTv v t = case t of
  DVar w -> v == w
  DCon _ as -> any (mentionsTv v) as

genCtors :: [AdtDef] -> [TvName] -> Int -> Gen (NonEmpty CtorDef, Int)
genCtors earlier params start = do
  extra <- Gen.int (Range.constant 0 2)
  c0 <- genCtor earlier params start
  rest <- traverse (genCtor earlier params) [start + 1 .. start + extra]
  pure (c0 :| rest, start + extra + 1)

genCtor :: [AdtDef] -> [TvName] -> Int -> Gen CtorDef
genCtor earlier params ix = do
  fs <- Gen.list (Range.constant 0 2) (genFieldTy earlier params)
  pure CtorDef {ctorName = "k" <> tshow ix, ctorFields = fs}

-- | A constructor field's declared type: a base type, one of the
-- definition's own parameters, a list, or an earlier definition
-- applied at leaf types.
genFieldTy :: [AdtDef] -> [TvName] -> Gen DTy
genFieldTy earlier params =
  Gen.frequency
    ( [ (2, pure (DCon CInt [])),
        (2, pure (DCon CBool [])),
        (2, (\t -> DCon CList [t]) <$> genLeafTy earlier params)
      ]
        ++ [(4, DVar <$> Gen.element params) | not (null params)]
        ++ [(2, genAdtApp earlier params) | not (null earlier)]
    )

genLeafTy :: [AdtDef] -> [TvName] -> Gen DTy
genLeafTy earlier params =
  Gen.frequency
    ( [(2, pure (DCon CInt [])), (2, pure (DCon CBool []))]
        ++ [(3, DVar <$> Gen.element params) | not (null params)]
        ++ [ (2, pure (DCon (CAdt d) []))
           | d <- earlier,
             null d.adtParams
           ]
    )

genAdtApp :: [AdtDef] -> [TvName] -> Gen DTy
genAdtApp earlier params = do
  d <- Gen.element earlier
  DCon (CAdt d) <$> replicateM (length d.adtParams) (genLeafTy earlier params)

-- ---------------------------------------------------------------------------
-- Classes
-- ---------------------------------------------------------------------------

-- | 0–2 overloaded predicates, each declared at two or more ground
-- instance types.
--
-- The instance types are drawn from the /non-parametric/ ground types
-- only, so each can be told from the others by a type predicate or a
-- constructor pattern; that is what lets the equations be partial in
-- exactly the declared set, which is what makes the catch-all
-- observation mean something.
--
-- Generating a class rather than leaning on the prelude's @\<@ and
-- @\>@ is what makes the instance set a knob: floats are outside the
-- fragment, so a prelude comparison is effectively single-instance and
-- a bound over it would be discharged at exactly one type.
genClasses :: [GTy] -> Gen [ClassFn]
genClasses univ
  | length nonParam < 2 = pure []
  | otherwise = do
      -- Leaning towards having one: a program with no class can carry
      -- no bound, and the bounded shapes are the only ones in which an
      -- overloaded operation reaches a rigid type.
      n <- Gen.frequency [(2, pure 0), (4, pure 1), (2, pure 2)]
      traverse one [0 .. n - 1 :: Int]
  where
    nonParam = [t | t@(GTy c as) <- univ, null as, nonParametricCon c]
    one i = do
      -- Distinct: two signatures at the same type would be a duplicate
      -- declaration and a duplicate equation, and would make the
      -- overload set smaller than it looks.
      a <- Gen.element nonParam
      b <- Gen.element [t | t <- nonParam, t /= a]
      let rest = [t | t <- nonParam, t /= a, t /= b]
      extra <-
        if null rest
          then pure []
          else Gen.frequency [(3, pure []), (1, (: []) <$> Gen.element rest)]
      pure
        ClassFn
          { cfName = "cls" <> tshow i,
            cfInstances = TwoOrMore a b extra,
            cfObsCode = 0
          }

-- | The skolems an occurrence's @requiring@ clause constrains, with
-- the class that constrains them.
boundedSkolemsOf :: Sig -> [Skolem] -> [(Skolem, Text)]
boundedSkolemsOf sig sks =
  [ (sk, b.bsClass)
  | b <- sig.sigBounds,
    (tv, sk) <- zip sig.sigTvs sks,
    tv == b.bsTv
  ]

-- | May this skolem be pinned to this type?
--
-- A rule head /assumes/ its declaration's bound, so pinning the bounded
-- parameter to a type with no declared instance leaves a rule that no
-- store instance can satisfy — nothing can tell the constraint at that
-- type, because a tell is a use site and would have to discharge the
-- bound. The generator would then build a goal instance the query
-- type-check rejects (YCHR-60012). Every pin — literal, match, shared
-- variable, type predicate — goes through this.
pinOk :: [ClassFn] -> [(Skolem, Text)] -> Skolem -> STy -> Bool
pinOk cls bounded sk t =
  all ok [nm | (s', nm) <- bounded, s' == sk]
  where
    ok nm = case List.find (\c -> c.cfName == nm) cls of
      Nothing -> True
      Just c -> t `elem` map gToS (classInstances c)

nonParametricCon :: TyCon -> Bool
nonParametricCon c = case c of
  CInt -> True
  CBool -> True
  CList -> False
  CAdt d -> null d.adtParams

-- ---------------------------------------------------------------------------
-- Constraint signatures
-- ---------------------------------------------------------------------------

-- | 2–4 constraint declarations, arity 1–3. The stratum is the
-- declaration's position, which is what 'genRule' uses to keep body
-- tells strictly descending.
genSigs :: Mode -> [GTy] -> [AdtDef] -> [ClassFn] -> Gen (NonEmpty Sig)
genSigs mode univ adts cls = do
  extra <- Gen.int (Range.constant 1 3)
  s0 <- genSig mode univ adts cls 0
  rest <- traverse (genSig mode univ adts cls) [1 .. extra]
  pure (s0 :| rest)

-- | One declaration, monomorphic or with 1–2 parameters.
--
-- Unused parameters are dropped for the same reason phantom type
-- parameters are: they would allocate a rigid variable no argument
-- position mentions, so nothing could observe which instance the store
-- chose.
genSig :: Mode -> [GTy] -> [AdtDef] -> [ClassFn] -> Int -> Gen Sig
genSig mode univ adts cls ix = do
  nTvs <- Gen.frequency [(3, pure 0), (3, pure 1), (2, pure 2)]
  let tvs = take nTvs [TvName "A", TvName "B"]
  a0 <- genArgDTy univ adts tvs
  more <- Gen.list (Range.constant 0 2) (genArgDTy univ adts tvs)
  let allArgs = a0 : more
      used = [v | v <- tvs, any (mentionsTv v) allArgs]
  -- The bound goes on a parameter some argument mentions /bare/.
  --
  -- A bound on a parameter that only ever appears nested — @list(A)@,
  -- @t0(A)@ — is still legal, but no head can bind a variable at the
  -- bare rigid type, so the ambient signature it contributes has
  -- nothing to be called on. That left "an overloaded call at a rigid
  -- type", the shape this whole mechanism exists for, in 1% of
  -- programs.
  let bareTvs = [v | v <- used, DVar v `elem` allArgs]
  bounds <-
    if null bareTvs || null cls
      then pure []
      else
        Gen.frequency
          [ (2, pure []),
            ( 3,
              do
                c <- Gen.element cls
                v <- Gen.element bareTvs
                pure [BoundSig {bsClass = c.cfName, bsTv = v}]
            )
          ]
  -- In the open regime some positions are willing to hold a term that
  -- is not bound yet. Something has to be, or nothing can ever be
  -- stored unbound and the store-interleaving shapes are unreachable.
  bnds <-
    traverse
      (const (if mode == Open then genBoundness else pure Ground))
      (a0 : more)
  pure
    Sig
      { sigName = "c" <> tshow ix,
        sigTvs = used,
        sigArgs = case zipWith mkArg (a0 : more) bnds of
          (x : xs) -> x :| xs
          [] -> mkArg a0 Ground :| [],
        sigBounds = bounds,
        stratum = ix
      }
  where
    genBoundness = Gen.frequency [(2, pure Ground), (1, pure MayBeUnbound)]
    mkArg t b = ArgSpec {argTy = t, argErased = False, argBound = b}

genArgDTy :: [GTy] -> [AdtDef] -> [TvName] -> Gen DTy
genArgDTy univ adts tvs =
  Gen.frequency
    ( [(4, gToD <$> Gen.element univ)]
        ++ [(4, DVar <$> Gen.element tvs) | not (null tvs)]
        ++ [ (2, (\v -> DCon CList [DVar v]) <$> Gen.element tvs)
           | not (null tvs)
           ]
        ++ [ (2, genParamAdtApp parametric tvs)
           | not (null tvs),
             not (null parametric)
           ]
    )
  where
    parametric = [d | d <- adts, not (null d.adtParams)]

-- | A parametric type applied with at least one of the declaration's
-- own parameters, so the argument's type genuinely varies with the
-- instantiation rather than only mentioning it at the top level.
genParamAdtApp :: [AdtDef] -> [TvName] -> Gen DTy
genParamAdtApp parametric tvs = do
  d <- Gen.element parametric
  args <- replicateM (length d.adtParams) (Gen.element (map DVar tvs))
  pure (DCon (CAdt d) args)

-- ---------------------------------------------------------------------------
-- Rules
-- ---------------------------------------------------------------------------

genRules :: [GTy] -> [AdtDef] -> [ClassFn] -> NonEmpty Sig -> Gen [Rule]
genRules univ adts cls sigList = do
  n <- Gen.int (Range.linear 1 6)
  traverse (genRule univ adts cls sigList) [0 .. n - 1]

-- | Which of the three CHR rule shapes to generate.
data RuleKind = KSimplify | KPropagate | KSimpagate

genRule :: [GTy] -> [AdtDef] -> [ClassFn] -> NonEmpty Sig -> Int -> Gen Rule
genRule univ adts cls sigList ix = do
  kind <- Gen.element [KSimplify, KPropagate, KSimpagate]
  nHeads <- case kind of
    KSimpagate -> pure 2
    _ -> Gen.int (Range.constant 1 2)
  (hs, sk0) <- genHeads nHeads
  (aliased, skHead) <- maybeAlias cls sk0 hs
  let rh = mkRuleHead kind aliased
      heads_ = ruleHeadList rh
      -- First occurrence wins for a repeated (aliased) variable: HNF
      -- renames the later occurrences away and keeps the first, so
      -- the checker types the surviving name at its first position.
      -- The occurrences' types need not resolve equal any more — a
      -- pair meeting inside a shared constructor teaches the checker
      -- nothing — so which one the scope records is load-bearing.
      scope0 =
        Map.fromListWith
          (\_ old -> old)
          (concatMap (headVars skHead) (NE.toList heads_))
      -- Every head occurrence of a bounded declaration contributes its
      -- bound as an ambient signature at that occurrence's own rigid
      -- variable. The rule head is an implementation site, so it
      -- /assumes/ the bound; a body tell of the same constraint is a
      -- use site and must discharge it.
      ambients =
        [ (b.bsClass, substD (occSub h) (DVar b.bsTv))
        | h <- NE.toList heads_,
          b <- h.headSig.sigBounds
        ]
      occSub h =
        Map.fromList (zip h.headSig.sigTvs (map SSk h.headSkolems))
      bounded =
        concat
          [ boundedSkolemsOf h.headSig h.headSkolems
          | h <- NE.toList heads_
          ]
      -- A head variable is tainted when the position it was matched at
      -- is willing to hold an unbound term — including one nested
      -- inside such a position, since matching a structured pattern
      -- against a partly instantiated value binds free variables just
      -- as readily.
      tainted =
        Set.fromList
          [ n
          | h <- NE.toList heads_,
            (spec, ty, p) <-
              zip3
                (NE.toList h.headSig.sigArgs)
                (NE.toList (headArgTys h))
                (NE.toList h.pats),
            spec.argBound == MayBeUnbound,
            (n, _) <- patVars skHead ty p
          ]
      ctxHead =
        Ctx
          { ctxSk = skHead,
            ctxScope = scope0,
            ctxUniv = univ,
            ctxAdts = adts,
            ctxClasses = cls,
            ctxAmbients = ambients,
            ctxBounded = bounded,
            ctxTainted = tainted
          }
  -- Boundness first, then evidence: both establish something used to
  -- their right and nothing to their left, and a variable has to be
  -- known bound before a type predicate on it can succeed.
  (modeGs, ctxM) <- genModeGuards ctxHead
  (ev, ctx0) <- genEvidenceGuards ctxM
  gs <- Gen.list (Range.constant 0 2) (genGuard ctx0)
  nBinds <- Gen.int (Range.constant 0 2)
  (ctx1, binds) <- foldM genBind (ctx0, []) [0 .. nBinds - 1]
  (gateGs, gateItems, ctx2) <- genGatedBind ctx1
  tellItems <-
    genTells ctx2 sigList (minimum (fmap (.headSig.stratum) heads_))
  pure
    Rule
      { ruleName = "r" <> tshow ix,
        ruleHead = rh,
        ruleEvidence = modeGs ++ ev,
        guards = gs ++ gateGs,
        body = binds ++ gateItems ++ tellItems,
        ruleTaintedHead = tainted,
        -- What is *still* possibly-unbound after the mode guards ran.
        ruleTainted = taintedAll ctx2 ctx2.ctxTainted binds,
        ruleSkHead = skHead,
        ruleSk = ctx1.ctxSk
      }
  where
    genHeads n =
      foldM
        ( \(acc, sk) hIx -> do
            (h, sk') <- genHead adts cls sigList hIx sk
            pure (acc ++ [h], sk')
        )
        ([], emptySkolems)
        [0 .. n - 1]
        >>= \(hsList, sk) -> case hsList of
          (h : rest) -> pure (h :| rest, sk)
          [] -> error "genHeads: no heads"

-- | Every variable the rule may see holding no value yet: the head
-- variables matched at a 'MayBeUnbound' position, plus any body
-- binding that took its value structurally from one.
--
-- A @W is E@ cannot: an evaluated expression never mentions a
-- possibly-unbound variable (see 'varsAt'). A @W = T@ can, because @=@
-- is structural and passing an unbound term on is how the open regime
-- moves one around.
taintedAll :: Ctx -> Set Text -> [BodyItem] -> Set Text
taintedAll ctx seed items = foldl step seed items
  where
    step acc it = case it of
      BUnify w _ st | mentionsTainted acc st -> Set.insert w acc
      _ -> acc
    mentionsTainted acc st = case st of
      SVar n _ -> n `Set.member` acc || n `Set.member` ctx.ctxTainted
      SCons a b -> mentionsTainted acc a || mentionsTainted acc b
      SCtor _ ts -> any (mentionsTainted acc) ts
      _ -> False

-- | One head occurrence.
--
-- It allocates the declaration's own rigid variables /fresh/ — \"each
-- rule-head occurrence allocates its own rigid variables, even between
-- two occurrences of the same constraint\" (§Rigid and flexible type
-- variables) — because the store is a heterogeneous multiset and
-- nothing makes two occurrences agree unless matching does.
genHead ::
  [AdtDef] ->
  [ClassFn] ->
  NonEmpty Sig ->
  Int ->
  SkolemEnv ->
  Gen (HeadC, SkolemEnv)
genHead adts cls sigList hIx sk = do
  sig <- Gen.element (NE.toList sigList)
  let (sks, sk0) = freshSkolems (length sig.sigTvs) sk
      bnd = boundedSkolemsOf sig sks
      sub = Map.fromList (zip sig.sigTvs (map SSk sks))
      t0 :| ts = fmap (substD sub) (sigArgDTys sig)
  (p0, sk1) <- genPat adts cls bnd sk0 2 [0, hIx] t0
  (rest, skN) <-
    foldM
      ( \(acc, skAcc) (i, t) -> do
          (p, skAcc') <- genPat adts cls bnd skAcc 2 [i, hIx] t
          pure (acc ++ [p], skAcc')
      )
      ([], sk1)
      (zip [1 :: Int ..] ts)
  pure (HeadC {headSig = sig, headSkolems = sks, pats = p0 :| rest}, skN)

-- | A head pattern for an implementation-site argument type.
--
-- Variable names are derived from the position path (head index,
-- argument index, then the path down into the pattern), so they are
-- unique by construction and no fresh-name counter has to be threaded
-- through the generator.
--
-- At a target that is already a constructor application the structured
-- alternatives are ordinary: matching @[H | R]@ at @list(T)@ reads the
-- field types off an instantiation the declaration already fixed, and
-- pins nothing.
--
-- At a /bare rigid/ target they are evidence. A literal pins the
-- skolem to that literal's type; a constructor or list pattern pins it
-- to that type constructor applied at __fresh rigid__ parameters. The
-- freshness and the rigidity are both load-bearing: @typecheck_match_beta_rigid@
-- pins that the parameters a @GuardMatch@ introduces are rigid, not
-- flexible, so a body may not then treat the field as a concrete type.
-- Getting that wrong here is the drift this stage exists to catch, so
-- the generator does exactly what the spec says and lets the checker
-- disagree if it will.
--
-- Threads the skolem state because a pin at one argument position is
-- visible to the next: @c(X, 5)@ at @c(T, T)@ types @X@ as @int@.
genPat ::
  [AdtDef] ->
  [ClassFn] ->
  [(Skolem, Text)] ->
  SkolemEnv ->
  Int ->
  [Int] ->
  STy ->
  Gen (Pat, SkolemEnv)
genPat adts cls bnd sk d path ty = Gen.frequency (common ++ specific)
  where
    common =
      [ (6, pure (PVar (varName path) ty, sk)),
        (1, pure (PWild, sk))
      ]
    specific = case resolveSTy sk ty of
      SSk s -> [(3, genPin s) | d > 0, not (null (pinChoices s))]
      SCon CInt [] -> [(2, lit (PLit . LInt <$> Gen.integral (Range.linear 0 20)))]
      SCon CBool [] -> [(2, lit (PLit . LBool <$> Gen.bool))]
      SCon CList [el] ->
        (2, pure (PNil, sk))
          : [(3, consPat sk el ty) | d > 0]
      SCon (CAdt def) args -> [(3, genCtorPat sk def args) | d > 0]
      SCon _ _ -> []
    lit g = (,sk) <$> g
    consPat skIn el rest = do
      (h, sk1) <- genPat adts cls bnd skIn (d - 1) (0 : path) el
      (t, sk2) <- genPat adts cls bnd sk1 (d - 1) (1 : path) rest
      pure (PCons h t, sk2)
    genCtorPat skIn def args = do
      c <- Gen.element (NE.toList def.adtCtors)
      (ps, skN) <-
        foldM
          ( \(acc, skAcc) (i, t) -> do
              (p, skAcc') <- genPat adts cls bnd skAcc (d - 1) (i : path) t
              pure (acc ++ [p], skAcc')
          )
          ([], skIn)
          (zip [0 :: Int ..] (ctorFieldTys def args c))
      pure (PCtor c.ctorName ps, skN)
    -- The evidence cases: a pattern at a bare rigid scrutinee.
    genPin s = Gen.choice (pinChoices s)
    -- Only pins the declaration's own bound can live with; see 'pinOk'.
    pinChoices s =
      [ pinTo PinLit s (SCon CInt []) (PLit . LInt <$> Gen.integral (Range.linear 0 20))
      | allowed s (SCon CInt [])
      ]
        ++ [ pinTo PinLit s (SCon CBool []) (PLit . LBool <$> Gen.bool)
           | allowed s (SCon CBool [])
           ]
        ++ [pinList s | allowed s (SCon CList [SSk (Skolem (-1))])]
        ++ [ pinCtor s def
           | def <- adtsInScope,
             allowed s (SCon (CAdt def) (map (const (SSk (Skolem (-1)))) def.adtParams))
           ]
    -- The placeholder skolem above only stands in for "some
    -- application of this constructor"; a class instance is
    -- non-parametric, so an application with arguments never matches
    -- one and the check is decided by the constructor alone.
    allowed = pinOk cls bnd
    pinTo src s t g = do
      p <- g
      pure (p, pinOrKeep src s t sk)
    pinList s = do
      let (betas, sk1) = freshSkolems 1 sk
          beta = case betas of
            (b : _) -> b
            [] -> error "genPat: freshSkolems 1 returned none"
          sk2 = pinOrKeep PinMatch s (SCon CList [SSk beta]) sk1
      Gen.choice
        [ pure (PNil, sk2),
          do
            (h, sk3) <- genPat adts cls bnd sk2 (d - 1) (0 : path) (SSk beta)
            (t, sk4) <- genPat adts cls bnd sk3 (d - 1) (1 : path) (SCon CList [SSk beta])
            pure (PCons h t, sk4)
        ]
    pinCtor s def = do
      let (betas, sk1) = freshSkolems (length def.adtParams) sk
          args = map SSk betas
          sk2 = pinOrKeep PinMatch s (SCon (CAdt def) args) sk1
      c <- Gen.element (NE.toList def.adtCtors)
      (ps, skN) <-
        foldM
          ( \(acc, skAcc) (i, t) -> do
              (p, skAcc') <- genPat adts cls bnd skAcc (d - 1) (i : path) t
              pure (acc ++ [p], skAcc')
          )
          ([], sk2)
          (zip [0 :: Int ..] (ctorFieldTys def args c))
      pure (PCtor c.ctorName ps, skN)
    -- A pin can only fail its occurs check, which cannot happen here:
    -- the target is built from skolems allocated a moment ago.
    pinOrKeep src s t env = fromMaybe env (pinSkolem src s t env)
    adtsInScope = adts

varName :: [Int] -> Text
varName path = "V" <> T.intercalate "_" (map tshow (reverse path))

-- | With some probability, rename one pattern variable to another —
-- possibly in a different head. The repeated variable becomes an
-- implicit equality once the compiler puts the rule in head normal
-- form, which puts the rule through the checker's @GuardEqual@ path.
--
-- When both positions are rigid this is the skolem merge that makes
-- multi-head idioms over a polymorphic constraint check at all —
-- transitivity of a @leq(T, T)@ and its like. Performing the rename
-- therefore performs the merge, so the rest of the rule is generated
-- under the same identification the checker will make.
--
-- A pair that identifies a rigid position with a concretely typed one
-- /pins/ the skolem, and is recorded as such: the checker reaches it
-- through the same @GuardEqual@, but the fact it contributes is
-- evidence rather than plain unification. What the pin may say is
-- bounded by what value equality proves (§What evidence does): a
-- non-parametric type pins exactly; a parametric application pins
-- only its constructor, at fresh skolems; and a pair meeting inside
-- a shared constructor teaches the checker nothing — the store
-- instance is then forced to agree ('skForce') without the static
-- model learning it.
maybeAlias ::
  [ClassFn] ->
  SkolemEnv ->
  NonEmpty HeadC ->
  Gen (NonEmpty HeadC, SkolemEnv)
maybeAlias cls sk hs
  | null pairs = pure (hs, sk)
  | otherwise = do
      -- Aliasing is worth more when a rigid merge is on the table, so
      -- the coin is weighted by whether one is: that is the case the
      -- checker's GuardEqual skolem merge exists for, and it is rarer
      -- than plain same-concrete-type aliasing.
      doIt <-
        Gen.frequency
          ( if null merging
              then [(2, pure True), (3, pure False)]
              else [(3, pure True), (1, pure False)]
          )
      if not doIt
        then pure (hs, sk)
        else do
          (keep, drop_, sk') <-
            Gen.frequency
              ( [(3, Gen.element merging) | not (null merging)]
                  ++ [(1, Gen.element plain) | not (null plain)]
              )
          pure (fmap (renameHead drop_ keep) hs, notePins sk sk')
  where
    vs = concatMap (headVars sk) (NE.toList hs)
    -- 'eqUnifySTy' is the checker's own @GuardEqual@ discipline —
    -- skolem merges and pins go into the static model, parameter
    -- identifications into the runtime forcings — so a pair it
    -- accepts is a pair the checker accepts /and/ the instance
    -- generator can arrange a firing for. A pair it refuses (an
    -- outermost-constructor mismatch, a forcing conflict) is simply
    -- not offered.
    pairs =
      [ (a, b, sk')
      | (a, ta) <- vs,
        (b, tb) <- vs,
        a < b,
        Just sk' <- [eqUnifySTy ta tb sk],
        -- The merge may pin a bounded parameter; the same gate as
        -- every other pin applies (see 'pinOk').
        pinsRespectBounds sk'
      ]
    bounded =
      concat
        [ boundedSkolemsOf h.headSig h.headSkolems
        | h <- NE.toList hs
        ]
    -- Both maps, not just 'skBind'. A parameter-depth identification
    -- teaches the checker nothing but still records what the store must
    -- satisfy for the alias to fire, and 'genRuleInstance' grounds the
    -- head instance under that forcing. Forcing a bounded parameter to
    -- a type with no instance therefore builds a goal tell the query
    -- type-check rejects (YCHR-60012), even though the rule itself
    -- checks clean.
    pinsRespectBounds after =
      all
        (\(s', t) -> pinOk cls bounded s' (stripSTy (runtimeView after) t))
        ( Map.toList (Map.difference after.skBind sk.skBind)
            ++ Map.toList (Map.difference after.skForce sk.skForce)
        )
    -- Pairs that genuinely constrain a rigid variable — a merge or
    -- pin the checker performs, or a parameter forcing it
    -- deliberately does not — as against two positions that already
    -- had the same concrete type. Drawn uniformly the latter swamp
    -- the former — there are many more concrete positions — and the
    -- skolem merge, which is what makes multi-head idioms over a
    -- polymorphic constraint check at all, showed up in 4% of
    -- programs. Hence the split.
    (merging, plain) =
      List.partition
        ( \(_, _, sk') ->
            not
              ( Map.null (Map.difference sk'.skBind sk.skBind)
                  && Map.null (Map.difference sk'.skForce sk.skForce)
              )
        )
        pairs

-- | Record, for coverage, which of the bindings a merge added pinned a
-- skolem to a concrete type rather than aliasing it to another skolem.
notePins :: SkolemEnv -> SkolemEnv -> SkolemEnv
notePins before after =
  after
    { skPinned =
        Map.union
          after.skPinned
          (Map.map (const PinMergeConcrete) concreteBindings)
    }
  where
    concreteBindings =
      Map.filter (not . isSk) (Map.difference after.skBind before.skBind)
    isSk t = case t of
      SSk _ -> True
      _ -> False

renameHead :: Text -> Text -> HeadC -> HeadC
renameHead from to h = h {pats = fmap go h.pats}
  where
    go p = case p of
      PVar n t | n == from -> PVar to t
      PCons a b -> PCons (go a) (go b)
      PCtor c ps -> PCtor c (map go ps)
      _ -> p

-- | Fit a generated head list to one of the three rule shapes. A
-- simpagation needs two heads; 'genRule' always asks for two when it
-- picks that shape, and a one-head list degrades to a simplification
-- rather than being fabricated into shape.
mkRuleHead :: RuleKind -> NonEmpty HeadC -> RuleHead
mkRuleHead kind hs = case (kind, hs) of
  (KPropagate, _) -> HPropagate hs
  (KSimpagate, k :| (r : rest)) -> HSimpagate (k :| []) (r :| rest)
  _ -> HSimplify hs

-- ---------------------------------------------------------------------------
-- Guards
-- ---------------------------------------------------------------------------

-- | 0–2 type-predicate guards, each pinning one still-unpinned rigid
-- variable that some in-scope variable is typed at exactly.
--
-- Only @integer@ and @boolean@: @float@ and @string@ are outside the
-- fragment, and @atom@, @var@, @nonvar@ and @ground@ are explicitly
-- /not/ evidence forms (§Non-forms) — the first because nullary
-- constructors inhabit many types, the others because their success
-- entails a boundness fact rather than a typing one.
--
-- Pinning here is what unlocks concrete and overloaded operations at
-- that variable for the guards to the right and the whole body, so
-- generating these /before/ the ordinary guards is load-bearing rather
-- than cosmetic: evidence is positional.
--
-- The candidates are bare unpinned skolems only. A predicate at an
-- already-concrete variable is either redundant (if it agrees) or a
-- contradiction (if it does not), and a contradiction makes the rule
-- dead code — YCHR-20104, which the oracle treats as a failure.
genEvidenceGuards :: Ctx -> Gen ([Expr], Ctx)
genEvidenceGuards ctx0
  | null (candidates ctx0) = pure ([], ctx0)
  | otherwise = do
      -- Weighted towards none. Every pin turns a rigid variable
      -- concrete, so evidence competes for exactly the variables a body
      -- tell would otherwise instantiate a callee's parameter at; at
      -- 2:3:1 that shape fell from 10% of programs to 2%.
      n <- Gen.frequency [(4, pure 0), (3, pure 1), (1, pure 2)]
      go n ([], ctx0)
  where
    go :: Int -> ([Expr], Ctx) -> Gen ([Expr], Ctx)
    go 0 acc = pure acc
    go k (gs, ctx) = case candidates ctx of
      [] -> pure (gs, ctx)
      cs -> do
        (n, s) <- Gen.element cs
        (fn, t, src) <-
          Gen.element
            [ alt
            | alt@(_, t, _) <-
                [ (PredInteger, SCon CInt [], PinTypePred),
                  (PredBoolean, SCon CBool [], PinTypePred)
                ],
              t `elem` predTys,
              pinOk ctx.ctxClasses ctx.ctxBounded s t
            ]
        let sk' = fromMaybe ctx.ctxSk (pinSkolem src s t ctx.ctxSk)
        go (k - 1) (gs ++ [EPred fn n (SSk s)], ctx {ctxSk = sk'})
    candidates ctx =
      [ (n, s)
      | (n, t) <- scopeTys ctx,
        SSk s <- [t],
        not (Map.member s ctx.ctxSk.skPinned),
        -- A force-constrained skolem's instance is already fixed by
        -- an alias; a predicate pin could contradict it, leaving a
        -- guard the arranged store values never pass.
        not (Map.member s ctx.ctxSk.skForce),
        -- And a bounded parameter can only be pinned where its class
        -- has an instance (see 'pinOk'). With neither predicate
        -- allowed there is nothing to draw, so the variable is not a
        -- candidate at all — this list and the draw below must agree.
        any (pinOk ctx.ctxClasses ctx.ctxBounded s) predTys
      ]
    predTys = [SCon CInt [], SCon CBool []]

-- | 0–2 boundness guards, each on a variable that may hold no value
-- yet, removing it from the taint for everything to their right.
--
-- This is the discipline @docs\/reference\/type-system.md@
-- §No mode checking prescribes, and the only reason the open regime
-- can do anything with a stored-unbound value beyond passing it on:
-- @nonvar(X)@ fails on a free variable, so the rule simply does not
-- fire until something binds it, and reactivation retries it then.
--
-- Deliberately __not__ evidence: its success entails that a term holds
-- a value, not what type that value has, so it pins no skolem and the
-- type model is untouched (§Non-forms).
genModeGuards :: Ctx -> Gen ([Expr], Ctx)
genModeGuards ctx0
  | Set.null ctx0.ctxTainted = pure ([], ctx0)
  | otherwise = do
      -- Weighted towards clearing at most one. A boundness guard stops
      -- the rule firing until something binds the value, so clearing
      -- every tainted variable in a rule would make the rules that
      -- could do the binding unable to run.
      n <- Gen.frequency [(2, pure 0), (3, pure 1), (1, pure 2)]
      go n ([], ctx0)
  where
    go :: Int -> ([Expr], Ctx) -> Gen ([Expr], Ctx)
    go 0 acc = pure acc
    go k (gs, ctx) = case Set.toList ctx.ctxTainted of
      [] -> pure (gs, ctx)
      cs -> do
        v <- Gen.element cs
        pr <- Gen.element [PredNonvar, PredGround]
        go
          (k - 1)
          ( gs ++ [EModePred pr v],
            ctx {ctxTainted = Set.delete v ctx.ctxTainted}
          )

-- | A rule guard, anchored on a head variable whenever one is in scope.
--
-- A conjunct that mentions no variable is a compile-time constant, and a
-- constant-false one makes the rule unconditionally dead — which costs a
-- whole test iteration, since a rule that never fires runs none of the
-- observations that carry the property. Generating the guard freely gave
-- a closed conjunct 64% of the time (guards like @is_zero(3)@), because
-- the leaf generator can only reach for a variable at the type it is
-- asked for and the head rarely binds one at every type a boolean test
-- descends through. So the guard is built /around/ a variable instead.
--
-- The anchor is drawn from the variables that some predicate can /say
-- something about/ when there are any. A generated algebraic type has no
-- predicate over it, so its only test is an equality against a value
-- drawn independently — which is false almost every time, and so just
-- relocates the dead-rule problem from constant-false to
-- improbably-true. A rigid-typed variable is in the same position, with
-- the extra restriction that the opposite operand has to come from
-- somewhere: only another variable at that same rigid type will do.
genGuard :: Ctx -> Gen Expr
genGuard ctx
  | null anchors = genNonVarAt ctx 2 (gToS gBool)
  | otherwise =
      Gen.frequency
        ( [(4, Gen.element ambientAnchors) | not (null ambientAnchors)]
            ++ [(3, Gen.element testable) | not (null testable)]
            ++ [(1, Gen.element anchors)]
        )
        >>= uncurry (genGuardOn ctx)
  where
    anchors =
      [ b
      | b@(n, t) <- scopeTys ctx,
        not (n `Set.member` ctx.ctxTainted),
        anchorable n t
      ]
    testable = [b | b@(_, t) <- anchors, hasPredicate t]
    -- Anchors whose type is still rigid and whose bound puts an
    -- overloaded predicate in scope. Preferred over the merely
    -- testable ones: this is the only place an overloaded operation
    -- can reach a rigid type, and left to compete on equal terms with
    -- every concrete anchor it lands in about 1% of programs.
    ambientAnchors =
      [ b
      | b@(_, t) <- anchors,
        SSk _ <- [t],
        not (null (classesAt ctx t))
      ]
    -- Every alternative draws the opposite operand with the anchor out
    -- of scope, so an anchor is only usable when its own type is still
    -- inhabited without it. Checking only the bare-rigid case is not
    -- enough: @t0(T)@ and @list(T)@ are just as uninhabited once the
    -- one variable carrying @T@ is gone.
    -- Usable /without/ a second value of its own type when an
    -- overloaded predicate applies to it directly: every other test
    -- needs an opposite operand, a unary class call does not.
    anchorable n t =
      inhabited (withoutVar ctx n) t || not (null (classesAt ctx t))
    -- A type some predicate can say something about. A generated
    -- algebraic type has none, so its only test is an equality against
    -- an independently drawn value — false almost every time, which
    -- relocates the dead-rule problem rather than fixing it.
    --
    -- A /rigid/ type counts when an ambient signature covers it: the
    -- bound puts an overloaded predicate in scope at exactly that
    -- variable, which is the one thing that can be said about a rigid
    -- value beyond equality. Leaving it out of this list is what kept
    -- \"an overloaded call at a rigid type\" — the shape bounded
    -- polymorphism exists for — at 1% of programs.
    hasPredicate t =
      t
        `elem` [ gToS gInt,
                 gToS gBool,
                 gToS (gList gInt),
                 gToS (gAdt colorDef []),
                 gToS (gAdt shapeDef [])
               ]
        || not (null (classesAt ctx t))

withoutVar :: Ctx -> Text -> Ctx
withoutVar ctx n = ctx {ctxScope = Map.delete n ctx.ctxScope}

-- | A boolean test mentioning the given variable.
--
-- Every alternative puts the anchor on one side and draws the other
-- side with the anchor /out of scope/. With it in scope the leaf
-- generator picks it back out often enough to matter: @V == V@
-- accounted for most of the variable-to-variable equalities, and
-- @V < V@ and friends for a further 5% of conjuncts, two fifths of
-- those constant-false. Nothing is lost by the deletion, since the
-- anchor already occupies one operand.
genGuardOn :: Ctx -> Text -> STy -> Gen Expr
genGuardOn ctx n t =
  Gen.frequency
    ( [(1, g) | g <- eqTests]
        ++ [(4, g) | g <- classTests]
        ++ [(2, g) | g <- specific]
    )
  where
    v = EVar n t
    inner = withoutVar ctx n
    sub ty = genExprAt inner 1 ty
    -- Only when the opposite operand can be built with the anchor out
    -- of scope. An anchor admitted purely because a unary class call
    -- applies to it has no second value of its own type, so equality
    -- is not available there — 'anchorable' lets it through on the
    -- strength of 'classTests' alone.
    eqTests
      | inhabited inner t = [EEq t v <$> sub t, EEq t <$> sub t <*> pure v]
      | otherwise = []
    -- An overloaded predicate on the anchor. At a rigid anchor this is
    -- the only test other than equality, and it exists only because a
    -- @requiring@ clause put the signature in scope — so it outweighs
    -- equality rather than tying with it.
    classTests = [pure (EClass cn [v]) | cn <- classesAt ctx t]
    intTests e =
      [ ECmp <$> genCmp <*> pure e <*> sub (gToS gInt),
        ECmp <$> genCmp <*> sub (gToS gInt) <*> pure e
      ]
    genCmp = Gen.element [CLt, CGt, CGe, CLe]
    specific
      | t == gToS gInt =
          intTests v
            ++ [ pure (ECall FnIsZero [v]),
                 (\e -> ECall FnLt [v, e]) <$> sub (gToS gInt),
                 (\e -> ECall FnLte [e, v]) <$> sub (gToS gInt),
                 (\e -> ECall FnSameInt [v, e]) <$> sub (gToS gInt)
               ]
      | t == gToS gBool = [pure v, pure (ENot v)]
      | t == gToS (gList gInt) =
          pure (ECall FnIsNil [v]) : intTests (ECall FnLen [v])
      | t == gToS (gAdt colorDef []) = [pure (ECall FnIsRed [v])]
      | t == gToS (gAdt shapeDef []) = intTests (ECall FnArea [v])
      | otherwise = []

-- ---------------------------------------------------------------------------
-- Body
-- ---------------------------------------------------------------------------

-- | One body binding: @W is E@ or @W = T@. Both bind a /fresh/
-- variable, which is what keeps @=@ unfailable and the store ground.
genBind :: (Ctx, [BodyItem]) -> Int -> Gen (Ctx, [BodyItem])
genBind (ctx, acc) i = do
  t <- pickTarget ctx
  let w = "W" <> tshow i
  item <-
    Gen.choice
      [ BIs w t <$> genExprRoot ctx t,
        BUnify w t <$> genSTermAt ctx 2 t
      ]
  pure (ctx {ctxScope = Map.insert w t ctx.ctxScope}, acc ++ [item])

-- | A rule that exists only to bind a store-resident variable.
--
-- The gated binding inside an ordinary rule ('genGatedBind') is the
-- faithful shape, but it lands on a rule that also has to /fire/ —
-- match every head, pass every guard — and measured, that put the
-- interleaving in about 2% of programs. Which is to say: the open
-- property was green and almost never open.
--
-- So one rule per program is planted for the job: a single head on a
-- constraint with a position willing to hold nothing, no guard but the
-- @unifiable@ gate, and a body that binds. It fires as soon as the
-- carrier is in the store, so a value the goal stored without one
-- reliably acquires one — from a different unit than stored it, which
-- is the whole point.
--
-- Simplification rather than propagation: the carrier is consumed, so
-- the rule cannot interact with the rest of the program beyond the one
-- binding it exists to make.
genPlantedBinder :: Mode -> NonEmpty Sig -> Gen [Rule]
genPlantedBinder mode sigList
  | mode /= Open || null cands = pure []
  | otherwise =
      Gen.frequency
        [ (1, pure []),
          ( 4,
            do
              (sig, i, g) <- Gen.element cands
              st <- genClosedSTermAt g
              let (sks, sk) = freshSkolems (length sig.sigTvs) emptySkolems
                  sub = Map.fromList (zip sig.sigTvs (map SSk sks))
                  tys = map (substD sub) (NE.toList (sigArgDTys sig))
                  names = ["P" <> tshow k | k <- [0 .. length tys - 1]]
                  pats = zipWith PVar names tys
                  target = names !! i
                  targetTy = tys !! i
                  taintedNames =
                    Set.fromList
                      [ n
                      | (n, spec) <- zip names (NE.toList sig.sigArgs),
                        spec.argBound == MayBeUnbound
                      ]
              pure
                [ Rule
                    { ruleName = "bind_" <> sig.sigName,
                      ruleHead =
                        HSimplify
                          ( HeadC
                              { headSig = sig,
                                headSkolems = sks,
                                pats = case pats of
                                  (x : xs) -> x :| xs
                                  [] -> PWild :| []
                              }
                              :| []
                          ),
                      ruleEvidence = [],
                      guards =
                        [EUnifiable (EVar target targetTy) (sTermToExpr st)],
                      body = [BUnify target targetTy st],
                      ruleTaintedHead = taintedNames,
                      ruleTainted = taintedNames,
                      ruleSkHead = sk,
                      ruleSk = sk
                    }
                ]
          )
        ]
  where
    -- Only a position whose declared type is ground: a closed term has
    -- to be built for it, and at a type parameter there is nothing to
    -- build.
    cands =
      [ (sig, i, g)
      | sig <- NE.toList sigList,
        (i, spec) <- zip [0 ..] (NE.toList sig.sigArgs),
        spec.argBound == MayBeUnbound,
        Just g <- [groundDTy spec.argTy]
      ]

-- | A gated binding of a store-resident variable.
--
-- This is what the open regime exists to produce. A constraint was
-- stored holding a term with no value; this rule matches it, and its
-- body binds that very term — so the value arrives from a different
-- unit than the one that stored it, which is the store interleaving
-- §No mode checking describes and the reason a query variable can come
-- back holding something at all.
--
-- The @unifiable@ guard is what keeps the oracle strict: a failed body
-- @=@ is a hard runtime error, and one indistinguishable from a real
-- fault. Guards are pure and nothing between the guard and the body
-- runs, so the trial unification decides exactly the question the body
-- asks. The right-hand side is a /closed/ term for the same reason:
-- a compound mentioning a free variable would be evaluated by
-- @unifiable@'s own argument position.
genGatedBind :: Ctx -> Gen ([Expr], [BodyItem], Ctx)
genGatedBind ctx
  | null cands = pure ([], [], ctx)
  | otherwise =
      Gen.frequency
        [ (1, pure ([], [], ctx)),
          ( 4,
            do
              (n, t, g) <- Gen.element cands
              st <- genClosedSTermAt g
              -- The taint is deliberately /not/ cleared. The variable is
              -- bound from this body item onward, but the guard-position
              -- observations sit to its left, where it is still free —
              -- and one taint set serves both. Leaving it tainted is
              -- the conservative reading: it only narrows what the
              -- items after it may do with the variable.
              pure
                ( [EUnifiable (EVar n t) (sTermToExpr st)],
                  [BUnify n t st],
                  ctx
                )
          )
        ]
  where
    cands =
      [ (n, t, g)
      | (n, t) <- scopeTys ctx,
        n `Set.member` ctx.ctxTainted,
        Just g <- [groundOf ctx.ctxSk t]
      ]

-- | The smallest closed structural term of a ground type.
genClosedSTermAt :: GTy -> Gen STerm
genClosedSTermAt (GTy c as) = case c of
  CInt -> SLit . LInt <$> Gen.integral (Range.linear 0 20)
  CBool -> SLit . LBool <$> Gen.bool
  CList -> pure SNil
  CAdt def -> do
    ctor <- Gen.element (NE.toList def.adtCtors)
    let sub = Map.fromList (zip def.adtParams (map gToS as))
        fieldGTys = map (groundOrInt . substD sub) ctor.ctorFields
    SCtor ctor.ctorName <$> traverse genClosedSTermAt fieldGTys
  where
    groundOrInt t = fromMaybe gInt (groundOf emptySkolems t)

-- | A closed structural term read as an expression. Total only because
-- the term is closed: it mentions no variable, so nothing here has to
-- decide whether a variable position evaluates — and a cons tail is
-- always itself a list, so it reads back as a list literal. Anything
-- else is an 'error' rather than a silent drop: this expression is the
-- @unifiable@ gate for the body item built from the same term, and the
-- two desynchronizing would turn a benign shape into a hard runtime
-- error the oracle reports as a violation.
sTermToExpr :: STerm -> Expr
sTermToExpr st = case st of
  SLit l -> ELit l
  SNil -> EListLit []
  SCons h t -> case sTermToExpr t of
    EListLit es -> EListLit (sTermToExpr h : es)
    _ -> error "sTermToExpr: cons tail is not a list literal"
  SCtor n ts -> ECtor n (map sTermToExpr ts)
  SVar n t -> EVar n t

-- | Body tells, restricted to strata strictly below every head stratum
-- (see @Note [Termination]@ in "YCHR.TypeSoundness.Instrument").
--
-- A polymorphic callee is a /use/ site, so the generator commits to a
-- substitution for its parameters. The interesting choice is a rigid
-- type this rule holds a value of: the callee's fresh flexible
-- variable then binds to the head's rigid one and the value flows
-- across the two declarations without either ever learning what the
-- store picked.
genTells :: Ctx -> NonEmpty Sig -> Int -> Gen [BodyItem]
genTells ctx sigList minHead
  | null lower = pure []
  | otherwise = do
      n <- Gen.int (Range.constant 0 2)
      replicateM n one
  where
    lower = [s | s <- NE.toList sigList, s.stratum < minHead]
    one = do
      s <- Gen.element lower
      sub <-
        Map.fromList
          <$> traverse
            (\v -> (v,) <$> pickBounded ctx s v)
            s.sigTvs
      args <-
        traverse
          (uncurry (tellArg ctx sub))
          (zip (NE.toList s.sigArgs) [0 :: Int ..])
      pure (BTell s sub args)
    -- A possibly-unbound variable may be passed on, but only bare and
    -- only into a position willing to hold one: a tell argument is
    -- evaluated, so a free variable nested inside a compound would be
    -- a runtime error, while a bare one evaluates to itself.
    tellArg ctx' sub spec _ =
      let ty = substD sub spec.argTy
          taintedVs =
            [ e
            | e@(EVar n _) <- varsAtAny ctx' ty,
              n `Set.member` ctx'.ctxTainted
            ]
       in Gen.frequency
            ( [(3, genExprAt ctx' 2 ty)]
                ++ [ (2, Gen.element taintedVs)
                   | spec.argBound == MayBeUnbound,
                     not (null taintedVs)
                   ]
            )

-- ---------------------------------------------------------------------------
-- Expressions
-- ---------------------------------------------------------------------------

-- | A well-typed expression at an implementation-site type.
--
-- PRECONDITION: @inhabited ctx ty@. Every caller draws its targets from
-- 'instantiationTargets' or from a signature instantiated at those, so
-- the precondition holds by construction and no alternative list here
-- can come up empty.
genExprAt :: Ctx -> Int -> STy -> Gen Expr
genExprAt ctx d ty =
  freqOr
    ctx
    "genExprAt"
    ty
    ( [(3, Gen.element vs) | not (null vs)]
        ++ [(2, g) | g <- structAlts ctx d ty]
        ++ [(3, g) | d > 0, g <- richAlts ctx d ty]
    )
  where
    vs = varsAt ctx ty

-- | 'Gen.frequency' with the precondition spelled out.
--
-- An empty alternative list means a caller asked for a value at a type
-- nothing here can build — an 'inhabited' violation. Reporting the type
-- and the scope turns that from "used with empty list" into a
-- diagnosis, and an 'error' rather than a silent fallback is the same
-- discipline 'patVars' uses: a fallback would quietly generate
-- something other than what was asked for.
freqOr :: Ctx -> String -> STy -> [(Int, Gen a)] -> Gen a
freqOr ctx who ty alts
  | null alts =
      error
        ( who
            ++ ": no inhabitant at "
            ++ T.unpack (renderSTy (stripSTy ctx.ctxSk ty))
            ++ "; scope = "
            ++ show [(n, renderSTy t) | (n, t) <- scopeTys ctx]
        )
  | otherwise = Gen.frequency alts

-- | As 'genExprAt', but never a bare variable at the root.
--
-- Used for @is@ right-hand sides and goal probes: @R is X@ with a
-- syntactically variable right-hand side widens to @any@ and would
-- leave the fragment under test. At a bare rigid type the /only/
-- non-variable form available is @copy_term@ — there is no literal and
-- no constructor at an unknown type — which is why the prelude's one
-- unbounded polymorphic function earns its place in the fragment.
genExprRoot :: Ctx -> STy -> Gen Expr
genExprRoot ctx ty = genNonVarAt ctx 2 ty

genNonVarAt :: Ctx -> Int -> STy -> Gen Expr
genNonVarAt ctx d ty =
  freqOr
    ctx
    "genNonVarAt"
    ty
    ( [(2, g) | g <- structAlts ctx d ty]
        ++ [(3, g) | d > 0, g <- richAlts ctx d ty]
        ++ [(2, ECopy <$> Gen.element vs) | null (structAlts ctx d ty), not (null vs)]
    )
  where
    vs = varsAt ctx ty

-- | The alternatives that build a value of a type out of its own
-- structure: a literal, a list, a constructor application. Empty at a
-- bare rigid type, which is exactly what makes that case special.
structAlts :: Ctx -> Int -> STy -> [Gen Expr]
structAlts ctx d ty = case stripSTy ctx.ctxSk ty of
  SSk _ -> []
  SCon CInt [] -> [(ELit . LInt <$> Gen.integral (Range.linear 0 20))]
  SCon CBool [] -> [(ELit . LBool <$> Gen.bool)]
  SCon CList [el] ->
    (pure (EListLit []))
      : [ (EListLit <$> Gen.list (Range.constant 1 3) (genExprAt ctx (d - 1) el))
        | d > 0,
          inhabited ctx el
        ]
  SCon (CAdt def) args ->
    [ (genCtorExpr ctx (d - 1) def args c)
    | c <- NE.toList def.adtCtors,
      all (inhabited ctx) (ctorFieldTys def args c)
    ]
  SCon _ _ -> []
  where

genCtorExpr :: Ctx -> Int -> AdtDef -> [STy] -> CtorDef -> Gen Expr
genCtorExpr ctx d def args c =
  ECtor c.ctorName
    <$> traverse (genExprAt ctx (max 0 d)) (ctorFieldTys def args c)

-- | The alternatives that come from the fixed predicate library and
-- the prelude. All monomorphic except @copy_term@, so they are
-- available only at the types the library covers — which is the
-- concrete part of the fragment.
richAlts :: Ctx -> Int -> STy -> [Gen Expr]
richAlts ctx d ty
  | ty' == gToS gInt =
      [ (EArith <$> Gen.element [Add, Sub, Mul] <*> sub (gToS gInt) <*> sub (gToS gInt)),
        (call FnLen),
        (call FnArea)
      ]
        ++ copyAlt
  | ty' == gToS gBool =
      [ (ECmp <$> Gen.element [CLt, CGt, CGe, CLe] <*> sub (gToS gInt) <*> sub (gToS gInt)),
        eqAlt,
        (ENot <$> sub (gToS gBool)),
        (call FnLt),
        (call FnLte),
        (call FnSameInt),
        (call FnIsZero),
        (call FnIsNil),
        (call FnIsRed)
      ]
        ++ classAlts
        ++ copyAlt
  | otherwise = copyAlt
  where
    ty' = stripSTy ctx.ctxSk ty
    sub = genExprAt ctx (d - 1)
    call fn = ECall fn <$> traverse sub (map gToS (fst (libFnSig fn)))
    -- @copy_term(A) -> A@ at any inhabited type, which is the one way
    -- a polymorphic function is exercised at a rigid argument without
    -- a @requiring@ clause.
    copyAlt = [(ECopy <$> Gen.element vs) | not (null vs)]
    vs = varsAt ctx ty
    eqAlt = do
      t <- pickTarget ctx
      -- Ask-equality never evaluates: it compares structure, and two
      -- distinct free variables simply come back unequal. So this is
      -- one of the few places a possibly-unbound variable may appear.
      let anyVs = varsAtAny ctx t
      Gen.frequency
        ( [(3, EEq t <$> sub t <*> sub t)]
            ++ [ (1, EEq t <$> Gen.element anyVs <*> Gen.element anyVs)
               | length anyVs > 1
               ]
        )
    -- An overloaded predicate at a type the site can actually call it
    -- at. At a ground type that means a declared instance; at a rigid
    -- one it means an ambient signature, which is the whole point of a
    -- @requiring@ clause and the only way an overloaded operation
    -- reaches a rigid type at all.
    classAlts =
      [ EClass n . (: []) <$> genExprAt ctx (d - 1) at
      | at <- callableTargets,
        n <- classesAt ctx at
      ]
    callableTargets =
      [ t
      | t <- instantiationTargets ctx,
        inhabited ctx t,
        not (null (classesAt ctx t))
      ]

genSTermAt :: Ctx -> Int -> STy -> Gen STerm
genSTermAt ctx d ty = freqOr ctx "genSTermAt" ty (varAlt ++ structs)
  where
    -- Structural: @=@ evaluates neither operand, so a term holding no
    -- value yet is fine here — and passing one on is how the open
    -- regime moves an unbound value around at all.
    vs = [SVar n t | EVar n t <- varsAtAny ctx ty]
    varAlt = [(2, Gen.element vs) | not (null vs)]
    sub = genSTermAt ctx (d - 1)
    structs = case stripSTy ctx.ctxSk ty of
      SSk _ -> []
      SCon CInt [] -> [(3, SLit . LInt <$> Gen.integral (Range.linear 0 20))]
      SCon CBool [] -> [(3, SLit . LBool <$> Gen.bool)]
      SCon CList [el] ->
        (2, pure SNil)
          : [(3, SCons <$> sub el <*> sub ty) | d > 0, inhabited ctx el]
      SCon (CAdt def) args ->
        [ ( 3,
            SCtor c.ctorName
              <$> traverse (genSTermAt ctx (max 0 (d - 1))) (ctorFieldTys def args c)
          )
        | c <- NE.toList def.adtCtors,
          all (inhabited ctx) (ctorFieldTys def args c)
        ]
      SCon _ _ -> []

-- ---------------------------------------------------------------------------
-- Ground values, for the goal
-- ---------------------------------------------------------------------------

-- | The smallest closed expression of a ground type. Terminates
-- because a constructor's fields only mention base types, @list@, or
-- strictly earlier definitions.
genClosedLeafAt :: GTy -> Gen Expr
genClosedLeafAt (GTy c as) = case c of
  CInt -> ELit . LInt <$> Gen.integral (Range.linear 0 20)
  CBool -> ELit . LBool <$> Gen.bool
  CList -> pure (EListLit [])
  CAdt def -> do
    ctor <- Gen.element (NE.toList def.adtCtors)
    let fieldGTys = map (groundOfUnsafe . substD sub) ctor.ctorFields
        sub = Map.fromList (zip def.adtParams (map gToS as))
    ECtor ctor.ctorName <$> traverse genClosedLeafAt fieldGTys
  where
    groundOfUnsafe t = case groundOf emptySkolems t of
      Just g -> g
      Nothing -> error "genClosedLeafAt: field type is not ground"

-- ---------------------------------------------------------------------------
-- The goal
-- ---------------------------------------------------------------------------

-- | 2–6 goal tells with closed arguments, plus 0–2 probes.
--
-- A goal that lands in a gap between every head pattern makes the whole
-- program dead weight — the rule bodies, and with them the observations
-- that carry the property, never run. So the goal is biased towards
-- firing something, in two ways. Usually it instantiates one whole rule
-- head at once ('genRuleInstance'), which is the only way a join or an
-- aliased variable is reliably satisfied. The remaining tells are drawn
-- freely but still prefer constraint symbols some rule heads on, and
-- for a /monomorphic/ symbol prefer an instance of a pattern a head
-- matches at that exact position.
--
-- The position-seed pool is restricted to monomorphic symbols because
-- a polymorphic head's pattern only makes sense at the instantiation
-- that occurrence chose: a literal @5@ harvested from a @c(A)@ head
-- checked at @A := int@ says nothing about a tell that instantiates
-- @A := bool@. 'genRuleInstance', which chooses the instantiation and
-- the pattern together, covers the polymorphic case instead.
genGoal :: [GTy] -> [AdtDef] -> [ClassFn] -> NonEmpty Sig -> [Rule] -> Gen Goal
genGoal univ adts cls sigList rs = do
  seeded <- genSeeded
  extra <- Gen.int (Range.constant 1 3)
  t0 <- genTell (0 :: Int)
  ts <- traverse genTell [1 .. extra]
  nProbes <- Gen.int (Range.constant 0 2)
  ps <- traverse genProbe [0 .. nProbes - 1]
  let allTells = t0 : ts
      plain = [(s, args) | (s, _, args) <- allTells] ++ seeded
  pure
    Goal
      { tells = case plain of
          (x : xs) -> x :| xs
          [] -> error "genGoal: no tells",
        probes = ps,
        unbounds = concatMap unboundsOf allTells
      }
  where
    goalCtx =
      Ctx
        { ctxSk = emptySkolems,
          ctxScope = Map.empty,
          ctxUniv = univ,
          ctxAdts = adts,
          ctxClasses = cls,
          ctxAmbients = [],
          ctxBounded = [],
          ctxTainted = Set.empty
        }
    -- The whole head of one rule, matched exactly. Dropping it
    -- occasionally keeps the free path — and the programs where nothing
    -- matches at all — represented. Drawn independently of the free
    -- tells: making the free count depend on how many seeded tells came
    -- back would mean shrinking the seed adds free tells, which is how
    -- a shrink plateaus.
    genSeeded
      | null rs = pure []
      | otherwise =
          Gen.frequency
            [ (4, NE.toList <$> (Gen.element rs >>= genRuleInstance univ cls)),
              (1, pure [])
            ]
    seeds = seedMap rs
    -- A goal is a use site like any other, so a bounded parameter may
    -- only be instantiated where the bound is discharged. Goals are
    -- ground, so that means a declared instance of the named class.
    -- An empty intersection would mean an unsatisfiable bound, which
    -- is a generator bug, not a program the fragment contains (see
    -- 'boundedTargets') — so it fails loudly rather than quietly
    -- emitting a goal the query type-check rejects (YCHR-60012).
    goalTargets s v = case [b | b <- s.sigBounds, b.bsTv == v] of
      [] -> univ
      bs -> case foldr (intersectBy) univ (map instancesOf bs) of
        [] ->
          error
            ( "genGoal: no ground instance discharges the bounds on "
                ++ show v
                ++ " of "
                ++ T.unpack s.sigName
            )
        ts -> ts
    instancesOf b = case List.find (\c -> c.cfName == b.bsClass) cls of
      Just c -> classInstances c
      Nothing -> univ
    intersectBy xs ys = [x | x <- xs, x `elem` ys]
    headSigs = [h.headSig | r <- rs, h <- ruleHeads r]
    genSigChoice =
      Gen.frequency
        ( [(3, Gen.element headSigs) | not (null headSigs)]
            ++ [(1, Gen.element (NE.toList sigList))]
        )
    -- A query variable passed unbound into a position willing to hold
    -- one. This is how anything gets into the store without a value:
    -- a bare variable in a goal argument is allocated fresh by the
    -- runtime, and whatever later binds it does so from another unit.
    unboundsOf (s, sub, args) =
      [ (n, groundD sub spec.argTy)
      | (spec, e) <- zip (NE.toList s.sigArgs) args,
        EVar n _ <- [e],
        "U" `T.isPrefixOf` n,
        spec.argBound == MayBeUnbound
      ]
    genTell tIx = do
      s <- genSigChoice
      sub <-
        Map.fromList
          <$> traverse (\v -> (v,) <$> Gen.element (goalTargets s v)) s.sigTvs
      args <-
        traverse
          (genArg tIx s)
          ( zip3
              [0 ..]
              (map (groundD sub) (NE.toList (sigArgDTys s)))
              (NE.toList s.sigArgs)
          )
      pure (s, sub, args)
    -- At a position willing to hold an unbound term, sometimes pass a
    -- fresh query variable instead of a value. The runtime allocates
    -- it, the constraint is stored holding nothing, and whatever binds
    -- it later does so from a different unit — which is the whole
    -- store-interleaving shape, arranged with one draw.
    --
    -- Names are positional so they are unique without a counter, and
    -- the @U@ prefix is what 'unboundsOf' recognises them by.
    genArg tIx s (i, g, spec)
      | spec.argBound == MayBeUnbound =
          Gen.frequency
            [ (2, pure (EVar ("U" <> tshow tIx <> "_" <> tshow i) (gToS g))),
              (3, genArgValue s (i, g))
            ]
      | otherwise = genArgValue s (i, g)
    genArgValue s (i, g) = case Map.lookup (s.sigName, i) seeds of
      Just ps@(_ : _)
        | null s.sigTvs ->
            Gen.frequency
              [ (3, Gen.element ps >>= patInstance Map.empty g),
                (1, genExprRoot goalCtx (gToS g))
              ]
      _ -> genExprRoot goalCtx (gToS g)
    genProbe i = do
      g <- Gen.element univ
      e <- genExprRoot goalCtx (gToS g)
      pure Probe {probeVar = "R" <> tshow i, probeTy = g, probeExpr = e}

-- | Instantiate a whole rule head into goal tells that match it.
--
-- A ground type is drawn for each of the rule's skolem /classes/, not
-- for each skolem: 'maybeAlias' may have merged two occurrences'
-- rigid variables, and the store must then really hold one instance
-- for both or the rule cannot fire.
--
-- Every pattern variable is given its value /once/, before any head is
-- read off, so a variable shared between two heads comes out equal in
-- both. Left to independent draws that agreement is a coincidence, and
-- the rates show it: two-head rules fired 22% of the time against 33%
-- for single-head ones, and aliased rules only 12%.
genRuleInstance :: [GTy] -> [ClassFn] -> Rule -> Gen (NonEmpty (Sig, [Expr]))
genRuleInstance univ cls r = do
  assign <-
    Map.fromList
      <$> traverse (\s -> (s,) <$> Gen.element (targetsFor s)) classes
  let groundTy = groundWith assign
  binding <-
    Map.fromList
      <$> traverse
        (\(n, t) -> (n,) <$> genClosedLeafAt (groundTy t))
        (ruleVars r)
  traverse (headInstance groundTy binding) (ruleHeadList r.ruleHead)
  where
    -- Grounding resolves under the runtime view: the parameter
    -- identifications an alias forces ('skForce') constrain which
    -- instances can actually fire the rule, even though the checker
    -- model deliberately does not know them. Only this function may
    -- look through the forcings — every typing decision upstream
    -- uses the plain env.
    rt = runtimeView r.ruleSk
    -- The tells this produces are use sites, so a skolem standing for
    -- a bounded parameter may only be grounded at a declared instance
    -- of the named class — otherwise the goal it builds cannot
    -- discharge the bound and the program is rejected before it runs.
    -- No instance at all would mean an unsatisfiable bound, which is
    -- a generator bug (see 'boundedTargets'), so it fails loudly
    -- rather than quietly building that rejected goal.
    targetsFor sk = case [c | (s', c) <- boundedSkolems, s' == sk] of
      [] -> univ
      names -> case [t | t <- univ, all (isInstance t) names] of
        [] ->
          error
            ( "genRuleInstance: no ground instance discharges the"
                ++ " bounds on "
                ++ show sk
            )
        ts -> ts
    isInstance t nm = case List.find (\c -> c.cfName == nm) cls of
      Just c -> t `elem` classInstances c
      Nothing -> True
    boundedSkolems =
      [ (sk, b.bsClass)
      | h <- ruleHeads r,
        b <- h.headSig.sigBounds,
        (tv, sk) <- zip h.headSig.sigTvs h.headSkolems,
        tv == b.bsTv
      ]
    classes =
      List.nub
        [ s
        | h <- ruleHeads r,
          t <- NE.toList (headArgTys h),
          s <- skolemsOf rt t
        ]
    groundWith assign t = case resolveSTy rt t of
      SSk s -> Map.findWithDefault gInt s assign
      SCon c as -> GTy c (map (groundWith assign) as)

-- | One head of a rule, read off as a tell that matches it, under a
-- ground assignment and a variable binding already fixed.
headInstance ::
  (STy -> GTy) ->
  Map Text Expr ->
  HeadC ->
  Gen (Sig, [Expr])
headInstance groundTy binding h =
  (h.headSig,)
    <$> traverse
      (uncurry (patInstance binding))
      (zip (map groundTy (NE.toList (headArgTys h))) (NE.toList h.pats))

-- | Head patterns harvested from the generated rules, keyed by the
-- constraint symbol and argument position they were found at.
--
-- Keying by position rather than by type is what makes the goal bias
-- effective: a head like @c1(0, red)@ only matches a tell that hits
-- /both/ positions, and a pool keyed by type alone would draw the @0@
-- for the @red@ slot as readily as for its own.
--
-- Only /structured/ patterns are collected. A bare variable or wildcard
-- constrains nothing, so seeding from it would be the same as drawing
-- the argument freely.
seedMap :: [Rule] -> Map (Text, Int) [Pat]
seedMap rs =
  Map.fromListWith
    (++)
    [ ((h.headSig.sigName, i), [p])
    | r <- rs,
      h <- ruleHeads r,
      (i, p) <- zip [0 ..] (NE.toList h.pats),
      structured p
    ]
  where
    structured p = case p of
      PVar _ _ -> False
      PWild -> False
      _ -> True

-- | A closed expression matching a head pattern, with each variable and
-- wildcard hole filled by a value of the hole's own type.
--
-- Instantiating /partial/ patterns is what lets the goal bias reach
-- shapes like @[7 | T]@ or @circle(R)@. Harvesting only fully-closed
-- patterns left 38% of the structured head positions with no candidate
-- at all, and a goal that misses one head position never fires the rule.
--
-- @env@ pins the variables that already have a value, so a variable
-- repeated across a rule's heads instantiates the same way in each; a
-- hole not in @env@ is filled independently.
patInstance :: Map Text Expr -> GTy -> Pat -> Gen Expr
patInstance env g@(GTy con args) p = case p of
  PVar n _ -> maybe (genClosedLeafAt g) pure (Map.lookup n env)
  PWild -> genClosedLeafAt g
  PLit l -> pure (ELit l)
  PNil -> pure (EListLit [])
  PCons h t -> case (con, args) of
    (CList, [el]) -> consExpr <$> patInstance env el h <*> patInstance env g t
    _ -> error ("patInstance: cons pattern at " ++ T.unpack (renderGTy g))
  PCtor cn ps -> case con of
    CAdt def -> case findCtor def cn of
      Just c
        | length c.ctorFields == length ps ->
            ECtor cn
              <$> traverse
                (uncurry (patInstance env))
                (zip (map groundField (ctorFieldTys def (map gToS args) c)) ps)
        | otherwise -> error ("patInstance: arity mismatch for " ++ T.unpack cn)
      Nothing ->
        error
          ( "patInstance: "
              ++ T.unpack cn
              ++ " is not a constructor of "
              ++ T.unpack def.adtName
          )
    _ ->
      error
        ( "patInstance: constructor pattern at non-algebraic type "
            ++ T.unpack (renderGTy g)
        )
  where
    groundField t = case groundOf emptySkolems t of
      Just gt -> gt
      Nothing -> error "patInstance: field type is not ground"

-- | Prepend an element to a list-typed instance. Every list instance
-- 'patInstance' produces is an 'EListLit', so the other case cannot
-- arise: 'PNil' and 'genClosedLeafAt' both give the empty list, a
-- nested 'PCons' is this function again, and a 'PVar' found in the
-- binding holds a value 'genRuleInstance' built with 'genClosedLeafAt'
-- at the variable's own type.
consExpr :: Expr -> Expr -> Expr
consExpr h t = case t of
  EListLit es -> EListLit (h : es)
  _ -> error "consExpr: list instance is not a list literal"
