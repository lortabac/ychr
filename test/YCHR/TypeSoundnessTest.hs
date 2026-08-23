{-# LANGUAGE OverloadedStrings #-}

-- | Property test for the first of the two correctness claims the type
-- system rests on (@docs\/reference\/type-system.md@, §Soundness):
--
-- > Soundness of the fully-typed fragment — if no expression is typed
-- > @any@ and the program type-checks, no operation receives a value of
-- > an unexpected type at runtime.
--
-- The test generates a random CHR program that is well-typed /by
-- construction/ (a typed core AST, §Core AST below), pretty-prints it to
-- @.chr@ source, pushes it through the real pipeline
-- (@compileModules@ → @typeCheckProgram@ → run), and requires the whole
-- round trip to succeed.
--
-- Absence of a crash is a weak oracle on its own — an operation could
-- receive a wrong-typed value and happen not to mind. So generated
-- programs are /instrumented/: every variable whose static type is known
-- carries an in-language @assert_τ\/1@ call that deep-checks the runtime
-- value against that type (see 'instrument'). The assertion functions
-- have no catch-all equation, so a value outside its static type raises
-- \"no matching equation\", which the oracle catches. That makes the
-- property statement observable rather than merely hoped for.
--
-- The oracle is /strict/: any exception at all is a failure. Section
-- 'Note [Why benign failures are impossible]' argues that the generated
-- fragment cannot fail for any reason other than a real violation.
--
-- The second claim (the gradual guarantee) is a separate property; this
-- module's core AST keeps annotations as data ('Ann') so that generator
-- can be reused by erasing annotations to @any@.
--
-- What v1 deliberately leaves out, so the coverage is not overread:
--
--   * /Polymorphism/. Every generated declaration is monomorphic, so
--     the rigid-variable machinery §Soundness credits for polymorphic
--     declarations — @requiring@ bounds, skolem merging — is untouched.
--     That is the most valuable next increment.
--   * /The open corner/. Goals are ground and nothing unbound is ever
--     stored, so the store-interleaving corner the spec leaves open is
--     out of scope (and the strict oracle depends on that; see
--     'Note [Why benign failures are impossible]').
--   * Floats, strings, lambdas and @'$call'@; rules with three or more
--     heads; simpagations other than @1 \\ 1@; recursive generated
--     algebraic types (@list(int)@ is the one recursive shape);
--     same-symbol recursion in rule bodies (forbidden by the
--     stratification that gives termination).
module YCHR.TypeSoundnessTest (tests) where

import Control.Exception (SomeException, fromException, try)
import Control.Monad (foldM, replicateM, unless)
import Data.List (find, nubBy)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Hedgehog
  ( Gen,
    Property,
    PropertyT,
    annotate,
    cover,
    evalIO,
    failure,
    forAllWith,
    property,
    withTests,
  )
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..))
import YCHR.Internal.Display (Display (..))
import YCHR.Internal.Meta (metaHostCallRegistry)
import YCHR.Internal.Runtime.Interpreter (baseHostCallRegistry)
import YCHR.Internal.TypeCheck (TypeCheckResult (..), typeCheckProgram)
import YCHR.Internal.Types (Name (..), Term (..))
import YCHR.Run (Error (..), compileModules, runProgramWithQuery)

-- ---------------------------------------------------------------------------
-- Core AST
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
-- generated program terminate (see 'Note [Termination]').
data Sig = Sig {sigName :: Text, argAnns :: NonEmpty Ann, stratum :: Int}
  deriving (Eq, Show)

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
-- defines (see 'preamble'). Every one of them is total and fully typed,
-- which is what lets the oracle stay strict.
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
    -- discarded. Inserted by 'instrument', never generated directly.
    BAssert Text Ty
  deriving (Eq, Show)

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
-- ('conforms' over the returned 'Term').
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

{- Note [Why benign failures are impossible]

The strict oracle (any exception is a failure) is only justified if the
generated fragment cannot fail for a reason unrelated to soundness. The
argument rests on one invariant: every in-scope variable is ground.

  * Goal tells carry closed expressions, so the initial store is ground.
    Both producers keep that so: the free arguments come from
    `genExprRoot` under an empty environment, and the seeded ones from
    `patInstance`, whose holes are filled by `genClosedLeaf`.
  * Head matching therefore binds head variables to ground values.
  * `BIs` and `BUnify` bind a *fresh* variable from ground inputs;
    guards bind nothing.

From groundness the rest follows:

  * No evaluated position ever sees an unbound variable, so the
    "unbound variable in evaluated position" runtime error cannot fire.
  * `BUnify` cannot fail: its left-hand side is always a fresh variable,
    which unifies with anything. (Failed body unification *is* a runtime
    error — see `unifyOrError` in the interpreter — so this matters.)
  * Nothing observes an unbound variable, so no reactivation ever
    happens.
  * The preamble predicates and the prelude functions used (`+ - *`,
    `< > >= =<`, `==`, `not`, and `integer/1` under `assert_int`) are
    total. `div`/`mod` are excluded because they are partial.
  * No form in `Expr`/`STerm` can widen to `any`: no host calls, no
    `quote`, no undeclared constructors, no evaluable head under `=`,
    and never a bare-variable `is` right-hand side (which the spec
    widens to `any`).

The only deliberately partial functions in a generated module are the
`assert_τ` instrumentation predicates, and their "no matching equation"
failure happens exactly when a runtime value falls outside its static
type — that is the property violation being detected, not noise.
-}

{- Note [Termination]

Every generated program terminates, by strict stratification: a rule
body may only tell constraints whose stratum is strictly below every
stratum appearing in the rule's head.

Induction downward from the top stratum. Instances at the top stratum
can only come from the goal (a rule telling it would need every head
stratum strictly above it), so there are finitely many. Given finitely
many instances at all strata above k, each rule whose heads all sit
above k fires finitely often — a propagation rule at most once per tuple
of constraint identifiers (propagation history), a simplification or
simpagation rule at most once per tuple as well, since each firing
consumes one of the tuple's members. So stratum k receives finitely many
instances, and the induction goes through.

Termination alone is not enough for a 60s test budget, though: the
per-level bound is quadratic in the level above, so a four-stratum
program can in principle derive hundreds of thousands of constraints.
'pruneTells' caps that statically — see its haddock.
-}

{- Note [Firing rates]

A program whose rules never fire runs none of the assertions that carry
the property, so it costs a test iteration and observes nothing. That is
a runtime fact `coverShape` cannot see, so it is measured out of band:
splice a body that always raises (`Z = 1, Z = 2` — well-typed, and a
failed body unification is a runtime error) into the rules of interest,
run, and count the programs that then fail. A failure means those rules
fired.

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
-- The fixed preamble
-- ---------------------------------------------------------------------------

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
-- 'renderAdt', the same path generated types take, so the values the
-- generator reasons with and the source it emits cannot drift apart.
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

-- ---------------------------------------------------------------------------
-- Small helpers
-- ---------------------------------------------------------------------------

tshow :: (Show a) => a -> Text
tshow = T.pack . show

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
-- left-to-right order. Names may repeat: 'maybeAlias' can rename one
-- pattern variable to another, which is the point of that pass.
-- 'ruleVars' is the deduplicating wrapper.
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

-- ---------------------------------------------------------------------------
-- Generation
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
genProgram = do
  defs <- genAdts
  let allAdts = fixedAdts ++ defs
      univ = baseTys ++ map TAdt allAdts
  sigList <- genSigs univ
  ruleList <- genRules univ sigList
  g <- genGoal univ sigList ruleList
  pure Program {adts = defs, sigs = sigList, rules = ruleList, goal = g}

-- | 0–2 algebraic types. A definition may only mention base types, the
-- fixed types, and /earlier/ generated types, so the definition graph is
-- a DAG and no depth budget is needed. Constructor names are globally
-- unique (@k0@, @k1@, …) across all generated types.
genAdts :: Gen [AdtDef]
genAdts = do
  n <- Gen.int (Range.constant 0 2)
  go n 0 0 []
  where
    go :: Int -> Int -> Int -> [AdtDef] -> Gen [AdtDef]
    go 0 _ _ acc = pure (reverse acc)
    go k tyIx ctorIx acc = do
      let avail = baseTys ++ map TAdt (fixedAdts ++ reverse acc)
      (cs, ctorIx') <- genCtors avail ctorIx
      let def = AdtDef {adtName = "t" <> tshow tyIx, ctors = cs}
      go (k - 1) (tyIx + 1) ctorIx' (def : acc)

genCtors :: [Ty] -> Int -> Gen (NonEmpty CtorDef, Int)
genCtors avail start = do
  extra <- Gen.int (Range.constant 0 2)
  c0 <- genCtor avail start
  rest <- traverse (genCtor avail) [start + 1 .. start + extra]
  pure (c0 :| rest, start + extra + 1)

genCtor :: [Ty] -> Int -> Gen CtorDef
genCtor avail ix = do
  fs <- Gen.list (Range.constant 0 2) (Gen.element avail)
  pure CtorDef {ctorName = "k" <> tshow ix, fields = fs}

-- | 2–4 constraint declarations, arity 1–3. The stratum is the
-- declaration's position, which is what 'genRule' uses to keep body
-- tells strictly descending.
genSigs :: [Ty] -> Gen (NonEmpty Sig)
genSigs univ = do
  extra <- Gen.int (Range.constant 1 3)
  s0 <- genSig univ 0
  rest <- traverse (genSig univ) [1 .. extra]
  pure (s0 :| rest)

genSig :: [Ty] -> Int -> Gen Sig
genSig univ ix = do
  a0 <- Gen.element univ
  more <- Gen.list (Range.constant 0 2) (Gen.element univ)
  pure
    Sig
      { sigName = "c" <> tshow ix,
        argAnns = mkAnn a0 :| map mkAnn more,
        stratum = ix
      }
  where
    mkAnn t = Ann {declared = t, erased = False}

genRules :: [Ty] -> NonEmpty Sig -> Gen [Rule]
genRules univ sigList = do
  n <- Gen.int (Range.linear 1 6)
  traverse (genRule univ sigList) [0 .. n - 1]

-- | Which of the three CHR rule shapes to generate.
data RuleKind = KSimplify | KPropagate | KSimpagate

genRule :: [Ty] -> NonEmpty Sig -> Int -> Gen Rule
genRule univ sigList ix = do
  kind <- Gen.element [KSimplify, KPropagate, KSimpagate]
  hs <- case kind of
    KSimpagate -> genHeads 2
    _ -> Gen.int (Range.constant 1 2) >>= genHeads
  aliased <- maybeAlias hs
  let rh = mkRuleHead kind aliased
      heads_ = ruleHeadList rh
      gamma0 = Map.fromList (concatMap headVars (NE.toList heads_))
  gs <- Gen.list (Range.constant 0 2) (genGuard univ gamma0)
  nBinds <- Gen.int (Range.constant 0 2)
  (gamma1, binds) <- foldM (genBind univ) (gamma0, []) [0 .. nBinds - 1]
  tellItems <- genTells univ sigList gamma1 (minimum (fmap (.headSig.stratum) heads_))
  pure
    Rule
      { ruleName = "r" <> tshow ix,
        ruleHead = rh,
        guards = gs,
        body = binds ++ tellItems
      }
  where
    genHeads n = traverse (genHead sigList) (0 :| [1 .. n - 1])

-- | A rule guard, anchored on a head variable whenever one is in scope.
--
-- A conjunct that mentions no variable is a compile-time constant, and a
-- constant-false one makes the rule unconditionally dead — which costs a
-- whole test iteration, since a rule that never fires runs none of the
-- assertions that carry the property. Generating the guard freely gave a
-- closed conjunct 64% of the time (guards like @is_zero(3)@), because
-- 'genLeaf' can only reach for a variable at the type it is asked for
-- and the head rarely binds one at every type a boolean test descends
-- through. So the guard is built /around/ a variable instead.
--
-- The bare boolean head variable (the @c(X) \<=\> X | …@ idiom, the only
-- thing that puts a plain variable in boolean position) survives as one
-- of the 'TBool' alternatives.
--
-- The anchor is drawn from the variables that some predicate can /say
-- something about/ when there are any. A generated algebraic type has no
-- predicate over it, so its only test is an equality against a value
-- drawn independently — which is false almost every time, and so just
-- relocates the dead-rule problem from constant-false to
-- improbably-true.
genGuard :: [Ty] -> Map Text Ty -> Gen Expr
genGuard univ env
  | null vars = genNode univ env 2 TBool
  | otherwise =
      Gen.frequency
        ( [(4, Gen.element testable) | not (null testable)]
            ++ [(1, Gen.element vars)]
        )
        >>= uncurry (genGuardOn univ env)
  where
    vars = Map.toList env
    testable = [b | b@(_, t) <- vars, hasPredicate t]
    -- Must agree with the types 'genGuardOn' gives a non-empty
    -- @specific@ list: advertising a type here that it has no test for
    -- would just route more anchors to the equality-only path.
    hasPredicate t = case t of
      TAdt def -> def == colorDef || def == shapeDef
      _ -> True

-- | A boolean test mentioning the given variable. The two equality
-- alternatives work at every type, so each 'Ty' only adds what is
-- interesting about it, and no case can come up empty.
--
-- Every alternative puts the anchor on one side and draws the other
-- side with the anchor /out of scope/. With it in scope 'genLeaf' picks
-- it back out often enough to matter: @V == V@ accounted for most of the
-- variable-to-variable equalities, and @V < V@ and friends for a further
-- 5% of conjuncts, two fifths of those constant-false. A constant guard
-- tests nothing while still counting towards 'coverShape'\'s guard
-- label, and a constant-false one kills the rule outright. Nothing is
-- lost by the deletion, since the anchor already occupies one operand.
genGuardOn :: [Ty] -> Map Text Ty -> Text -> Ty -> Gen Expr
genGuardOn univ env n t = Gen.choice (generic ++ specific)
  where
    v = EVar n t
    sub = genExpr univ (Map.delete n env) 1
    generic = [EEq t v <$> sub t, EEq t <$> sub t <*> pure v]
    -- Comparisons against an int-valued expression built from the
    -- variable, in both operand orders.
    intTests e =
      [ ECmp <$> genCmp <*> pure e <*> sub TInt,
        ECmp <$> genCmp <*> sub TInt <*> pure e
      ]
    genCmp = Gen.element [CLt, CGt, CGe, CLe]
    specific = case t of
      TInt ->
        intTests v
          ++ [ pure (ECall FnIsZero [v]),
               (\e -> ECall FnLt [v, e]) <$> sub TInt,
               (\e -> ECall FnLte [e, v]) <$> sub TInt,
               (\e -> ECall FnSameInt [v, e]) <$> sub TInt
             ]
      TBool -> [pure v, pure (ENot v)]
      TListInt -> pure (ECall FnIsNil [v]) : intTests (ECall FnLen [v])
      TAdt def
        | def == colorDef -> [pure (ECall FnIsRed [v])]
        | def == shapeDef -> intTests (ECall FnArea [v])
        | otherwise -> []

-- | Fit a generated head list to one of the three rule shapes. A
-- simpagation needs two heads; 'genRule' always asks for two when it
-- picks that shape, and a one-head list degrades to a simplification
-- rather than being fabricated into shape.
mkRuleHead :: RuleKind -> NonEmpty HeadC -> RuleHead
mkRuleHead kind hs = case (kind, hs) of
  (KPropagate, _) -> HPropagate hs
  (KSimpagate, k :| (r : rest)) -> HSimpagate (k :| []) (r :| rest)
  _ -> HSimplify hs

genHead :: NonEmpty Sig -> Int -> Gen HeadC
genHead sigList hIx = do
  sig <- Gen.element (NE.toList sigList)
  let (t0 :| ts) = sigArgTys sig
  p0 <- genPat 2 [0, hIx] t0
  rest <- traverse (\(i, t) -> genPat 2 [i, hIx] t) (zip [1 :: Int ..] ts)
  pure HeadC {headSig = sig, pats = p0 :| rest}

-- | A head pattern for a declared argument type. Variable names are
-- derived from the position path (head index, argument index, then the
-- path down into the pattern), so they are unique by construction and
-- no fresh-name counter has to be threaded through the generator.
genPat :: Int -> [Int] -> Ty -> Gen Pat
genPat d path ty = Gen.frequency (common ++ specific)
  where
    common = [(6, pure (PVar (varName path) ty)), (1, pure PWild)]
    sub i = genPat (d - 1) (i : path)
    specific = case ty of
      TInt -> [(2, PLit . LInt <$> Gen.integral (Range.linear 0 20))]
      TBool -> [(2, PLit . LBool <$> Gen.bool)]
      TListInt ->
        (2, pure PNil)
          : [(3, PCons <$> sub 0 TInt <*> sub 1 TListInt) | d > 0]
      TAdt def -> [(3, genCtorPat def) | d > 0]
    genCtorPat def = do
      c <- Gen.element (NE.toList def.ctors)
      ps <- traverse (\(i, t) -> sub i t) (zip [0 :: Int ..] c.fields)
      pure (PCtor c.ctorName ps)

varName :: [Int] -> Text
varName path = "V" <> T.intercalate "_" (map tshow (reverse path))

-- | With some probability, rename one pattern variable to another of
-- the same type — possibly in a different head. The repeated variable
-- becomes an implicit equality once the compiler puts the rule in head
-- normal form, which puts the rule through the checker's @GuardEqual@
-- path.
--
-- Only at /concrete/ types, though: every generated declaration is
-- monomorphic, so no rigid variables are allocated and the skolem-merge
-- reading of @GuardEqual@ is not reached. Exercising that needs
-- polymorphic declarations, which v1 does not generate.
maybeAlias :: NonEmpty HeadC -> Gen (NonEmpty HeadC)
maybeAlias hs
  | null pairs = pure hs
  | otherwise = do
      doIt <- Gen.frequency [(2, pure True), (3, pure False)]
      if not doIt
        then pure hs
        else do
          (keep, drop_) <- Gen.element pairs
          pure (fmap (renameHead drop_ keep) hs)
  where
    vs = concatMap headVars (NE.toList hs)
    pairs = [(a, b) | (a, ta) <- vs, (b, tb) <- vs, a < b, ta == tb]

renameHead :: Text -> Text -> HeadC -> HeadC
renameHead from to h = h {pats = fmap go h.pats}
  where
    go p = case p of
      PVar n t | n == from -> PVar to t
      PCons a b -> PCons (go a) (go b)
      PCtor c ps -> PCtor c (map go ps)
      _ -> p

-- | One body binding: @W is E@ or @W = T@. Both bind a /fresh/
-- variable, which is what keeps @=@ unfailable and the store ground.
genBind ::
  [Ty] ->
  (Map Text Ty, [BodyItem]) ->
  Int ->
  Gen (Map Text Ty, [BodyItem])
genBind univ (env, acc) i = do
  t <- Gen.element univ
  let w = "W" <> tshow i
  item <-
    Gen.choice
      [ BIs w t <$> genExprRoot univ env t,
        BUnify w t <$> genSTerm env 2 t
      ]
  pure (Map.insert w t env, acc ++ [item])

-- | Body tells, restricted to strata strictly below every head stratum
-- (see 'Note [Termination]').
genTells :: [Ty] -> NonEmpty Sig -> Map Text Ty -> Int -> Gen [BodyItem]
genTells univ sigList env minHead
  | null lower = pure []
  | otherwise = do
      n <- Gen.int (Range.constant 0 2)
      replicateM n one
  where
    lower = [s | s <- NE.toList sigList, s.stratum < minHead]
    one = do
      s <- Gen.element lower
      args <- traverse (genExpr univ env 2) (NE.toList (sigArgTys s))
      pure (BTell s args)

-- | A well-typed expression of the requested type, over the variables
-- in scope.
genExpr :: [Ty] -> Map Text Ty -> Int -> Ty -> Gen Expr
genExpr univ env d ty
  | d <= 0 = genLeaf env ty
  | otherwise =
      Gen.frequency [(2, genLeaf env ty), (3, genNode univ env d ty)]

genLeaf :: Map Text Ty -> Ty -> Gen Expr
genLeaf env ty =
  Gen.frequency
    ([(3, Gen.element vars) | not (null vars)] ++ [(2, genClosedLeaf ty)])
  where
    vars = [EVar n t | (n, t) <- Map.toList env, t == ty]

-- | The smallest closed expression of a type. Terminates on every
-- generated type because a constructor's fields only mention base types
-- or strictly earlier definitions.
genClosedLeaf :: Ty -> Gen Expr
genClosedLeaf ty = case ty of
  TInt -> ELit . LInt <$> Gen.integral (Range.linear 0 20)
  TBool -> ELit . LBool <$> Gen.bool
  TListInt -> pure (EListLit [])
  TAdt def -> do
    c <- Gen.element (NE.toList def.ctors)
    ECtor c.ctorName <$> traverse genClosedLeaf c.fields

genNode :: [Ty] -> Map Text Ty -> Int -> Ty -> Gen Expr
genNode univ env d ty = case ty of
  TInt ->
    Gen.choice
      [ EArith <$> Gen.element [Add, Sub, Mul] <*> sub TInt <*> sub TInt,
        call FnLen,
        call FnArea
      ]
  TBool ->
    Gen.choice
      [ ECmp <$> Gen.element [CLt, CGt, CGe, CLe] <*> sub TInt <*> sub TInt,
        do
          t <- Gen.element univ
          EEq t <$> sub t <*> sub t,
        ENot <$> sub TBool,
        call FnLt,
        call FnLte,
        call FnSameInt,
        call FnIsZero,
        call FnIsNil,
        call FnIsRed
      ]
  TListInt -> EListLit <$> Gen.list (Range.constant 1 3) (sub TInt)
  TAdt def -> do
    c <- Gen.element (NE.toList def.ctors)
    ECtor c.ctorName <$> traverse sub c.fields
  where
    sub = genExpr univ env (d - 1)
    call fn = ECall fn <$> traverse sub (fst (libFnSig fn))

-- | An expression whose root is never a bare variable. Used for @is@
-- right-hand sides and goal probes: @R is X@ with a syntactically
-- variable right-hand side widens to @any@ and would leave the fragment
-- under test.
genExprRoot :: [Ty] -> Map Text Ty -> Ty -> Gen Expr
genExprRoot univ env ty =
  Gen.choice [genClosedLeaf ty, genNode univ env 2 ty]

genSTerm :: Map Text Ty -> Int -> Ty -> Gen STerm
genSTerm env d ty = Gen.frequency (varAlt ++ structAlts)
  where
    vars = [SVar n t | (n, t) <- Map.toList env, t == ty]
    varAlt = [(2, Gen.element vars) | not (null vars)]
    sub = genSTerm env (d - 1)
    structAlts = case ty of
      TInt -> [(3, SLit . LInt <$> Gen.integral (Range.linear 0 20))]
      TBool -> [(3, SLit . LBool <$> Gen.bool)]
      TListInt ->
        (2, pure SNil)
          : [(3, SCons <$> sub TInt <*> sub TListInt) | d > 0]
      TAdt def ->
        [ ( 3,
            do
              c <- Gen.element (NE.toList def.ctors)
              SCtor c.ctorName <$> traverse (genSTerm env (max 0 (d - 1))) c.fields
          )
        ]

-- | 2–6 goal tells with closed arguments, plus 0–2 probes.
--
-- A goal that lands in a gap between every head pattern makes the whole
-- program dead weight — the rule bodies, and with them the assertions
-- that carry the property, never run. So the goal is biased towards
-- firing something, in two ways. Usually it instantiates one whole rule
-- head at once ('genRuleInstance'), which is the only way a join or an
-- aliased variable is reliably satisfied. The remaining tells are drawn
-- freely but still prefer constraint symbols some rule heads on, and for
-- each argument prefer an instance of a pattern a head matches /at that
-- exact position/. Every candidate is derived from the already generated
-- rules, so the bias costs nothing in shrink quality.
--
-- More than one tell also matters: most generated rules have two head
-- constraints, and a single-constraint store can never satisfy a join.
genGoal :: [Ty] -> NonEmpty Sig -> [Rule] -> Gen Goal
genGoal univ sigList rs = do
  seeded <- genSeeded
  extra <- Gen.int (Range.constant 1 3)
  t0 <- genTell
  ts <- replicateM extra genTell
  nProbes <- Gen.int (Range.constant 0 2)
  ps <- traverse genProbe [0 .. nProbes - 1]
  pure Goal {tells = t0 :| (ts ++ seeded), probes = ps}
  where
    -- The whole head of one rule, matched exactly. Dropping it
    -- occasionally keeps the free path — and the programs where nothing
    -- matches at all — represented.
    -- Drawn independently of the free tells: making the free count
    -- depend on how many seeded tells came back would mean shrinking the
    -- seed adds free tells, which is how a shrink plateaus.
    genSeeded
      | null rs = pure []
      | otherwise =
          Gen.frequency
            [ (4, NE.toList <$> (Gen.element rs >>= genRuleInstance)),
              (1, pure [])
            ]
    seeds = seedMap rs
    headSigs = [h.headSig | r <- rs, h <- ruleHeads r]
    genSigChoice =
      Gen.frequency
        ( [(3, Gen.element headSigs) | not (null headSigs)]
            ++ [(1, Gen.element (NE.toList sigList))]
        )
    genTell = do
      s <- genSigChoice
      args <-
        traverse (genArg s.sigName) (zip [0 ..] (NE.toList (sigArgTys s)))
      pure (s, args)
    genArg sn (i, t) = case Map.lookup (sn, i) seeds of
      Just ps@(_ : _) ->
        Gen.frequency
          [ (3, Gen.element ps >>= uncurry (patInstance Map.empty)),
            (1, genExprRoot univ Map.empty t)
          ]
      _ -> genExprRoot univ Map.empty t
    genProbe i = do
      t <- Gen.element univ
      e <- genExprRoot univ Map.empty t
      pure Probe {probeVar = "R" <> tshow i, probeTy = t, probeExpr = e}

-- | Instantiate a whole rule head into goal tells that match it.
--
-- Every pattern variable is given its value /once/, before any head is
-- read off, so a variable shared between two heads ('maybeAlias') comes
-- out equal in both. Left to independent draws that agreement is a
-- coincidence, and the rates show it: two-head rules fired 22% of the
-- time against 33% for single-head ones, and aliased rules only 12%.
genRuleInstance :: Rule -> Gen (NonEmpty (Sig, [Expr]))
genRuleInstance r = do
  binding <- traverse (\(n, t) -> (n,) <$> genClosedLeaf t) (ruleVars r)
  traverse (headInstance (Map.fromList binding)) (ruleHeadList r.ruleHead)

-- | One head of a rule, read off as a tell that matches it, under a
-- variable binding 'genRuleInstance' has already fixed.
headInstance :: Map Text Expr -> HeadC -> Gen (Sig, [Expr])
headInstance env h =
  (h.headSig,)
    <$> traverse
      (uncurry (patInstance env))
      (zip (NE.toList (sigArgTys h.headSig)) (NE.toList h.pats))

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
seedMap :: [Rule] -> Map (Text, Int) [(Ty, Pat)]
seedMap rs =
  Map.fromListWith
    (++)
    [ ((h.headSig.sigName, i), [(t, p)])
    | r <- rs,
      h <- ruleHeads r,
      (i, t, p) <- zip3 [0 ..] (NE.toList (sigArgTys h.headSig)) (NE.toList h.pats),
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
patInstance :: Map Text Expr -> Ty -> Pat -> Gen Expr
patInstance env ty p = case p of
  PVar n _ -> maybe (genClosedLeaf ty) pure (Map.lookup n env)
  PWild -> genClosedLeaf ty
  PLit l -> pure (ELit l)
  PNil -> pure (EListLit [])
  PCons h t -> consExpr <$> patInstance env TInt h <*> patInstance env TListInt t
  PCtor cn ps -> case ty of
    TAdt def -> case findCtor def cn of
      Just c
        | length c.fields == length ps ->
            ECtor cn <$> traverse (uncurry (patInstance env)) (zip c.fields ps)
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
            ++ T.unpack (renderTy ty)
        )

-- | Prepend an element to a list-typed instance. Every @list(int)@
-- instance 'patInstance' produces is an 'EListLit', so the other case
-- cannot arise: 'PNil' and 'genClosedLeaf' both give the empty list, a
-- nested 'PCons' is this function again, and a 'PVar' found in @env@
-- holds a value 'genRuleInstance' built with 'genClosedLeaf' at the
-- variable's own type. That last path is the one to re-check if the
-- binding 'genRuleInstance' hands down ever stops being closed leaves.
consExpr :: Expr -> Expr -> Expr
consExpr h t = case t of
  EListLit es -> EListLit (h : es)
  _ -> error "consExpr: list instance is not a list literal"

-- ---------------------------------------------------------------------------
-- Instrumentation and pruning (pure, deterministic, shrink-safe)
-- ---------------------------------------------------------------------------

-- | Everything a generated program needs before it is rendered.
-- Both passes are pure functions of the generated value, so applying
-- them after 'forAllWith' keeps shrinking well-behaved.
prepare :: Program -> Program
prepare = instrument . pruneTells

-- | Weave the runtime type assertions into every rule body.
--
-- Each rule opens with an @assert_τ(V)@ per pattern-bound head
-- variable: that is the store-typing invariant, i.e. that head matching
-- really did deliver values of the declared argument types. Each @is@
-- or @=@ binding is followed by an assertion on the variable it just
-- bound.
--
-- Goal probes are instrumented at render time ('renderQuery'), where
-- each @R is E@ picks up a @B is assert_τ(R)@ conjunct.
instrument :: Program -> Program
instrument prog = prog {rules = map instrumentRule prog.rules}

instrumentRule :: Rule -> Rule
instrumentRule r = r {body = headAsserts ++ concatMap expand r.body}
  where
    headAsserts = [BAssert n t | (n, t) <- ruleVars r]
    expand it = case it of
      BIs w t _ -> [it, BAssert w t]
      BUnify w t _ -> [it, BAssert w t]
      _ -> [it]

-- | Ceiling on the number of constraint instances a generated program
-- may derive.
maxInstances :: Integer
maxInstances = 200

-- | Per-stratum saturation point, so the bound computation itself
-- cannot produce astronomically large 'Integer's before deciding to
-- prune.
capLimit :: Integer
capLimit = 1_000_000

-- | Drop body tells until the derivation is provably small.
--
-- Stratification (see 'Note [Termination]') guarantees termination but
-- not speed: each stratum can hold up to the /product/ of the instance
-- counts of the strata above it, so a four-stratum program can derive
-- six figures' worth of constraints and blow the 60s per-test budget.
--
-- 'derivationBound' computes that recurrence exactly (it is a genuine
-- upper bound: a rule fires at most once per tuple of head instances,
-- by propagation history for propagation rules and by consumption for
-- the others). While the bound is over 'maxInstances', the tells of the
-- last rule that still has any are dropped. Being a deterministic
-- function of the generated program, this composes with shrinking.
pruneTells :: Program -> Program
pruneTells prog
  | derivationBound prog <= maxInstances = prog
  | otherwise = case lastTellingRule prog.rules of
      Nothing -> prog
      Just i -> pruneTells prog {rules = dropTellsAt i prog.rules}
  where
    lastTellingRule rs =
      case [i | (i, r) <- zip [0 :: Int ..] rs, any isTell r.body] of
        [] -> Nothing
        is -> Just (last is)
    dropTellsAt i rs =
      [ if j == i then r {body = filter (not . isTell) r.body} else r
      | (j, r) <- zip [0 :: Int ..] rs
      ]

-- | Upper bound on the constraint instances a program can ever create.
--
-- Because a body may only tell strata strictly below its head, the cap
-- at a stratum depends only on strata above it, so one top-down fold
-- suffices. At stratum @s@ the instances are the goal's own tells there
-- plus, for each rule whose heads all sit above @s@, its firings times
-- the tells it makes to @s@. Firings are over-approximated by the
-- product of the head strata's caps — a rule fires at most once per
-- tuple of head instances, by propagation history for a propagation
-- rule and by consumption for the other two — which ignores the
-- id-distinctness discount and so can only overshoot.
--
-- Caps saturate at 'capLimit' so that a program headed for an
-- astronomical bound does not build an astronomical 'Integer' before
-- 'pruneTells' notices. 'capLimit' is far above 'maxInstances', so
-- saturation can never hide a program that needed pruning.
derivationBound :: Program -> Integer
derivationBound prog = sum (Map.elems caps)
  where
    top = maximum [s.stratum | s <- NE.toList prog.sigs]
    caps = foldl step Map.empty [top, top - 1 .. 0]
    step acc s = Map.insert s (min capLimit (goalCount s + fromRules acc s)) acc
    goalCount s =
      toInteger (length [() | (sig, _) <- NE.toList prog.goal.tells, sig.stratum == s])
    fromRules acc s =
      sum [firings acc r * tellsTo r s | r <- prog.rules, minHeadStratum r > s]
    firings acc r =
      product [Map.findWithDefault 0 h.headSig.stratum acc | h <- ruleHeads r]
    tellsTo r s =
      toInteger (length [() | BTell sig _ <- r.body, sig.stratum == s])

-- ---------------------------------------------------------------------------
-- Rendering
-- ---------------------------------------------------------------------------

renderTy :: Ty -> Text
renderTy ty = case ty of
  TInt -> "int"
  TBool -> "bool"
  TListInt -> "list(int)"
  TAdt def -> def.adtName

renderAnn :: Ann -> Text
renderAnn a = if a.erased then "any" else renderTy a.declared

renderLit :: Lit -> Text
renderLit l = case l of
  LInt n -> tshow n
  LBool True -> "true"
  LBool False -> "false"

args_ :: [Text] -> Text
args_ ts = "(" <> T.intercalate ", " ts <> ")"

-- | A constructor application, collapsing the nullary case to a bare
-- atom (which is how a 0-arity constructor is written in source).
applied :: Text -> [Text] -> Text
applied f [] = f
applied f as = f <> args_ as

renderModule :: Program -> Text
renderModule prog =
  T.unlines
    ( [ ":- module(gen).",
        ":- use_module(library(prelude)).",
        ""
      ]
        ++ concatMap renderAdt (fixedAdts ++ prog.adts)
        ++ [preamble]
        ++ [renderConstraintDecl prog.sigs, ""]
        ++ map renderRule prog.rules
    )

-- | A generated type declaration plus its runtime assertion predicate.
renderAdt :: AdtDef -> [Text]
renderAdt def =
  [ ":- chr_type "
      <> def.adtName
      <> " ---> "
      <> T.intercalate " ; " (map renderCtorDecl (NE.toList def.ctors))
      <> ".",
    ":- function " <> assertFn (TAdt def) <> "(" <> def.adtName <> ") -> bool."
  ]
    ++ map renderAssertEq (NE.toList def.ctors)
    ++ [""]
  where
    renderCtorDecl c = applied c.ctorName (map renderTy c.fields)
    renderAssertEq c =
      let vars = ["F" <> tshow i | i <- [0 .. length c.fields - 1]]
          checks =
            T.intercalate
              ", "
              (zipWith (\t v -> assertFn t <> "(" <> v <> ")") c.fields vars)
          guardPart = if null c.fields then "" else " | " <> checks
       in assertFn (TAdt def)
            <> "("
            <> applied c.ctorName vars
            <> ")"
            <> guardPart
            <> " -> true."

renderConstraintDecl :: NonEmpty Sig -> Text
renderConstraintDecl ss =
  ":- chr_constraint "
    <> T.intercalate ", " (map one (NE.toList ss))
    <> "."
  where
    one s = s.sigName <> args_ (map renderAnn (NE.toList s.argAnns))

renderRule :: Rule -> Text
renderRule r =
  r.ruleName
    <> " @ "
    <> headText
    <> " "
    <> guardText
    <> bodyText
    <> "."
  where
    headText = case r.ruleHead of
      HSimplify hs -> renderHeads hs <> " <=>"
      HPropagate hs -> renderHeads hs <> " ==>"
      HSimpagate ks rs -> renderHeads ks <> " \\ " <> renderHeads rs <> " <=>"
    renderHeads hs = T.intercalate ", " (map renderHeadC (NE.toList hs))
    guardText
      | null r.guards = ""
      | otherwise = T.intercalate ", " (map renderExpr r.guards) <> " | "
    bodyText
      | null r.body = "true"
      | otherwise = T.intercalate ", " (map renderBodyItem r.body)

renderHeadC :: HeadC -> Text
renderHeadC h = h.headSig.sigName <> args_ (map renderPat (NE.toList h.pats))

renderPat :: Pat -> Text
renderPat p = case p of
  PVar n _ -> n
  PWild -> "_"
  PLit l -> renderLit l
  PCtor c ps -> applied c (map renderPat ps)
  PNil -> "[]"
  PCons h t -> renderListLike (renderPat h) (renderPat t) (t == PNil)

-- | Render a cons cell as list syntax, given the head and tail already
-- rendered and whether the tail is the empty list. A spine ending in
-- @[]@ prints as @[a, b]@; anything else keeps the tail after a bar,
-- @[a | T]@.
--
-- Splicing the tail's own brackets is safe because a cons tail is
-- always list-typed, so it renders as @[]@, a @[…]@ list, a variable,
-- or @_@ — never as something unrelated that happens to end in @]@.
renderListLike :: Text -> Text -> Bool -> Text
renderListLike hd tl tailIsNil
  | tailIsNil = "[" <> hd <> "]"
  | Just inner <- T.stripPrefix "[" tl,
    Just body <- T.stripSuffix "]" inner,
    not (T.null body) =
      "[" <> hd <> ", " <> body <> "]"
  | otherwise = "[" <> hd <> " | " <> tl <> "]"

renderExpr :: Expr -> Text
renderExpr e = case e of
  ELit l -> renderLit l
  EVar n _ -> n
  EListLit es -> "[" <> T.intercalate ", " (map renderExpr es) <> "]"
  ECtor c es -> applied c (map renderExpr es)
  EArith op a b -> infix_ (arithOp op) a b
  ECmp op a b -> infix_ (cmpOp op) a b
  EEq _ a b -> infix_ "==" a b
  ENot a -> "not(" <> renderExpr a <> ")"
  ECall fn es -> libFnName fn <> args_ (map renderExpr es)
  where
    infix_ o a b = "(" <> renderExpr a <> " " <> o <> " " <> renderExpr b <> ")"
    arithOp op = case op of
      Add -> "+"
      Sub -> "-"
      Mul -> "*"
    cmpOp op = case op of
      CLt -> "<"
      CGt -> ">"
      CGe -> ">="
      CLe -> "=<"

renderSTerm :: STerm -> Text
renderSTerm t = case t of
  SLit l -> renderLit l
  SVar n _ -> n
  SNil -> "[]"
  SCons h tl -> renderListLike (renderSTerm h) (renderSTerm tl) (tl == SNil)
  SCtor c ts -> applied c (map renderSTerm ts)

renderBodyItem :: BodyItem -> Text
renderBodyItem it = case it of
  BTell s es -> s.sigName <> args_ (map renderExpr es)
  BIs w _ e -> w <> " is " <> renderExpr e
  BUnify w _ st -> w <> " = " <> renderSTerm st
  BAssert n ty -> assertFn ty <> "(" <> n <> ")"

-- | The query: the goal tells (module-qualified, as every goal in the
-- golden suite is), then each probe followed by its runtime type
-- assertion.
renderQuery :: Program -> Text
renderQuery prog =
  T.intercalate ", " (map tell_ (NE.toList prog.goal.tells) ++ probeParts) <> "."
  where
    tell_ (s, es) = "gen:" <> s.sigName <> args_ (map renderExpr es)
    probeParts =
      concat
        [ [ p.probeVar <> " is " <> renderExpr p.probeExpr,
            "B" <> tshow i <> " is " <> assertFn p.probeTy <> "(" <> p.probeVar <> ")"
          ]
        | (i, p) <- zip [0 :: Int ..] prog.goal.probes
        ]

-- ---------------------------------------------------------------------------
-- Conformance of a returned binding to its static type
-- ---------------------------------------------------------------------------

-- | The name a runtime 'Term' carries, without its module. Answers come
-- back qualified (@gen:k0@, @prelude:[]@) or bare depending on how the
-- value was built, so only the final component is compared.
baseOf :: Name -> Text
baseOf n = case n of
  Unqualified t -> t
  Qualified _ t -> t

-- | Does a returned binding structurally inhabit its static type?
--
-- This is the Haskell-side half of the oracle; the in-language
-- @assert_τ@ calls are the other half. They check the same thing from
-- opposite sides of the runtime boundary.
conforms :: Ty -> Term -> Bool
conforms ty t = case ty of
  TInt -> case t of
    IntTerm _ -> True
    _ -> False
  TBool -> case t of
    CompoundTerm n [] -> baseOf n == "true" || baseOf n == "false"
    _ -> False
  TListInt -> case t of
    CompoundTerm n [] -> baseOf n == "[]"
    CompoundTerm n [h, tl] ->
      baseOf n == "." && conforms TInt h && conforms TListInt tl
    _ -> False
  TAdt def -> case t of
    CompoundTerm n as -> case findCtor def (baseOf n) of
      Just c -> length c.fields == length as && and (zipWith conforms c.fields as)
      Nothing -> False
    _ -> False

-- ---------------------------------------------------------------------------
-- The property
-- ---------------------------------------------------------------------------

prop_soundness :: Property
prop_soundness = withTests 100 $ property $ do
  raw <- forAllWith (T.unpack . showProgram) genProgram
  let prog = prepare raw
      src = renderModule prog
      query = renderQuery prog
  coverShape prog
  cp <- case compileModules False [("gen.chr", src)] of
    Left err -> annotate ("compile error: " ++ displayMsg (err :: Error)) >> failure
    Right (cp, ws) -> do
      mapM_ (annotate . ("compile warning: " ++) . displayMsg) ws
      pure cp
  tc <- evalIO (typeCheckProgram cp.desugaredProgram)
  mapM_ (annotate . ("typecheck warning: " ++) . displayMsg) tc.warnings
  unless (null tc.errors) $ do
    mapM_ (annotate . ("type error: " ++) . displayMsg) tc.errors
    failure
  outcome <-
    evalIO
      ( try @SomeException
          (runProgramWithQuery cp (baseHostCallRegistry <> metaHostCallRegistry) query)
      )
  bindings <- case outcome of
    Left exc -> annotate (describeException exc) >> failure
    Right bs -> pure bs
  mapM_ (checkProbe bindings) prog.goal.probes
  where
    showProgram p =
      let q = prepare p in renderModule q <> "\n?- " <> renderQuery q <> "\n"

-- | Assert that the generated programs are structurally rich enough for
-- the property to mean anything.
--
-- Without this the property can go quietly vacuous: a size-scaled
-- 'Range.linear' whose span is 1 or 2 truncates to its lower bound over
-- most of hedgehog's size sweep, which once left the first ~40% of
-- every run with a single-constraint store, no guards, no body tells
-- and no probes — nothing that could observe a soundness violation.
--
-- The floors are therefore set /between/ the current rates and the
-- rates that same degeneration would produce, not merely somewhere
-- above zero — a floor of 20% would have let the original defect
-- through. Measured rates (n = 3000) against the rate the degeneration
-- would give:
--
-- > join two heads  85% (would be 53%)   floor 65
-- > body tell       52% (would be 37%)   floor 30
-- > body bind       82% (would be 53%)   floor 62
-- > guard           83% (would be 52%)   floor 62
-- > probe           70% (would be 39%)   floor 45
-- > algebraic type  66% (would be 41%)   floor 46
--
-- Five of these six events are decided by generators the goal- and
-- guard-seeding of 'Note [Firing rates]' does not touch, so the rates
-- above are as first measured. The exception is the body-tell label,
-- which reads the /prepared/ program and so depends on how much
-- 'pruneTells' dropped, and hence on the goal size that work widened;
-- measured, the extra pruning is nil and the rate is unchanged.
-- Re-measuring all six after that work reproduced them to within two
-- points.
--
-- Only the body-tell floor is loose: its rate sits near 50%, where the
-- binomial spread at @withTests 100@ is widest, so a discriminating
-- floor would flake. The other five bind, and the degeneration trips
-- all of them at once.
--
-- What these do /not/ measure is whether a rule actually fires — that
-- is a runtime fact, and nothing observable crosses back from the CHR
-- session. It is measured out of band by splicing a body that always
-- raises (@Z = 1, Z = 2@) into the rules of interest and counting the
-- runs that then fail; see 'Note [Firing rates]'. Redo that measurement
-- rather than trusting the labels below if the generator's firing
-- behaviour is ever in question.
coverShape :: Program -> PropertyT IO ()
coverShape prog = do
  cover 65 "a rule joins two head constraints" (any ((> 1) . length . ruleHeads) rs)
  cover 30 "a rule body tells a constraint" (any (any isTell . (.body)) rs)
  cover 62 "a rule body binds a variable" (any (any isBind . (.body)) rs)
  cover 62 "a rule has a guard" (any (not . null . (.guards)) rs)
  cover 45 "the goal has a probe" (not (null prog.goal.probes))
  cover 46 "the program declares an algebraic type" (not (null prog.adts))
  where
    rs = prog.rules
    isBind it = case it of
      BIs {} -> True
      BUnify {} -> True
      _ -> False

-- | Classify a failure so the counterexample says which stage of the
-- claim broke. A 'TypeErrors' here comes from the query type-check
-- inside @prepareQuery@, not from running: the program itself was
-- checked separately and cleanly at that point.
describeException :: SomeException -> String
describeException exc = case fromException exc of
  Just (TypeErrors errs) ->
    "goal rejected by the query type-check: " ++ unlines (map displayMsg errs)
  Just (err :: Error) -> "run failed: " ++ displayMsg err
  Nothing -> "unexpected exception: " ++ show exc

checkProbe :: Map Text Term -> Probe -> PropertyT IO ()
checkProbe bindings p = case Map.lookup p.probeVar bindings of
  Nothing ->
    annotate ("probe " ++ T.unpack p.probeVar ++ " has no binding") >> failure
  Just t
    | conforms p.probeTy t -> pure ()
    | otherwise -> do
        annotate
          ( "probe "
              ++ T.unpack p.probeVar
              ++ " : "
              ++ T.unpack (renderTy p.probeTy)
              ++ " is bound to a value outside that type: "
              ++ show t
          )
        failure

tests :: TestTree
tests =
  testGroup
    "TypeSoundness"
    [ testProperty
        "fully-typed programs run without type errors"
        prop_soundness
    ]
