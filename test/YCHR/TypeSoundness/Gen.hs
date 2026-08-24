{-# LANGUAGE OverloadedStrings #-}

-- | The generator: random well-typed programs in the core AST of
-- "YCHR.TypeSoundness.Types".
module YCHR.TypeSoundness.Gen (genProgram) where

import Control.Monad (foldM, replicateM)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Hedgehog (Gen)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import YCHR.TypeSoundness.Preamble
import YCHR.TypeSoundness.Types

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
-- tests nothing while still counting towards @coverShape@'s guard
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
-- (see @Note [Termination]@ in "YCHR.TypeSoundness.Instrument").
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
