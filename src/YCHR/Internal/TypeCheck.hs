{-# LANGUAGE OverloadedStrings #-}

-- | Haskell driver for the YCHR type checker.
--
-- Walks the desugared AST and feeds constraints into a CHR session
-- running the pre-compiled type-checker program. The type checker
-- catches type inconsistencies statically, while remaining optional:
-- programs without type annotations are accepted without errors.
--
-- == @any@ never binds; declaration positions stamp
--
-- The CHR-side @tc_unify(T1, T2, Ctx)@ rules implement the meet
-- table of @docs/reference/type-system.md@ §Type states: @any@ on
-- either side is only checked against — it never binds a type
-- variable, in either direction. A source variable is typed @any@
-- only when a declaration says so, and that is enforced here in the
-- driver, statically: before a rule's (or single-signature
-- equation's) slots are allocated, 'headVarSkeletons' /
-- 'paramVarSkeletons' compute each variable's slot shape from its
-- declaration positions. A position every source leaves @any@ is
-- allocated as the literal @any@ atom; a position some source makes
-- concrete is allocated as a fresh flexible variable, which that
-- solid source binds — in any emission order, since the @any@
-- positions bind nothing.
--
-- This is a per-/position/ judgement, not a per-variable one
-- ('TypeSkeleton'). A variable declared @list(any)@ in one head and
-- @list(int)@ in another gets the slot @list(β)@: the @any@ source
-- meets β and binds nothing, the @int@ source binds it, and the two
-- HNF halves merge to @list(int)@ either way round. Allocating the
-- whole slot flexible instead would let the first head bind it to
-- @list(any)@ entire, and the merge would then compare an @any@ that
-- has nowhere left to go.
--
-- Invariant: a slot equal to the @any@ atom can only originate from
-- this driver-side stamping; no CHR rule binds a var to @any@.
-- 'checkFunStmt' relies on this to tell "declared @any@" (whose
-- rebound local keeps @any@) apart from "still flexible" (which
-- takes a fresh slot bound to the RHS type).
--
-- == Guard-derived evidence
--
-- A guard whose operational success entails a typing fact tells that
-- fact alongside its ordinary checks: @ev_unify@ for a type
-- predicate, @check_guard_match@ for an HNF constructor match,
-- @eq_unify@ for an HNF equality. The fact may pin a rigid type
-- variable — the one sanctioned exception to the meet table's rigid
-- rows — and is inert at a flexible or @any@ slot, so evidence can
-- only ever accept more programs. Where it contradicts a known type
-- the guard can never succeed, and the unit draws the
-- inaccessible-branch warning rather than an error. Because
-- evidence is scoped to the positions that run after the guard,
-- 'checkGuards' is called between the head\/parameter checks and
-- the body\/RHS checks, and threads each match's field slots
-- forward to the extractions that follow it.
--
-- @eq_unify@ is the one that is not purely evidence: HNF splits a
-- repeated source variable in two, and the two halves are one
-- variable, so a still-flexible half /binds/ to the other's type
-- (the declaration-source merge of §Type states) instead of staying
-- inert. See its rule block in @typechecker.chr@.
--
-- Rigid type variables exist at both kinds of implementation site:
-- a function's declared type parameters while checking its
-- equations, and a typed polymorphic constraint's while checking a
-- rule whose head mentions it — freshly per head occurrence, since
-- the store may hold any mix of instances.
module YCHR.Internal.TypeCheck
  ( TypeCheckError (..),
    TypeCheckWarning (..),
    TypeCheckResult (..),
    typeCheckProgram,
    typeCheckGoals,
  )
where

import Control.Monad (foldM, replicateM, when, zipWithM_)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, put)
import Data.List qualified as List
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Compile.Names (vmName)
import YCHR.Internal.Constructors (buildConAlias, buildConMap)
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Diagnostic (Diagnostic (..))
import YCHR.Internal.PExpr (PExpr (Atom))
import YCHR.Internal.Parsed (AnnP (..), SourceLoc (..))
import YCHR.Internal.Resolved qualified as R
import YCHR.Internal.Runtime.Interpreter (baseHostCallRegistry)
import YCHR.Internal.Runtime.Monad (Chr)
import YCHR.Internal.Runtime.Registry (fromValueList, valueList)
import YCHR.Internal.Runtime.Session (tellConstraint, withCHR)
import YCHR.Internal.Runtime.Types (Value (..))
import YCHR.Internal.Runtime.Var (deref, newVar)
import YCHR.Internal.TypeCheck.Compiled (typeCheckerProgram)
import YCHR.Internal.TypeCheck.Error
  ( TypeCheckError (..),
    TypeCheckResult (..),
    TypeCheckWarning (..),
  )
import YCHR.Internal.Types
  ( BoundSig (..),
    DataConstructor (..),
    HeadArg (..),
    Name (..),
    Term (..),
    TypeDefinition (..),
    TypeExpr (..),
    flattenName,
    headArgToTerm,
    headConstraintToConstraint,
    typeConstructors,
  )
import YCHR.Internal.Types qualified as Types
import YCHR.Internal.VM qualified as VM

-- | Flatten a 'Name' to the same single-atom form used by the runtime
-- (see 'YCHR.Internal.Compile.Names.vmName'). Required so CHR-side constraints
-- emitted from this Haskell driver match what compiled CHR rules
-- produce after the renamer canonicalizes data-constructor names.
runtimeName :: Name -> Text
runtimeName name = let VM.Name t = vmName name in t

-- | Runtime functor name of a constructor declared in the
-- @'$typechecker'@ module — base types (@int@), record/tag
-- constructors (@sig@), and compound shapes (@tcon@, @fun@) alike.
-- The renamer canonicalizes such names to @$typechecker:<n>@; the
-- runtime functor symbol is the flattened form @$typechecker__<n>@.
-- Used as the functor argument of 'VTerm' values this Haskell driver
-- builds, of any arity.
tcAtom :: Text -> Text
tcAtom n = "$typechecker__" <> n

-- | A base type (@int@, @float@, @string@, @any@) as a runtime
-- 'Value'. 0-arity compounds collapse to 'VAtom' at the runtime
-- layer; 'BMatchTerm' accepts 'VAtom' for arity-0 dispatch, so this
-- matches the shape compiled head patterns produce.
--
-- Callers pass the /source-level/ name; the @ty_@ prefix of the CHR
-- constructor is added here and stripped again by 'displayTypeAtom',
-- so neither side of the driver has to spell the internal name. See
-- the @ty@ declaration in @typechecker.chr@ for why the prefix exists.
tcCon0 :: Text -> Value
tcCon0 n = VAtom (tcBaseAtom n)

-- | Runtime functor name of a base-type constructor.
tcBaseAtom :: Text -> Text
tcBaseAtom n = tcAtom ("ty_" <> n)

-- ---------------------------------------------------------------------------
-- Type-check environment and context
-- ---------------------------------------------------------------------------

-- | Program-wide immutable environment, shared via 'Reader'.
data TypeCheckEnv = TypeCheckEnv
  { -- | Map from constructor name to its parent type definition and constructor info.
    conMap :: Map Name (TypeDefinition, DataConstructor),
    -- | Resolves a use-site unqualified name to its declaration's qualified
    -- name when exactly one constructor matches. Constructors are name-only
    -- in YCHR's type system (arity is not part of their identity), so this
    -- is keyed by name alone — wrong-arity uses are diagnosed separately by
    -- 'validateConstructorArities'. Ambiguous names (declared in more than
    -- one module) are omitted so the canonicalization falls through and the
    -- lookup behaves as if the name were unknown.
    conAlias :: Map Text Name,
    -- | Declared bounds for every bounded @:- chr_constraint@. Used
    -- by 'checkRule' to allocate per-head-occurrence ambient
    -- signatures and emit the head-occurrence bound checks
    -- (§Bounded constraints §Use sites).
    constraintBoundsEnv :: Map Types.ConstraintKey [BoundSig],
    -- | Declared argument types for every @:- chr_constraint@ —
    -- the same data 'tellConstraintSigs' tells to the CHR program.
    -- Pulled in here so 'checkRule' can encode a bounded
    -- constraint's primary signature against the same σ as its
    -- ambient signatures.
    constraintTypesEnv :: Map Types.ConstraintKey [TypeExpr],
    -- | Bounds declared on every bounded function, keyed by runtime
    -- name and arity. Consulted at call sites so the callee's own
    -- bound checks are emitted with by-value candidate lists (the
    -- CHR discharge rules are pure and cannot gather candidates
    -- across the store).
    functionBoundsEnv :: Map AmbientKey [BoundSig],
    -- | Declared signatures per runtime function name — all arities
    -- mixed, mirroring what the CHR side's function_sig(s) see.
    -- Untyped functions contribute their synthesized all-@any@
    -- signature. Used to encode the declared-signature candidates of
    -- a bound's named function at @check_bound@ emission.
    functionSigsEnv :: Map Text [([TypeExpr], TypeExpr)]
  }

-- | Key of the ambient-signature and function-bounds maps: functions
-- are arity-overloadable, so a bound naming @g/1@ must not capture
-- calls to @g/2@.
data AmbientKey = AmbientKey
  { ambName :: Text,
    ambArity :: Int
  }
  deriving (Show, Eq, Ord)

-- | Per-rule or per-equation checking context, passed explicitly
-- because it changes at each scope boundary.
data CheckCtx = CheckCtx
  { -- | Maps source variable names to fresh type variables (Values).
    varTypes :: Map Text Value,
    -- | Human-readable label for error messages (e.g., "rule trans").
    label :: Maybe Text,
    -- | Source location of the current AST section.
    loc :: SourceLoc,
    -- | Original PExpr for the current AST section.
    origin :: PExpr,
    -- | Ambient signatures contributed by the enclosing bounded
    -- declarations. Keyed by the runtime name of the bound's target
    -- function. Each entry is the list of @sig(args, ret)@ values
    -- visible at every call site in this scope; the list has one
    -- entry per relevant bound currently active. Empty for code
    -- outside any bounded scope.
    --
    -- A call to a function whose name appears in this map is emitted
    -- as @check_function_use_with_ambient@; calls to other functions
    -- use the ordinary @check_function_use@ path. See the CHR
    -- @check_with_ambient_*@ rules in
    -- @typechecker\/typechecker.chr@.
    ambientSigs :: Map AmbientKey [Value],
    -- | The checking unit this context belongs to — one rule, one
    -- function equation, or one top-level goal (spec §Type Checking
    -- Procedure). Every 'CtxHandle' allocated from this context
    -- records it, so a diagnostic decoded on the way out knows which
    -- unit produced it. Warning suppression is per unit: a unit that
    -- reports an error omits its warnings.
    unitId :: UnitId
  }

-- | Detect data constructors declared in more than one type definition.
-- Two constructors collide when they share a 'Qualified m n' after
-- renaming, regardless of arity (the type checker keys constructor
-- lookups on name only — see 'buildConMap' and the CHR-side
-- @delegate_guard_getarg@ / @constructor_match@ rules in
-- @typechecker/typechecker.chr@). Without this check, 'Map.fromList'
-- in 'buildConMap' would silently drop the earlier declaration.
detectDuplicateConstructors :: [TypeDefinition] -> [Diagnostic TypeCheckError]
detectDuplicateConstructors tds =
  [ Diagnostic
      Nothing
      ( AnnP
          (DuplicateConstructor (flattenName name) (map dropLoc sortedByLoc))
          firstLoc
          (Atom firstTypeName)
      )
  | (name, decls) <- Map.toList grouped,
    length decls > 1,
    let sortedByLoc = List.sortOn (\(_, _, l) -> (l.file, l.line, l.col)) decls,
    (firstTypeName, _, firstLoc) : _ <- [sortedByLoc]
  ]
  where
    dropLoc (tn, ar, _) = (tn, ar)
    grouped =
      Map.fromListWith
        (++)
        [ (dc.conName, [(flattenName td.name, length dc.conArgs, td.loc)])
        | td <- tds,
          dc <- typeConstructors td
        ]

-- | Map a use-site constructor name to its declared, qualified form when a
-- unique match exists. 'Qualified' names pass through unchanged;
-- 'Unqualified' names are resolved through 'conAlias'. When no unique
-- match exists the name is returned as-is.
canonicalizeConName :: TypeCheckEnv -> Name -> Name
canonicalizeConName _ name@(Qualified _ _) = name
canonicalizeConName env (Unqualified n) =
  Map.findWithDefault (Unqualified n) n env.conAlias

-- | True when @name@ is a known data constructor and its declared arity
-- matches @useArity@. Wrong-arity uses are diagnosed by
-- 'validateConstructorArities'; this predicate gates the @check_constructor_use@
-- emissions so we don't pile a spurious tcon mismatch on top of the
-- arity-mismatch error.
knownConstructorWithArity :: TypeCheckEnv -> Name -> Int -> Bool
knownConstructorWithArity env name useArity =
  case Map.lookup name env.conMap of
    Just (_, dc) -> length dc.conArgs == useArity
    Nothing -> False

-- | Number of type parameters of the algebraic type a data
-- constructor belongs to. Zero for an unknown constructor, which the
-- callers gate on anyway.
parentTypeArity :: TypeCheckEnv -> Name -> Int
parentTypeArity env name =
  case Map.lookup name env.conMap of
    Just (td, _) -> length td.typeVars
    Nothing -> 0

-- | Safe list indexing.
listAt :: Int -> [a] -> Maybe a
listAt i xs
  | i < 0 = Nothing
  | otherwise = case drop i xs of
      (x : _) -> Just x
      [] -> Nothing

-- | Identity of a checking unit: one rule, one function equation, or
-- one top-level goal. Allocated fresh at each unit boundary, including
-- for each equation of a function (extension equations included) and
-- for each per-signature attempt session of a class function, so units
-- that happen to share a source location still have distinct
-- identities.
newtype UnitId = UnitId Int
  deriving (Eq, Ord)

-- | Source-location info recovered from a CHR-side @Ctx@ handle.
data CtxInfo = CtxInfo
  { label :: Maybe Text,
    loc :: SourceLoc,
    origin :: PExpr,
    -- | Named @unit@ rather than @unitId@ so that record updates of
    -- 'CheckCtx.unitId' stay unambiguous under @DuplicateRecordFields@.
    unit :: UnitId
  }

-- | Opaque handle into 'CtxMap'. Travels through the CHR program as
-- the @Ctx@ argument of every @check_*@ constraint and comes back in
-- 'decodeError' to recover the originating source location.
newtype CtxHandle = CtxHandle Int
  deriving (Eq, Ord)

-- | Materialize a 'CtxHandle' as the 'Value' the CHR program sees.
ctxHandleValue :: CtxHandle -> Value
ctxHandleValue (CtxHandle n) = VInt (fromIntegral n)

-- | Map from 'CtxHandle' to the originating source location.
type CtxMap = Map CtxHandle CtxInfo

-- | Holds the source-location info for every allocated 'CtxHandle'
-- together with the rigid-type-var counter. Threaded as a single
-- 'State' effect so the counters and the location map stay in step.
data CtxStore = CtxStore
  { nextCtxHandle :: !CtxHandle,
    ctxMap :: !CtxMap,
    -- | Fresh-id counter for rigid type variables. Each rigid tvar
    -- is encoded as the runtime term @rigid(Cell, N)@ where @N@ is a
    -- globally unique integer from this counter (and @Cell@ the pin
    -- slot allocated alongside it, see 'freshRigidTypeVar'); distinct
    -- rigid identities therefore never accidentally unify.
    nextRigidId :: !Int,
    -- | Fresh-id counter for checking units (see 'UnitId').
    nextUnitId :: !Int,
    -- | Errors this session found in Haskell rather than through a
    -- CHR rule, tagged with the unit they belong to (most recent
    -- first). Kept here, rather than returned from a whole-program
    -- pre-pass, so warning suppression sees them.
    hsDiags :: [(UnitId, Diagnostic TypeCheckError)]
  }

emptyCtxStore :: CtxStore
emptyCtxStore =
  CtxStore
    { nextCtxHandle = CtxHandle 0,
      ctxMap = Map.empty,
      nextRigidId = 0,
      nextUnitId = 0,
      hsDiags = []
    }

-- | Internal monad of the type-check driver: a 'ReaderT' carrying the
-- program-wide environment over a 'StateT' for the context store,
-- both sitting above the 'Chr' session monad.
type TC = ReaderT TypeCheckEnv (StateT CtxStore Chr)

-- | Lift a 'Chr' action into 'TC'.
chrOp :: Chr a -> TC a
chrOp = lift . lift

-- | Read the context store.
getStore :: TC CtxStore
getStore = lift get

-- | Replace the context store.
putStore :: CtxStore -> TC ()
putStore = lift . put

-- | Allocate a fresh checking-unit identity. Called once at each unit
-- boundary; the resulting 'UnitId' goes into the unit's 'CheckCtx'
-- and from there into every 'CtxHandle' the unit allocates.
freshUnitId :: TC UnitId
freshUnitId = do
  store <- getStore
  let n = store.nextUnitId
  putStore store {nextUnitId = n + 1}
  pure (UnitId n)

-- | Record Haskell-side errors against the unit they were found in.
recordHsDiags :: UnitId -> [Diagnostic TypeCheckError] -> TC ()
recordHsDiags unit diags = do
  store <- getStore
  putStore store {hsDiags = reverse [(unit, d) | d <- diags] ++ store.hsDiags}

-- | Allocate a fresh rigid type variable. Distinct allocations get
-- distinct identities; the only way two rigid tvars unify is if
-- they share the same identity (typically via the same entry in a
-- @tvars@ map shared between the declaration's parameter encoding
-- and its ambient bound signatures).
--
-- The first field is the skolem's /pin slot/: a fresh unbound
-- variable that only guard-derived evidence may bind (@ev_unify@ /
-- @check_guard_match@ CHR-side). Because every occurrence of the
-- skolem shares this one term, pinning it once makes every occurrence
-- behave as the pinned type. See the @rigid@ note in
-- @typechecker/typechecker.chr@ for the copy_term invariant.
freshRigidTypeVar :: TC Value
freshRigidTypeVar = do
  store <- getStore
  let n = store.nextRigidId
  putStore store {nextRigidId = n + 1}
  cell <- chrOp newVar
  pure (VTerm (tcAtom "rigid") [cell, VInt (fromIntegral n)])

-- | Allocate fresh rigid type variables for each unique type variable
-- name. Mirrors 'freshTypeVarsForDecl' but uses rigid identities;
-- intended for a polymorphic function's own equation-body scope, where
-- the enclosing tvars must enforce a structural match (so calls to
-- overloaded operations at those tvars fail without a covering
-- @requiring@ clause).
--
-- Lives in 'TC' rather than 'Chr' because the rigid-id counter is in
-- 'CtxStore' (the @StateT@ layer); 'freshTypeVarsForDecl' has no such
-- counter so it can live in 'Chr' directly.
freshRigidTypeVarsForDecl :: [Text] -> TC (Map Text Value)
freshRigidTypeVarsForDecl vars = do
  let unique = Set.toList (Set.fromList vars)
  pairs <- mapM (\v -> (v,) <$> freshRigidTypeVar) unique
  pure (Map.fromList pairs)

-- ---------------------------------------------------------------------------
-- Main entry point
-- ---------------------------------------------------------------------------

-- | Type-check a desugared program.
--
-- Returns a list of diagnostics for every type inconsistency found.
-- An empty list means the program is well-typed (or has no type
-- annotations — unannotated programs are accepted without errors
-- because missing types default to @any@).
--
-- Type errors prevent compilation from proceeding; the caller is
-- responsible for aborting when the list is non-empty.
-- | Assemble the read-only environment shared by program and goal
-- checking.
buildTypeCheckEnv :: D.Program -> TypeCheckEnv
buildTypeCheckEnv prog =
  TypeCheckEnv
    { conMap = buildConMap prog.typeDefinitions,
      conAlias = buildConAlias prog.typeDefinitions,
      constraintBoundsEnv = prog.constraintBounds,
      constraintTypesEnv = prog.constraintTypes,
      functionBoundsEnv =
        Map.fromList
          [ (AmbientKey (runtimeName (Types.qualifiedToName f.name)) f.arity, f.requiring)
          | f <- prog.functions,
            not (null f.requiring)
          ],
      functionSigsEnv =
        Map.fromListWith
          (flip (++))
          [ (runtimeName (Types.qualifiedToName f.name), effectiveSigs f)
          | f <- prog.functions
          ]
    }
  where
    anyTE = TypeCon (Unqualified "any") []
    effectiveSigs f = case f.signatures of
      [] -> [(replicate f.arity anyTE, anyTE)]
      sigs -> sigs

typeCheckProgram :: D.Program -> IO TypeCheckResult
typeCheckProgram prog = do
  let env = buildTypeCheckEnv prog
      hsErrors =
        validateTypeDefinitions
          prog.typeDefinitions
          ( Map.fromList
              [ ( (td.name, length td.typeVars),
                  td
                )
              | td <- prog.typeDefinitions
              ]
          )
          ++ detectDuplicateConstructors prog.typeDefinitions
          -- Rules and single-signature functions report their
          -- constructor-arity errors per unit from inside the session
          -- ('recordHsDiags'); only class functions, whose equations
          -- are checked in throwaway sessions, are validated here.
          ++ concatMap (functionConstructorArities env) classFunctions
  chrResult <-
    runCheckSession env prog $ do
      mapM_ checkRule prog.rules
      -- Multi-signature class functions are excluded here: their
      -- equations are checked per candidate signature in isolated
      -- sessions below (spec §Signature Overloading §Equation
      -- checking).
      mapM_ checkFunction plainFunctions
  classErrors <- concat <$> traverse (checkClassFunction env prog) classFunctions
  pure
    TypeCheckResult
      { errors = hsErrors ++ chrResult.errors ++ classErrors,
        warnings = chrResult.warnings
      }
  where
    (classFunctions, plainFunctions) =
      List.partition (\f -> length f.signatures > 1) prog.functions

-- | Run one CHR type-checking session: initialize the diagnostic
-- accumulators, tell the program's signatures, run the body, and
-- collect the session's diagnostics.
runCheckSession ::
  TypeCheckEnv -> D.Program -> TC () -> IO TypeCheckResult
runCheckSession env prog body =
  withCHR typeCheckerProgram baseHostCallRegistry $
    evalStateT
      ( runReaderT
          ( do
              chrOp (tellConstraint (Qualified "$typechecker" "errors") [valueList []])
              chrOp (tellConstraint (Qualified "$typechecker" "warnings") [valueList []])
              tellConstraintSigs prog
              tellFunctionSigs prog
              tellConSigs prog
              body
              collectDiagnostics
          )
          env
      )
      emptyCtxStore

-- | Check a multi-signature class function's equations. Each
-- equation must type-check under at least one declared signature,
-- with its parameters typed by that signature's argument types and
-- its RHS checked against that signature's return type (spec
-- §Signature Overloading §Equation checking). Every
-- (equation × signature) attempt runs in its own isolated CHR
-- session — CHR has no backtracking, and the program-wide session
-- has a single error accumulator — and an attempt's diagnostics are
-- discarded: they describe the failed fit, not the program. An
-- equation that checks under no signature reports one
-- NoMatchingOverload.
checkClassFunction ::
  TypeCheckEnv -> D.Program -> D.Function -> IO [Diagnostic TypeCheckError]
checkClassFunction env prog func = do
  let AnnP eqs eqLoc eqOrigin = func.equations
      fname = flattenName (Types.qualifiedToName func.name)
      attempt eq (argTys, retTy) =
        runCheckSession env prog $ do
          let stamped = paramVarSkeletons env eq.params argTys eq.guards
          varTypes <- allocVarTypes (collectVarsInEq eq) stamped
          unit <- freshUnitId
          checkSingleSigEquation unit func (argTys, retTy) [] varTypes eq
      -- Attempts stop at the first signature the equation checks
      -- under; later candidates cannot change the accept verdict. A
      -- failed attempt's diagnostics describe the failed fit rather
      -- than the program, so they are discarded — including its
      -- warnings: under a candidate signature a contradicting
      -- evidence fact counts as failure of that candidate and emits
      -- nothing (spec §What evidence does), which is exactly "success
      -- requires no errors and no warnings". Suppression already ran
      -- inside the attempt session, so a non-empty warning list means
      -- the equation contradicted this signature without erroring.
      checkEq eq =
        let go [] =
              pure
                [ Diagnostic
                    (Just ("function " <> fname))
                    (AnnP (NoMatchingOverload fname) eqLoc eqOrigin)
                ]
            go (sig : rest) = do
              result <- attempt eq sig
              if null result.errors && null result.warnings
                then pure []
                else go rest
         in go func.signatures
  concat <$> traverse checkEq eqs

-- | Type-check a list of body goals (a query or single goal) against
-- the signatures of an already-compiled program.
--
-- Mirrors 'typeCheckProgram' but skips Haskell-side validations that
-- only make sense on a whole program (no new type definitions or
-- constructors are introduced by a goal). Constructor /uses/ do
-- appear in goals, so the wrong-arity check still runs, per goal —
-- goals are checked exactly like rule bodies (spec §Type Checking
-- Procedure), and a known constructor at the wrong arity is the
-- YCHR-60008 error there, not a silent fall-through to @any@.
-- Variables are gathered once across the whole goal list so a name
-- shared between goals refers to the same type slot — matching how
-- rule bodies are checked.
--
-- Pass the desugared program whose signatures should be in scope. For
-- queries that introduce lifted lambdas, extend @prog.functions@ with
-- those lambdas before calling so their (default-@any@) signatures are
-- visible to @check_function_use@.
typeCheckGoals ::
  D.Program ->
  SourceLoc ->
  Maybe Text ->
  [D.BodyGoal] ->
  IO TypeCheckResult
typeCheckGoals prog loc lbl goals = do
  let env = buildTypeCheckEnv prog
  runCheckSession env prog $ do
    let allVarNames = foldMap collectVarsInBodyGoal goals
    varTypes <-
      Map.fromList
        <$> mapM (\v -> (v,) <$> chrOp newVar) (Set.toList allVarNames)
    -- Seed identity, replaced per goal below; it only reaches a
    -- diagnostic if @goals@ is empty (in which case there are none).
    seedUnit <- freshUnitId
    let cctx =
          CheckCtx
            { varTypes,
              label = lbl,
              loc,
              origin = Atom "",
              ambientSigs = Map.empty,
              unitId = seedUnit
            }
    -- Each top-level goal is its own unit (spec §Type Checking
    -- Procedure), even though the goals of one query share their
    -- variable slots.
    mapM_ (checkGoalAsUnit cctx) goals
  where
    checkGoalAsUnit cctx goal = do
      unit <- freshUnitId
      env <- ask
      recordHsDiags
        unit
        (mkArityDiags cctx.label cctx.loc cctx.origin (bodyArity env goal))
      checkBodyGoal cctx {unitId = unit} goal

-- ---------------------------------------------------------------------------
-- Context helpers
-- ---------------------------------------------------------------------------

-- | Allocate a fresh 'CtxHandle' and store the current 'CheckCtx''s
-- source-location info in 'CtxMap' under it. The handle travels
-- through the CHR program as the @Ctx@ argument of every @check_*@
-- constraint (materialised via 'ctxHandleValue'); on error decoding
-- we look it back up to recover the source location for the
-- diagnostic.
freshCtxHandle :: CheckCtx -> TC CtxHandle
freshCtxHandle cctx = do
  store <- getStore
  let CtxHandle n = store.nextCtxHandle
      handle = CtxHandle n
      info =
        CtxInfo
          { label = cctx.label,
            loc = cctx.loc,
            origin = cctx.origin,
            unit = cctx.unitId
          }
  putStore
    store
      { nextCtxHandle = CtxHandle (n + 1),
        ctxMap = Map.insert handle info store.ctxMap
      }
  pure handle

-- ---------------------------------------------------------------------------
-- Environment setup
-- ---------------------------------------------------------------------------

-- | Tell @constraint_sig@ for every declared constraint. Bounded
-- constraints additionally emit @constraint_bounds@ using the SAME
-- shared type-variable map so a single @copy_term@ at the use site
-- freshens both the argument types and the bound signatures
-- consistently.
tellConstraintSigs :: D.Program -> TC ()
tellConstraintSigs prog =
  Map.foldlWithKey'
    ( \m key argTypes ->
        m >> do
          let bounds = Map.findWithDefault [] key prog.constraintBounds
              allVars = collectTypeVars argTypes ++ concatMap boundSigVars bounds
          tvars <- chrOp (freshTypeVarsForDecl allVars)
          encodedArgs <- chrOp (traverse (encodeTypeExpr tvars) argTypes)
          let runtimeNm = runtimeName (Types.qualifiedToName key.name)
              arityVal = VInt (fromIntegral key.arity)
          chrOp $
            tellConstraint
              (Qualified "$typechecker" "constraint_sig")
              [VAtom runtimeNm, arityVal, valueList encodedArgs]
          case bounds of
            [] -> pure ()
            _ -> do
              encodedBounds <- chrOp (traverse (encodeNamedBound tvars) bounds)
              chrOp $
                tellConstraint
                  (Qualified "$typechecker" "constraint_bounds")
                  [VAtom runtimeNm, arityVal, valueList encodedBounds]
    )
    (pure ())
    prog.constraintTypes

-- | Tell @function_sig@ or @function_sigs@ for every declared
-- function. Bounded single-sig functions additionally emit
-- @function_bounds@ using a shared type-variable map so a single
-- @copy_term@ at the use site freshens the signature and the
-- bound signatures consistently (see
-- 'YCHR.Internal.Types.BoundSig' and the @bounded_function_match@ rule).
tellFunctionSigs :: D.Program -> TC ()
tellFunctionSigs prog = mapM_ tellOne prog.functions
  where
    tellOne f =
      let fName = Types.qualifiedToName f.name
          runtimeNm = runtimeName fName
          arityVal = VInt (fromIntegral f.arity)
       in case (f.signatures, f.requiring) of
            ([], _) -> do
              -- No annotations: default to all-any. Bounded functions
              -- always have one signature (the resolver guarantees
              -- this), so a missing signature implies no bounds.
              let anyArgs = replicate f.arity (tcCon0 "any")
                  sig = VTerm (tcAtom "sig") [valueList anyArgs, tcCon0 "any"]
              chrOp $
                tellConstraint
                  (Qualified "$typechecker" "function_sig")
                  [VAtom runtimeNm, arityVal, sig]
            ([s], bounds@(_ : _)) -> do
              let (argTys, retTy) = s
                  allVars =
                    collectTypeVars argTys
                      ++ collectTypeVarsExpr retTy
                      ++ concatMap boundSigVars bounds
              tvars <- chrOp (freshTypeVarsForDecl allVars)
              encodedArgs <- chrOp (traverse (encodeTypeExpr tvars) argTys)
              encodedRet <- chrOp (encodeTypeExpr tvars retTy)
              let sig = VTerm (tcAtom "sig") [valueList encodedArgs, encodedRet]
              encodedBounds <- chrOp (traverse (encodeNamedBound tvars) bounds)
              chrOp $
                tellConstraint
                  (Qualified "$typechecker" "function_sig")
                  [VAtom runtimeNm, arityVal, sig]
              chrOp $
                tellConstraint
                  (Qualified "$typechecker" "function_bounds")
                  [VAtom runtimeNm, arityVal, valueList encodedBounds]
            ([s], []) -> do
              sig <- chrOp (encodeFunctionSig s)
              chrOp $
                tellConstraint
                  (Qualified "$typechecker" "function_sig")
                  [VAtom runtimeNm, arityVal, sig]
            (ss, _) -> do
              sigs <- chrOp (traverse encodeFunctionSig ss)
              chrOp $
                tellConstraint
                  (Qualified "$typechecker" "function_sigs")
                  [VAtom runtimeNm, arityVal, valueList sigs]

-- | Encode one declared @(arg-types, return-type)@ pair as a runtime
-- @sig(args, ret)@ value, allocating fresh logical variables for the
-- type variables shared between the args and the return.
encodeFunctionSig :: ([TypeExpr], TypeExpr) -> Chr Value
encodeFunctionSig (argTys, retTy) = do
  tvars <- freshTypeVarsForDecl (collectTypeVars argTys ++ collectTypeVarsExpr retTy)
  encodedArgs <- traverse (encodeTypeExpr tvars) argTys
  encodedRet <- encodeTypeExpr tvars retTy
  pure (VTerm (tcAtom "sig") [valueList encodedArgs, encodedRet])

-- | Encode a single 'BoundSig' against a shared type-variable map
-- as a runtime @nbound(GName, args, ret)@ value (the flat shape
-- expected by the CHR-side @bound_named@ algebraic type). The
-- shared map is essential: every bound on the same declaration uses
-- the same logical variables for the declaration's type parameters,
-- so a single @copy_term@ at the call site freshens them
-- consistently across signature and bounds.
encodeNamedBound :: Map Text Value -> BoundSig -> Chr Value
encodeNamedBound tvars bs = do
  encodedArgs <- traverse (encodeTypeExpr tvars) bs.argTypes
  encodedRet <- encodeTypeExpr tvars bs.returnType
  pure
    ( VTerm
        (tcAtom "nbound")
        [VAtom (runtimeName bs.name), valueList encodedArgs, encodedRet]
    )

-- | Collect every type variable mentioned in a 'BoundSig'.
boundSigVars :: BoundSig -> [Text]
boundSigVars bs = collectTypeVars bs.argTypes ++ collectTypeVarsExpr bs.returnType

tellConSigs :: D.Program -> TC ()
tellConSigs prog =
  mapM_
    ( \td ->
        mapM_
          ( \dc -> do
              let allVars = td.typeVars
              tvars <- chrOp (freshTypeVarsForDecl allVars)
              let parentType = encodeTCon tvars td.name td.typeVars
              encodedFields <- chrOp (traverse (encodeTypeExpr tvars) dc.conArgs)
              let sig = VTerm (tcAtom "sig") [parentType, valueList encodedFields]
              chrOp $
                tellConstraint
                  (Qualified "$typechecker" "con_sig")
                  [ VAtom
                      ( runtimeName
                          dc.conName
                      ),
                    sig
                  ]
          )
          (typeConstructors td)
    )
    prog.typeDefinitions

-- | Encode a 'Name' as a runtime 'Value', matching the runtime
-- representation produced by 'YCHR.Internal.Compile.compileTerm' for declared
-- constructors: every name becomes a 'VAtom' with the @vmName@
-- encoding (@m__n@ for qualified, plain @n@ for unqualified).
-- 'BMatchTerm' accepts 'VAtom' for arity-0 dispatch, matching the
-- shape compiled head patterns produce. (The two prelude booleans are
-- the exception on the pattern side, where the compiler lowers the
-- match guard to a boolean equality instead — but they are encoded
-- here as names, never matched against a compiled pattern, so the atom
-- encoding is still the right one.)
encodeName :: Name -> Value
encodeName (Unqualified n) = VAtom n
encodeName name@(Qualified _ _) = VAtom (runtimeName name)

-- | Encode a type constructor application: tcon(name, [arg1, arg2, ...])
encodeTCon :: Map Text Value -> Name -> [Text] -> Value
encodeTCon tvars name vars =
  VTerm
    (tcAtom "tcon")
    [ encodeName name,
      valueList (map (\v -> Map.findWithDefault (tcCon0 "any") v tvars) vars)
    ]

-- ---------------------------------------------------------------------------
-- Type encoding
-- ---------------------------------------------------------------------------

-- | Collect type variable names from a list of type expressions.
collectTypeVars :: [TypeExpr] -> [Text]
collectTypeVars = concatMap collectTypeVarsExpr

collectTypeVarsExpr :: TypeExpr -> [Text]
collectTypeVarsExpr (TypeVar v) = [v]
collectTypeVarsExpr (TypeCon _ args) = concatMap collectTypeVarsExpr args

-- | Create fresh logical variables for each unique type variable name.
freshTypeVarsForDecl :: [Text] -> Chr (Map Text Value)
freshTypeVarsForDecl vars = do
  let unique = Set.toList (Set.fromList vars)
  pairs <- mapM (\v -> (v,) <$> newVar) unique
  pure (Map.fromList pairs)

-- | Encode a TypeExpr as a runtime Value.
encodeTypeExpr :: Map Text Value -> TypeExpr -> Chr Value
encodeTypeExpr tvars (TypeVar v) =
  case Map.lookup v tvars of
    Just val -> pure val
    Nothing -> pure (tcCon0 "any")
encodeTypeExpr _ (TypeCon (Unqualified "int") []) = pure (tcCon0 "int")
encodeTypeExpr _ (TypeCon (Unqualified "float") []) = pure (tcCon0 "float")
encodeTypeExpr _ (TypeCon (Unqualified "string") []) = pure (tcCon0 "string")
encodeTypeExpr _ (TypeCon (Unqualified "any") []) = pure (tcCon0 "any")
-- Function type: fun(A, B) -> C is parsed as TypeCon "->" [TypeCon "fun" [A, B], C]
encodeTypeExpr
  tvars
  ( TypeCon
      (Unqualified "->")
      [ TypeCon (Unqualified "fun") argTys,
        retTy
        ]
    ) = do
    encodedArgs <- traverse (encodeTypeExpr tvars) argTys
    encodedRet <- encodeTypeExpr tvars retTy
    pure (VTerm (tcAtom "fun") [valueList encodedArgs, encodedRet])
encodeTypeExpr tvars (TypeCon name args) = do
  encodedArgs <- traverse (encodeTypeExpr tvars) args
  pure (VTerm (tcAtom "tcon") [encodeName name, valueList encodedArgs])

-- ---------------------------------------------------------------------------
-- Declaration-position `any` stamping
-- ---------------------------------------------------------------------------

isAnyTypeExpr :: TypeExpr -> Bool
isAnyTypeExpr (TypeCon (Unqualified "any") []) = True
isAnyTypeExpr _ = False

-- | True when @any@ appears anywhere in a type expression, at any
-- depth. Only such a source needs a shaped slot ('SkCon' \/ 'SkFun');
-- everything else takes the plain flexible slot it always took.
mentionsAny :: TypeExpr -> Bool
mentionsAny t | isAnyTypeExpr t = True
mentionsAny (TypeCon _ args) = any mentionsAny args
mentionsAny (TypeVar _) = False

-- | The shape a variable's declaration sources determine for its type
-- slot, computed position by position.
data TypeSkeleton
  = -- | Every source says @any@ here. The slot gets the literal @any@
    -- atom, which no rule binds.
    SkAny
  | -- | At least one source says something else here. The slot gets a
    -- fresh flexible variable for that source to bind.
    SkOpen
  | -- | Every source applies this type constructor here.
    SkCon Name [TypeSkeleton]
  | -- | Every source is a function type of this shape here.
    SkFun [TypeSkeleton] TypeSkeleton
  deriving (Show, Eq)

-- | The skeleton a set of declaration sources determines.
--
-- The rule of §Type states — "the variable keeps its most informative
-- source; the @any@ positions are merely checked" — applies per
-- /position/, not per variable. @any@ never binds, so a position that
-- some source leaves @any@ and another makes concrete must reach the
-- checker as a flexible variable: the @any@ source then binds nothing
-- and the concrete one determines it, in either order.
--
-- That works at the top level for free, because a whole-variable slot
-- starts out flexible. It does not work nested inside a declared type,
-- because @tc_unify@ binds a flexible slot to a type constructor
-- application /as a whole/ — @list(any)@ meeting @list(int)@ then
-- compares an @any@ that no longer has anywhere to go. Pre-shaping the
-- slot as @list(β)@ keeps the meet componentwise, so the nested
-- position behaves exactly like a top-level one.
--
-- Positions no source leaves @any@ keep the plain flexible slot, which
-- is what this used to allocate for every variable that was not
-- stamped outright.
skeletonOf :: [TypeExpr] -> TypeSkeleton
skeletonOf [] = SkOpen
skeletonOf ts
  | all isAnyTypeExpr ts = SkAny
  | not (any mentionsAny ts) = SkOpen
  | Just (argss, rets) <- sameFunShape ts =
      SkFun (map skeletonOf (List.transpose argss)) (skeletonOf rets)
  | Just (name, argss) <- sameConShape ts =
      SkCon name (map skeletonOf (List.transpose argss))
  | otherwise = SkOpen

-- | The @fun(τ₁, …, τₙ) -> τᵣ@ shape, spelled as 'encodeTypeExpr'
-- recognizes it.
funShape :: TypeExpr -> Maybe ([TypeExpr], TypeExpr)
funShape
  ( TypeCon
      (Unqualified "->")
      [TypeCon (Unqualified "fun") args, ret]
    ) = Just (args, ret)
funShape _ = Nothing

-- | The argument lists and return types when every source is a
-- function type of the same arity.
sameFunShape :: [TypeExpr] -> Maybe ([[TypeExpr]], [TypeExpr])
sameFunShape ts = do
  shapes <- traverse funShape ts
  let argss = map fst shapes
  case argss of
    [] -> Nothing
    (as : rest) | all ((== length as) . length) rest -> Just (argss, map snd shapes)
    _ -> Nothing

-- | The per-position argument lists when every source applies the same
-- type constructor at the same arity. Function types are excluded —
-- they are spelled as a @'->'@ application but encoded differently, so
-- 'sameFunShape' handles them and this must not claim them.
sameConShape :: [TypeExpr] -> Maybe (Name, [[TypeExpr]])
sameConShape ts@(TypeCon name args : _)
  | not (null args),
    all (matches name (length args)) ts =
      Just (name, [as | TypeCon _ as <- ts])
  where
    matches n ar t = case t of
      TypeCon n' as -> n == n' && length as == ar && funShape t == Nothing
      TypeVar _ -> False
sameConShape _ = Nothing

-- | Given @(variable, declared type)@ occurrences gathered from a
-- unit's declaration positions, plus the variable pairs linked by the
-- synthetic var–var 'D.GuardEqual's that HNF introduces for repeated
-- head/pattern variables, the slot skeleton of each variable.
--
-- HNF splits a repeated surface variable into distinct variables
-- joined by @GuardEqual@, so declaration sources must be judged per
-- /equivalence class/, not per HNF variable. Every member of a class
-- gets its own instance of the class's skeleton: the members stay
-- distinct terms, each checked against its own declaration position,
-- and @eq_unify@ merges them (two shared slots would let the first
-- head position win outright, turning the deliberate
-- inaccessible-branch warning of two contradicting sources into an
-- inconsistency error).
varSkeletons :: [(Text, TypeExpr)] -> [(Text, Text)] -> Map Text TypeSkeleton
varSkeletons occs links =
  Map.fromList
    [ (v, skeletonOf srcs)
    | comp <- components,
      let srcs = [t | (v', t) <- occs, Set.member v' comp],
      not (null srcs),
      v <- Set.toList comp
    ]
  where
    allVars =
      Set.fromList (map fst occs)
        <> Set.fromList (concatMap (\(a, b) -> [a, b]) links)
    adj =
      Map.fromListWith
        (<>)
        ( [(a, Set.singleton b) | (a, b) <- links]
            ++ [(b, Set.singleton a) | (a, b) <- links]
        )
    components = go (Set.toList allVars) Set.empty
    go [] _ = []
    go (v : vs) seen
      | Set.member v seen = go vs seen
      | otherwise =
          let comp = reach (Set.singleton v) [v]
           in comp : go vs (seen <> comp)
    reach acc [] = acc
    reach acc (x : xs) =
      let new = Set.difference (Map.findWithDefault Set.empty x adj) acc
       in reach (acc <> new) (Set.toList new ++ xs)

-- | The var–var links contributed by a guard list: only
-- 'D.GuardEqual' between two bare variables counts. These are the
-- synthetic equalities HNF emits for repeated head variables (user
-- ask-equality guards desugar to 'D.GuardExpr', not 'D.GuardEqual').
guardEqualLinks :: [D.Guard] -> [(Text, Text)]
guardEqualLinks gs =
  [(v1, v2) | D.GuardEqual (R.VarExpr v1) (R.VarExpr v2) <- gs]

-- | Field-type occurrences contributed by HNF's 'D.GuardGetArg'
-- guards: the extracted variable's declaration source is the matched
-- constructor's field type at the extracted index (spec §Sources of
-- Type Information §8). Without these, a variable reached only
-- through a compound head pattern would look sourceless (or
-- @any@-only, via a 'D.GuardEqual' link) to 'varSkeletons' and could
-- be stamped even though the field type is solid. Tracks which
-- constructor each term was matched against exactly like 'checkGuards'
-- does — keyed by the scrutinized variable, since a nested pattern's
-- match interleaves with its parent's extractions — including the
-- @Unqualified varName@ fallback.
guardFieldOccs :: TypeCheckEnv -> [D.Guard] -> [(Text, TypeExpr)]
guardFieldOccs env = go Map.empty
  where
    go _ [] = []
    go matched (D.GuardMatch operand conName _ : gs) =
      case guardOperandVar operand of
        Just v -> go (Map.insert v (canonicalizeConName env conName) matched) gs
        Nothing -> go matched gs
    go matched (D.GuardGetArg varName operand idx : gs) =
      let scrutinee = guardOperandVar operand >>= \v -> Map.lookup v matched
          conName = fromMaybe (Unqualified varName) scrutinee
          occ = case Map.lookup conName env.conMap of
            Just (_, dc)
              | idx < length dc.conArgs ->
                  [(varName, dc.conArgs !! idx)]
            _ -> []
       in occ ++ go matched gs
    go matched (D.GuardEqual {} : gs) = go matched gs
    go matched (D.GuardExpr {} : gs) = go matched gs

-- | Slot skeletons determined by a rule head's declaration positions.
-- Head arguments are HNF (variables and wildcards only), so the
-- position-to-variable mapping is a static zip against the declared
-- argument types.
headVarSkeletons ::
  TypeCheckEnv -> [D.HeadConstraint] -> [D.Guard] -> Map Text TypeSkeleton
headVarSkeletons env hcs guards =
  varSkeletons
    ( [ (v, t)
      | hc <- hcs,
        Just declTys <-
          [Map.lookup (headConstraintKey hc) env.constraintTypesEnv],
        (HeadVar v, t) <- zip hc.args declTys
      ]
        ++ guardFieldOccs env guards
    )
    (guardEqualLinks guards)

-- | Declaration-map key for a head occurrence.
headConstraintKey :: D.HeadConstraint -> Types.ConstraintKey
headConstraintKey hc = Types.ConstraintKey hc.name (length hc.args)

-- | Slot skeletons determined by a single-signature equation's
-- parameter positions. Same shape as 'headVarSkeletons' for the one
-- declaration an equation has.
paramVarSkeletons ::
  TypeCheckEnv -> [HeadArg] -> [TypeExpr] -> [D.Guard] -> Map Text TypeSkeleton
paramVarSkeletons env params declTys guards
  | length params /= length declTys = Map.empty
  | otherwise =
      varSkeletons
        ( [(v, t) | (HeadVar v, t) <- zip params declTys]
            ++ guardFieldOccs env guards
        )
        (guardEqualLinks guards)

-- | Allocate the per-unit variable type slots from their skeletons. A
-- variable with no declaration source at all takes a plain flexible
-- slot ('SkOpen').
allocVarTypes :: Set Text -> Map Text TypeSkeleton -> TC (Map Text Value)
allocVarTypes allVarNames skels =
  Map.fromList <$> mapM slot (Set.toList allVarNames)
  where
    slot v = (v,) <$> allocSkeleton (Map.findWithDefault SkOpen v skels)

-- | Materialize one skeleton. Mirrors 'encodeTypeExpr''s shapes, so a
-- shaped slot meets a declared type componentwise instead of binding
-- to it whole.
allocSkeleton :: TypeSkeleton -> TC Value
allocSkeleton SkAny = pure (tcCon0 "any")
allocSkeleton SkOpen = chrOp newVar
allocSkeleton (SkCon name subs) = do
  args <- traverse allocSkeleton subs
  pure (VTerm (tcAtom "tcon") [encodeName name, valueList args])
allocSkeleton (SkFun argSks retSk) = do
  args <- traverse allocSkeleton argSks
  ret <- allocSkeleton retSk
  pure (VTerm (tcAtom "fun") [valueList args, ret])

-- ---------------------------------------------------------------------------
-- Per-rule checking
-- ---------------------------------------------------------------------------

checkRule :: D.Rule -> TC ()
checkRule rule = do
  env <- ask
  let allVarNames = collectVarsInRule rule
      AnnP hd headLoc headOrigin = rule.head
      AnnP guards guardLoc guardOrigin = rule.guard
  varTypes <-
    allocVarTypes
      allVarNames
      (headVarSkeletons env (hd.kept ++ hd.removed) guards)
  -- A rule is one checking unit: head, guards, and body share a
  -- 'UnitId' even though each section gets its own 'CheckCtx'.
  unit <- freshUnitId
  recordHsDiags unit (ruleConstructorArities env rule)
  let ruleLabel = fmap (\n -> "rule " <> n) rule.name
      AnnP body bodyLoc bodyOrigin = rule.body
      headCtx0 =
        CheckCtx
          { varTypes,
            label = ruleLabel,
            loc = headLoc,
            origin = headOrigin,
            ambientSigs = Map.empty,
            unitId = unit
          }
      headConstraints = hd.kept ++ hd.removed
  -- Walk each head constraint. For bounded constraints, allocate a
  -- fresh σ for this head occurrence (per §Use sites: each
  -- occurrence's type variables are freshly allocated even when the
  -- same bounded constraint appears twice) and collect the ambient
  -- signatures the occurrence assumes. For unbounded constraints,
  -- fall through to the ordinary check.
  ambientPerName <-
    fmap (Map.unionsWith (++)) $
      traverse (checkHeadConstraint headCtx0 env) headConstraints
  let guardCtx =
        CheckCtx
          { varTypes,
            label = ruleLabel,
            loc = guardLoc,
            origin = guardOrigin,
            ambientSigs = ambientPerName,
            unitId = unit
          }
      -- Same context, attributed to the head: where the patterns the
      -- HNF-synthetic guards were derived from are written.
      headPatternCtx =
        CheckCtx
          { varTypes,
            label = ruleLabel,
            loc = headLoc,
            origin = headOrigin,
            ambientSigs = ambientPerName,
            unitId = unit
          }
      bodyCtx =
        CheckCtx
          { varTypes,
            label = ruleLabel,
            loc = bodyLoc,
            origin = bodyOrigin,
            ambientSigs = ambientPerName,
            unitId = unit
          }
  -- HNF-synthetic guards represent the head patterns they were
  -- derived from, so they report against the head rather than against
  -- the guard text (a rule with no user guard has no guard text at
  -- all).
  checkGuards
    GuardCtxs {userGuardCtx = guardCtx, patternCtx = headPatternCtx}
    guards
  mapM_ (checkBodyGoal bodyCtx) body

-- | Check one head constraint occurrence. Returns the ambient sigs
-- this occurrence contributes (empty for unbounded constraints).
--
-- A rule-head occurrence is an *implementation site*, not a use site
-- (spec §Bounded constraints §Use sites): it allocates the declared
-- type parameters as fresh **rigid** identities, per occurrence, and
-- types the head's variables through the declared argument types.
-- Rigidity is what makes the rule body correct for an /arbitrary/
-- instantiation: the store is a heterogeneous multiset, so with
-- @:- chr_constraint leq(T, T).@ declared, an @leq(1, 2)@ and an
-- @leq(a, b)@ may sit in it side by side and each occurrence matches
-- an independently chosen instance. A rule-wide (or program-wide)
-- flexible σ would silently assume they agree.
--
-- Where matching /does/ force two occurrences to agree — a variable
-- shared between head positions — HNF turns the sharing into a
-- 'D.GuardEqual', whose evidence merges the two skolems
-- ('checkGuard'), so multi-head idioms like transitivity of a
-- polymorphic @leq@ still check.
--
-- Both the bounded and the unbounded case take this path: the
-- declared argument types are encoded here rather than matched
-- CHR-side, because @check_constraint_use@ @copy_term@s the stored
-- declaration into fresh /flexible/ variables — right for a use
-- site (a body tell or a goal), wrong for an implementation site.
-- Untyped and all-@any@ declarations mention no type variables and
-- so allocate no rigids, which is why unannotated programs never
-- meet one.
checkHeadConstraint ::
  CheckCtx ->
  TypeCheckEnv ->
  D.HeadConstraint ->
  TC (Map AmbientKey [Value])
checkHeadConstraint cctx env hc = do
  let key = headConstraintKey hc
      argTypes = Map.findWithDefault [] key env.constraintTypesEnv
      bounds = Map.findWithDefault [] key env.constraintBoundsEnv
      allVars = collectTypeVars argTypes ++ concatMap boundSigVars bounds
  tvars <- freshRigidTypeVarsForDecl allVars
  encodedDeclArgs <- chrOp (traverse (encodeTypeExpr tvars) argTypes)
  headArgValues <- traverse (typeOfTerm cctx . headArgToTerm) hc.args
  ctx <- freshCtxHandle cctx
  zipWithM_ (tellCheckUnify ctx) headArgValues encodedDeclArgs
  ambEntries <- traverse (emitAmbient tvars) bounds
  pure (Map.fromListWith (++) ambEntries)

-- | Emit a @check_unify(t1, t2, ctx)@ constraint. The argument order
-- matches the CHR rule: source-variable type first, declared type
-- second. See the @tc_unify@ argument-order note in the module
-- header.
tellCheckUnify :: CtxHandle -> Value -> Value -> TC ()
tellCheckUnify ctx t1 t2 =
  chrOp $
    tellConstraint
      (Qualified "$typechecker" "check_unify")
      [t1, t2, ctxHandleValue ctx]

-- | One bound signature, encoded against a declaration's tvar map.
data EncodedBound = EncodedBound
  { boundName :: Text,
    boundArgs :: [Value],
    boundRet :: Value,
    boundSigValue :: Value
  }

encodeBoundSig :: Map Text Value -> BoundSig -> TC EncodedBound
encodeBoundSig tvars bs = do
  encodedArgs <- chrOp (traverse (encodeTypeExpr tvars) bs.argTypes)
  encodedRet <- chrOp (encodeTypeExpr tvars bs.returnType)
  pure
    EncodedBound
      { boundName = runtimeName bs.name,
        boundArgs = encodedArgs,
        boundRet = encodedRet,
        boundSigValue = VTerm (tcAtom "sig") [valueList encodedArgs, encodedRet]
      }

-- | Encode a bound as an ambient-sig map entry. A rule-head
-- occurrence of a bounded constraint (and a bounded function's own
-- equation) /assumes/ its bound (spec §Bounded constraints — heads
-- and equations are implementation sites): the required signatures
-- enter the scope's ambient map, which the driver carries by value
-- into every use-site emission — there is no CHR-side ambient store.
emitAmbient ::
  Map Text Value ->
  BoundSig ->
  TC (AmbientKey, [Value])
emitAmbient tvars bs = do
  eb <- encodeBoundSig tvars bs
  pure (AmbientKey eb.boundName (length eb.boundArgs), [eb.boundSigValue])

-- | Ambient candidate signatures for one bound's named function at
-- the current scope (identity sharing with the enclosing
-- declaration's tvars).
boundAmbientSigs :: CheckCtx -> BoundSig -> [Value]
boundAmbientSigs cctx bs =
  Map.findWithDefault
    []
    (AmbientKey (runtimeName bs.name) (length bs.argTypes))
    cctx.ambientSigs

-- | Declared candidate signatures for one bound's named function,
-- each freshly instantiated ('encodeFunctionSig' — the existential
-- discharge check never binds, so per-emission instantiation cannot
-- pollute anything).
boundDeclSigs :: BoundSig -> TC [Value]
boundDeclSigs bs = do
  env <- ask
  let declSigTys =
        Map.findWithDefault [] (runtimeName bs.name) env.functionSigsEnv
  chrOp (traverse encodeFunctionSig declSigTys)

-- | Assemble the by-value @bcand@ entries for a bounded callee's (or
-- bounded constraint tell's) own bounds: one @bc(name, ambs, decls)@
-- per bound-named function, same-named entries merged. Ambient and
-- declared candidates travel separately — see the @bcand@ note in
-- typechecker.chr.
buildBoundCands :: CheckCtx -> [BoundSig] -> TC Value
buildBoundCands cctx bounds = do
  entries <-
    traverse
      ( \bs -> do
          decls <- boundDeclSigs bs
          pure (runtimeName bs.name, (boundAmbientSigs cctx bs, decls))
      )
      bounds
  let merge (a1, d1) (a2, d2) = (a2 ++ a1, d2 ++ d1)
      merged = Map.toList (Map.fromListWith merge entries)
  pure $
    valueList
      [ VTerm (tcAtom "bc") [VAtom gname, valueList ambs, valueList decls]
      | (gname, (ambs, decls)) <- merged
      ]

-- | Emit the equation-site @check_bound@ for one of the enclosing
-- function's own bounds (trivially satisfied through the ambient
-- signature it just contributed; see the discharge notes in
-- typechecker.chr).
tellEquationBound :: CheckCtx -> CtxHandle -> BoundSig -> EncodedBound -> TC ()
tellEquationBound cctx ctx bs eb = do
  declSigs <- boundDeclSigs bs
  chrOp $
    tellConstraint
      (Qualified "$typechecker" "check_bound")
      [ VAtom eb.boundName,
        valueList (boundAmbientSigs cctx bs),
        valueList declSigs,
        valueList eb.boundArgs,
        eb.boundRet,
        ctxHandleValue ctx
      ]

-- | Tell-side constraint use: arguments are 'Expr's and are evaluated
-- like any other expression position.
checkConstraintTell :: CheckCtx -> Types.QualifiedName -> [D.Expr] -> TC ()
checkConstraintTell cctx qn args = do
  argTypeVars <- traverse (typeOfExpr cctx) args
  emitConstraintUse cctx qn argTypeVars

emitConstraintUse :: CheckCtx -> Types.QualifiedName -> [Value] -> TC ()
emitConstraintUse cctx qn argTypeVars = do
  env <- ask
  ctx <- freshCtxHandle cctx
  let key = Types.ConstraintKey qn (length argTypeVars)
      bounds = Map.findWithDefault [] key env.constraintBoundsEnv
  boundCands <- buildBoundCands cctx bounds
  chrOp $
    tellConstraint
      (Qualified "$typechecker" "check_constraint_use")
      [ VAtom (runtimeName (Types.qualifiedToName qn)),
        VInt (fromIntegral (length argTypeVars)),
        boundCands,
        valueList argTypeVars,
        ctxHandleValue ctx
      ]

-- ---------------------------------------------------------------------------
-- Guard checking
-- ---------------------------------------------------------------------------

-- | Process a guard list left-to-right, threading the canonicalized
-- constructor name from each 'D.GuardMatch' into any 'D.GuardGetArg's
-- that follow on the same term. Per 'docs/reference/type-system.md' (Desugared
-- guards / HNF synthetic guards), a @GuardGetArg@ always follows a
-- @GuardMatch@ on the same term — the match establishes which
-- constructor's field types to use, which the get-arg then needs to
-- resolve a field index.
-- | The two source attributions guard checking needs. Only
-- 'D.GuardExpr' is user-written guard text; the other guard forms are
-- synthesized by HNF from a head or parameter pattern and have no
-- source of their own, so their diagnostics point at the pattern they
-- came from. The two contexts must agree on everything but location
-- and origin: they describe one unit's variable slots and ambient
-- signatures.
data GuardCtxs = GuardCtxs
  { userGuardCtx :: CheckCtx,
    patternCtx :: CheckCtx
  }

checkGuards :: GuardCtxs -> [D.Guard] -> TC ()
checkGuards gctxs = go Map.empty
  where
    go _ [] = pure ()
    go matches (g : gs) = do
      matches' <- checkGuard gctxs matches g
      go matches' gs

-- | What a 'D.GuardMatch' leaves for the 'D.GuardGetArg's that read
-- from the same term: the canonicalized constructor name, and one
-- type slot per field at the instantiation the match determined.
-- Reading a field type out of a slot rather than re-deriving it from
-- the constructor declaration is what makes extraction work at a
-- rigid scrutinee, where the match pinned the skolem to fresh rigid
-- parameters (spec §What evidence does).
--
-- 'fieldSlots' is empty when the match was not emitted at all (an
-- undeclared constructor, or one used at the wrong arity), which
-- sends the following extractions down the fallback path.
data MatchState = MatchState
  { conName :: Name,
    fieldSlots :: [Value]
  }

-- | Matches recorded so far, keyed by the variable they scrutinize.
-- Keying by operand rather than remembering only the most recent match
-- is load-bearing: HNF decomposes a compound depth-first, so a nested
-- pattern's match sits /between/ its parent's extractions
-- (@[[_|_]|Rest]@ gives match, get 0, match, get 1) and "most recent
-- wins" would read the outer term's field out of the inner term's
-- constructor.
type MatchStates = Map Text MatchState

-- | The variable an HNF guard scrutinizes. Every 'D.GuardMatch' and
-- 'D.GuardGetArg' HNF emits has a bare-variable operand (see
-- @decomposeCompound@ / @decomposeArg@ in "YCHR.Internal.Desugar"), so a
-- non-variable operand simply records nothing and the extraction falls
-- back to the constructor declaration.
guardOperandVar :: R.Expr -> Maybe Text
guardOperandVar (R.VarExpr v) = Just v
guardOperandVar _ = Nothing

checkGuard :: GuardCtxs -> MatchStates -> D.Guard -> TC MatchStates
checkGuard gctxs matches (D.GuardEqual e1 e2) = do
  let cctx = gctxs.patternCtx
  -- GuardEqual operands are structural positions (spec §Expression
  -- Typing); after HNF they are only variables and literals, where
  -- the two typing modes coincide, but structural mode is the
  -- correct one on principle.
  tv1 <- typeOfExprStructural cctx e1
  tv2 <- typeOfExprStructural cctx e2
  ctx <- freshCtxHandle cctx
  -- An evidence form (spec §Evidence forms): ask-equality succeeds
  -- only on structurally identical terms, so the two positions have
  -- the same type whenever the guard passes. HNF emits this for a
  -- variable repeated across head (or parameter) positions and for a
  -- non-variable head argument, which is what lets the shared
  -- variable of a multi-head rule over a polymorphic constraint
  -- merge the two occurrences' skolems, and a literal pattern pin
  -- its equation's. @eq_unify@ carries the second reading too: the
  -- two HNF variables of a repeated source variable are one
  -- variable, so a still-flexible slot binds (§Type states) rather
  -- than staying inert as evidence proper would. The relation is
  -- symmetric, so the source order is kept.
  chrOp $
    tellConstraint
      (Qualified "$typechecker" "eq_unify")
      [tv1, tv2, ctxHandleValue ctx]
  pure matches
checkGuard gctxs matches (D.GuardMatch operand conName arity) = do
  let cctx = gctxs.patternCtx
  env <- ask
  let canonical = canonicalizeConName env conName
  matched <-
    if knownConstructorWithArity env canonical arity
      then do
        operandType <- typeOfExpr cctx operand
        fieldSlots <- chrOp (replicateM arity newVar)
        -- One fresh /rigid/ variable per parameter of the
        -- constructor's parent type. They are used only at a rigid
        -- scrutinee, where the match pins the skolem to the parent
        -- type at these parameters: the matched value's field types
        -- are store-chosen, so nothing downstream may assume more
        -- about them than the match proved (spec §What evidence does).
        betas <- replicateM (parentTypeArity env canonical) freshRigidTypeVar
        ctx <- freshCtxHandle cctx
        chrOp $
          tellConstraint
            (Qualified "$typechecker" "check_guard_match")
            [ operandType,
              VAtom (runtimeName canonical),
              valueList betas,
              valueList fieldSlots,
              ctxHandleValue ctx
            ]
        pure MatchState {conName = canonical, fieldSlots}
      else pure MatchState {conName = canonical, fieldSlots = []}
  pure $ case guardOperandVar operand of
    Just v -> Map.insert v matched matches
    Nothing -> matches
checkGuard gctxs matches (D.GuardGetArg varName operand idx) = do
  let cctx = gctxs.patternCtx
  resultTypeVar <- chrOp (varType cctx varName)
  env <- ask
  let scrutinee = guardOperandVar operand >>= \v -> Map.lookup v matches
  case scrutinee >>= \ms -> listAt idx ms.fieldSlots of
    -- The match on this same term already resolved the field's type at
    -- the instantiation it determined; unifying against its slot
    -- avoids consulting the scrutinee's type a second time (which is
    -- what broke extraction at a rigid scrutinee).
    Just slot -> do
      ctx <- freshCtxHandle cctx
      tellCheckUnify ctx resultTypeVar slot
    -- No usable match on this term: resolve the field type from the
    -- constructor declaration instead.
    Nothing -> do
      let conName = maybe (Unqualified varName) (.conName) scrutinee
          withinArity =
            case Map.lookup conName env.conMap of
              Just (_, dc) -> idx < length dc.conArgs
              Nothing -> True
      when withinArity $ do
        operandType <- typeOfExpr cctx operand
        ctx <- freshCtxHandle cctx
        chrOp $
          tellConstraint
            (Qualified "$typechecker" "check_guard_getarg")
            [ resultTypeVar,
              operandType,
              VAtom (runtimeName conName),
              VInt (fromIntegral idx),
              ctxHandleValue ctx
            ]
  pure matches
checkGuard gctxs matches (D.GuardExpr expr) = do
  let cctx = gctxs.userGuardCtx
  tv <- typeOfExpr cctx expr
  ctx <- freshCtxHandle cctx
  chrOp $
    tellConstraint
      (Qualified "$typechecker" "check_guard_bool")
      [tv, ctxHandleValue ctx]
  -- A type-predicate guard additionally contributes evidence: its
  -- success at runtime entails the operand's type (spec §Evidence
  -- forms). The ordinary call check above still runs — the fact is
  -- extra information, not a replacement.
  case typePredicateGuard expr of
    Nothing -> pure ()
    Just (v, fact) -> do
      slot <- chrOp (varType cctx v)
      tellEvUnify ctx fact slot
  pure matches

-- | Emit an @ev_unify(fact, slot, ctx)@ constraint: the evidence meet,
-- which may pin a rigid type variable and reports a contradiction as
-- the inaccessible-branch warning rather than an error. The fact the
-- guard establishes goes first and the type the position already has
-- second — the order the warning message reads them in.
tellEvUnify :: CtxHandle -> Value -> Value -> TC ()
tellEvUnify ctx t1 t2 =
  chrOp $
    tellConstraint
      (Qualified "$typechecker" "ev_unify")
      [t1, t2, ctxHandleValue ctx]

-- | The typing fact a type-predicate guard contributes, as
-- @(operand variable, fact type)@.
--
-- Only a call of one of the prelude type predicates on a /bare
-- variable/ qualifies: the fact is about that variable's type slot,
-- and the guard's success entails it exactly (spec §Evidence forms).
-- @atom/1@ is deliberately absent — a nullary constructor inhabits
-- many types — as are @var@/@nonvar@/@ground@, whose success entails
-- boundness rather than a type.
--
-- This list is **provisional**: it names prelude functions directly,
-- pending the declaration mechanism by which a function declares
-- itself a refinement predicate (docs/roadmap.md). Nothing else in
-- the checker keys off function names.
typePredicateGuard :: R.Expr -> Maybe (Text, Value)
typePredicateGuard (R.CallExpr qn [R.VarExpr v])
  | qn.moduleName == "prelude" =
      (v,) <$> case qn.baseName of
        "integer" -> Just (tcCon0 "int")
        "float" -> Just (tcCon0 "float")
        "string" -> Just (tcCon0 "string")
        "boolean" -> Just preludeBoolType
        _ -> Nothing
typePredicateGuard _ = Nothing

-- | The encoded @prelude:bool@ type, as @check_guard_bool@ builds it
-- CHR-side.
preludeBoolType :: Value
preludeBoolType =
  VTerm
    (tcAtom "tcon")
    [encodeName (Qualified "prelude" "bool"), valueList []]

-- ---------------------------------------------------------------------------
-- Body goal checking
-- ---------------------------------------------------------------------------

-- | Type-check one body goal. A rule body's variable slots are fixed
-- for the whole body: nothing a goal does replaces them, because
-- nothing narrows @any@ (spec §The role of @any@) and no other state
-- flows left-to-right.
checkBodyGoal :: CheckCtx -> D.BodyGoal -> TC ()
checkBodyGoal _ D.BodyTrue = pure ()
checkBodyGoal cctx (D.BodyTell qn args) = checkConstraintTell cctx qn args
checkBodyGoal cctx (D.BodyUnify e1 e2) = do
  -- `=` is pure structural unification: neither operand is
  -- evaluated at runtime, so neither is typed by evaluation here
  -- (spec §Expression Typing; contrast the `is` RHS below).
  tv1 <- typeOfExprStructural cctx e1
  tv2 <- typeOfExprStructural cctx e2
  ctx <- freshCtxHandle cctx
  tellCheckUnify ctx tv1 tv2
checkBodyGoal cctx (D.BodyIs v expr) = do
  -- The RHS is an evaluated position, so it is typed by evaluation,
  -- and the result meets the LHS variable's slot through the
  -- ordinary meet table: a flexible LHS binds to a concrete RHS
  -- (this is what carries a type through shared head type
  -- parameters), an `any` on either side is checked against and
  -- binds nothing, a rigid LHS meeting a concrete RHS is an error,
  -- and two concrete sides are consistency-checked. `is` has no
  -- special narrowing power over `any` (spec §The role of `any`:
  -- "No construct replaces `any` with something more precise").
  vType <- chrOp (varType cctx v)
  exprType <- typeOfExpr cctx expr
  ctx <- freshCtxHandle cctx
  tellCheckUnify ctx vType exprType
checkBodyGoal cctx (D.BodyCall qn args) = do
  argTypeVars <- traverse (typeOfExpr cctx) args
  retTypeVar <- chrOp newVar
  emitFunctionCall cctx (Types.qualifiedToName qn) argTypeVars retTypeVar
checkBodyGoal cctx (D.BodyApply f args) = do
  _ <- typeOfExpr cctx f
  mapM_ (typeOfExpr cctx) args
checkBodyGoal cctx (D.BodyHostStmt _ args) = mapM_ (typeOfExpr cctx) args

-- | Is this (dereferenced) type value the @any@ atom? Only the
-- driver's declaration-position stamping produces such a slot — no
-- CHR rule binds a var to @any@ (see the module header invariant).
isAnyTy :: Value -> Bool
isAnyTy (VAtom a) = a == tcBaseAtom "any"
isAnyTy _ = False

-- | Type-check a function-body prelude statement and return a 'CheckCtx'
-- to use for the remainder of the body. A 'FunIs' binding allocates a
-- /fresh/ type slot for the bound variable (mirroring the runtime's
-- lexical shadowing — 'compileFunStmt' emits 'LetVal', not unification),
-- so subsequent statements and the return expression see the new slot.
-- The RHS itself is typed against the previous slot, so @N is N + 1@
-- with N captured from an outer scope still type-checks against the
-- outer N's type.
checkFunStmt :: CheckCtx -> D.FunStmt -> TC CheckCtx
checkFunStmt cctx (D.FunIs v expr) = do
  oldSlot <- chrOp (varType cctx v)
  exprType <- typeOfExpr cctx expr
  oldT <- chrOp (deref oldSlot)
  if isAnyTy oldT
    then
      -- Rebinding a declared-`any` local keeps `any`, whatever the
      -- RHS evaluates to. Nothing narrows `any` (spec §The role of
      -- `any`), and that has to include the shadowing slot: were the
      -- rebound local to take the RHS's type, `is` would be a
      -- back-door refinement of exactly the variables the
      -- declaration said to leave alone. The RHS is still typed (the
      -- `typeOfExpr` above emits its own checks).
      pure cctx {varTypes = Map.insert v (tcCon0 "any") cctx.varTypes}
    else do
      newSlot <- chrOp newVar
      ctx <- freshCtxHandle cctx
      tellCheckUnify ctx newSlot exprType
      pure cctx {varTypes = Map.insert v newSlot cctx.varTypes}
checkFunStmt cctx (D.FunHostStmt _ args) = do
  mapM_ (typeOfExpr cctx) args
  pure cctx
checkFunStmt cctx (D.FunCall qn args) = do
  argTypeVars <- traverse (typeOfExpr cctx) args
  retTypeVar <- chrOp newVar
  emitFunctionCall cctx (Types.qualifiedToName qn) argTypeVars retTypeVar
  pure cctx
checkFunStmt cctx (D.FunApply f args) = do
  _ <- typeOfExpr cctx f
  mapM_ (typeOfExpr cctx) args
  pure cctx

checkFunStmts :: CheckCtx -> [D.FunStmt] -> TC CheckCtx
checkFunStmts = foldM checkFunStmt

-- | Emit a function-call type check. Routes through
-- @check_function_use_with_ambient@ when the call's target name has
-- ambient signatures in the current 'CheckCtx' (i.e. the call sits
-- inside a bounded function's equation or under a bounded
-- constraint's head occurrence in a rule). Otherwise falls back to
-- the plain @check_function_use@ path. The CHR side handles both
-- forms with the same overload-resolution mechanism.
emitFunctionCall ::
  CheckCtx ->
  Name ->
  [Value] ->
  Value ->
  TC ()
emitFunctionCall cctx name argTypeVars retTypeVar = do
  env <- ask
  ctx <- freshCtxHandle cctx
  let runtimeFname = runtimeName name
      ctxVal = ctxHandleValue ctx
      key = AmbientKey runtimeFname (length argTypeVars)
      calleeBounds = Map.findWithDefault [] key env.functionBoundsEnv
  boundCands <- buildBoundCands cctx calleeBounds
  case Map.lookup key cctx.ambientSigs of
    Just ambs@(_ : _) ->
      chrOp $
        tellConstraint
          (Qualified "$typechecker" "check_function_use_with_ambient")
          [ VAtom runtimeFname,
            VInt (fromIntegral (length argTypeVars)),
            valueList ambs,
            boundCands,
            valueList argTypeVars,
            retTypeVar,
            ctxVal
          ]
    _ ->
      chrOp $
        tellConstraint
          (Qualified "$typechecker" "check_function_use")
          [ VAtom runtimeFname,
            VInt (fromIntegral (length argTypeVars)),
            boundCands,
            valueList argTypeVars,
            retTypeVar,
            ctxVal
          ]

-- | Emit the check for a @fun name/arity@ reference: matched against
-- the expected function type at the use site (for a class referent,
-- the return component participates in the residual filtering — see
-- the funref rules in typechecker.chr).
emitFunctionRef ::
  CheckCtx ->
  Name ->
  [Value] ->
  Value ->
  TC ()
emitFunctionRef cctx name argTypeVars retTypeVar = do
  env <- ask
  ctx <- freshCtxHandle cctx
  let runtimeFname = runtimeName name
      key = AmbientKey runtimeFname (length argTypeVars)
      calleeBounds = Map.findWithDefault [] key env.functionBoundsEnv
      ambs = Map.findWithDefault [] key cctx.ambientSigs
  boundCands <- buildBoundCands cctx calleeBounds
  chrOp $
    tellConstraint
      (Qualified "$typechecker" "check_function_ref")
      [ VAtom runtimeFname,
        VInt (fromIntegral (length argTypeVars)),
        valueList ambs,
        boundCands,
        valueList argTypeVars,
        retTypeVar,
        ctxHandleValue ctx
      ]

-- ---------------------------------------------------------------------------
-- Per-equation checking
-- ---------------------------------------------------------------------------

checkFunction :: D.Function -> TC ()
checkFunction func = do
  let AnnP eqs _ _ = func.equations
  mapM_ (checkEquation func) eqs

checkEquation ::
  D.Function ->
  D.Equation ->
  TC ()
checkEquation func eq = do
  env <- ask
  let allVarNames = collectVarsInEq eq
      anyTE = TypeCon (Unqualified "any") []
      -- Effective single signature: an untyped function checks
      -- exactly like its all-`any` spelled-out form (spec §Defaults,
      -- "type checking treats the two forms identically"). The
      -- all-`any` signature has no type variables, so no rigid tvars
      -- are allocated, and bounds are dropped — user-written untyped
      -- functions cannot carry `requiring` (the resolver rejects
      -- it), and lifted lambdas' inherited `requiring` is ignored
      -- here exactly as 'tellFunctionSigs' ignores it for the
      -- all-`any` signature.
      effSig = case func.signatures of
        [] -> Just (replicate func.arity anyTE, anyTE, [])
        [(argTys, retTy)] -> Just (argTys, retTy, func.requiring)
        _ -> Nothing
      -- Parameters in declared-`any` positions are typed `any` (spec
      -- §Defaults); multi-sig class equations have no single column
      -- of declared types, so nothing is stamped there.
      stamped = case effSig of
        Just (argTys, _, _) -> paramVarSkeletons env eq.params argTys eq.guards
        Nothing -> Map.empty
  varTypes <- allocVarTypes allVarNames stamped
  case effSig of
    -- Single-sig (untyped, bounded, or unbounded): allocate the
    -- function's declared tvars as rigid for this equation. Calls
    -- inside the body that target the rigid tvars must resolve
    -- through ambient signatures contributed by a `requiring`
    -- clause; without a matching clause, an overloaded operator at
    -- the tvar fails with @no_matching_overload@. Empty @bounds@ is
    -- fine — it just means no ambient signatures are emitted.
    Just (argTys, retTy, bounds) -> do
      unit <- freshUnitId
      recordHsDiags unit (equationConstructorArities env func eq)
      checkSingleSigEquation unit func (argTys, retTy) bounds varTypes eq
    -- Multi-sig (class) equations never reach this function: they
    -- are checked per candidate signature in isolated sessions by
    -- 'checkClassFunction' (typeCheckProgram partitions them out).
    Nothing -> pure ()

-- | Check an equation of a single-signature function (bounded or
-- unbounded). Allocates the function's declared type variables as
-- *rigid* identities, shared between the equation's parameter types,
-- RHS type, and any ambient signatures contributed by a @requiring@
-- clause. The rigid identity is what makes the spec's "the ambient
-- signature's type variables share identity with the enclosing
-- function's declared type variables" property hold: a call to a
-- bound-named function inside the equation that resolves through the
-- ambient sig stays polymorphic in T, because T is the SAME rigid
-- term the equation parameters' types are bound to. Rigidity also
-- closes the soundness gap for /unbounded/ polymorphic functions:
-- @foo(T, T) -> bool@ with body @X > Y@ now fails to type-check
-- (no_matching_overload on @>@), because there is no ambient sig and
-- no declared sig of @>@ is consistent with the rigid @T@.
checkSingleSigEquation ::
  UnitId ->
  D.Function ->
  ([TypeExpr], TypeExpr) ->
  [BoundSig] ->
  Map Text Value ->
  D.Equation ->
  TC ()
checkSingleSigEquation unit func (argTys, retTy) bounds varTypes eq = do
  let allVars =
        collectTypeVars argTys
          ++ collectTypeVarsExpr retTy
          ++ concatMap boundSigVars bounds
  tvars <- freshRigidTypeVarsForDecl allVars
  encodedArgs <- chrOp (traverse (encodeTypeExpr tvars) argTys)
  encodedRet <- chrOp (encodeTypeExpr tvars retTy)
  -- Each equation is its own checking unit, including each equation
  -- contributed by an `:- extend_function` / `:- extend_class`
  -- directive: they share the owning declaration's 'AnnP' location,
  -- so the 'UnitId' the caller allocated is what keeps their
  -- diagnostics apart.
  let AnnP _ eqLoc eqOrigin = func.equations
      baseCtx =
        CheckCtx
          { varTypes,
            label = Just ("function " <> flattenName (Types.qualifiedToName func.name)),
            loc = eqLoc,
            origin = eqOrigin,
            ambientSigs = Map.empty,
            unitId = unit
          }
  ctx <- freshCtxHandle baseCtx
  ebs <- traverse (encodeBoundSig tvars) bounds
  let ambMap =
        Map.fromListWith
          (++)
          [ (AmbientKey eb.boundName (length eb.boundArgs), [eb.boundSigValue])
          | eb <- ebs
          ]
      cctx = baseCtx {ambientSigs = ambMap}
  -- Equation-site bound checks: each bound trivially discharges
  -- through the ambient signature it just contributed (identity
  -- sharing at the rigid tvars).
  zipWithM_ (tellEquationBound cctx ctx) bounds ebs
  paramTypes <- traverse (typeOfTerm cctx . headArgToTerm) eq.params
  zipWithM_ (tellCheckUnify ctx) paramTypes encodedArgs
  -- Guards are gathered between the parameters and the body, matching
  -- the operational order (an equation's guards run after pattern
  -- matching and before the RHS). Spec §The evidence criterion makes
  -- this order load-bearing: a guard's typing fact must already be
  -- told when the prelude and RHS constraints are gathered.
  -- An equation's parameters and guards share its 'AnnP' source, so
  -- both attributions are the same context here.
  checkGuards GuardCtxs {userGuardCtx = cctx, patternCtx = cctx} eq.guards
  cctx' <- checkFunStmts cctx eq.prelude
  rhsType <- typeOfExpr cctx' eq.rhs
  tellCheckUnify ctx rhsType encodedRet

-- ---------------------------------------------------------------------------
-- Term typing
-- ---------------------------------------------------------------------------

-- | Look up a source variable's pre-allocated type slot.
-- 'collectVarsInRule' / 'collectVarsInEq' walk the same nodes that
-- 'typeOfTerm' / @checkGuard@ / @checkBodyGoal@ visit, so every
-- variable has an entry in 'CheckCtx.varTypes' before type checking
-- begins. A missing entry signals a broken invariant in the desugarer
-- or the variable collector.
varType :: CheckCtx -> Text -> Chr Value
varType cctx v = case Map.lookup v cctx.varTypes of
  Just val -> pure val
  Nothing -> error ("TypeCheck.varType: missing var slot for " <> T.unpack v)

-- | Type a 'Term' at a value position. Used for the 'Term'-typed slots
-- the desugared AST still carries: head occurrence arguments and the
-- 'GuardMatch' / 'GuardGetArg' operand of head normal-form guards.
-- Every 'CompoundTerm' is treated as a data-constructor application —
-- call vs constructor disambiguation has been moved upstream into the
-- 'D.Expr' AST.
typeOfTerm :: CheckCtx -> Term -> TC Value
typeOfTerm cctx (VarTerm v) = chrOp (varType cctx v)
typeOfTerm _ (IntTerm _) = pure (tcCon0 "int")
typeOfTerm _ (FloatTerm _) = pure (tcCon0 "float")
typeOfTerm _ (TextTerm _) = pure (tcCon0 "string")
typeOfTerm _ Wildcard = chrOp newVar
typeOfTerm cctx (CompoundTerm name args) =
  typeOfTermCtor cctx name args

-- | Type a 'Term'-shaped constructor application. Used for the
-- 'Term'-typed positions that the desugared AST still carries: head
-- arguments (via 'headArgToTerm').
--
-- Head/equation patterns are unevaluated: a compound whose head
-- happens to name a declared function is still a literal term in
-- pattern position, never a call. We therefore treat every compound
-- as a constructor application here. Calls inside expression positions
-- are handled structurally by 'typeOfExpr' against 'R.CallExpr'.
typeOfTermCtor :: CheckCtx -> Name -> [Term] -> TC Value
typeOfTermCtor cctx name args = do
  env <- ask
  let arity = length args
      canonical = canonicalizeConName env name
  if knownConstructorWithArity env canonical arity
    then do
      argTypes <- traverse (typeOfTerm cctx) args
      resultType <- chrOp newVar
      ctx <- freshCtxHandle cctx
      chrOp $
        tellConstraint
          (Qualified "$typechecker" "check_constructor_use")
          [ VAtom (runtimeName canonical),
            valueList argTypes,
            resultType,
            ctxHandleValue ctx
          ]
      pure resultType
    else do
      mapM_ (typeOfTerm cctx) args
      pure (tcCon0 "any")

-- | Type an expression. Each 'D.Expr' constructor maps to a specific
-- typechecker query; the call-vs-constructor split is structural here,
-- replacing the legacy @typeOfCompound@'s @funSet@ membership test.
typeOfExpr :: CheckCtx -> D.Expr -> TC Value
typeOfExpr cctx e = case e of
  R.VarExpr v -> chrOp (varType cctx v)
  R.IntExpr _ -> pure (tcCon0 "int")
  R.FloatExpr _ -> pure (tcCon0 "float")
  R.TextExpr _ -> pure (tcCon0 "string")
  R.WildcardExpr -> chrOp newVar
  R.CtorExpr name args -> typeOfExprCtor cctx name args
  R.CallExpr qn args -> do
    argTypes <- traverse (typeOfExpr cctx) args
    resultType <- chrOp newVar
    emitFunctionCall cctx (Types.qualifiedToName qn) argTypes resultType
    pure resultType
  R.ApplyExpr f args -> do
    _ <- typeOfExpr cctx f
    mapM_ (typeOfExpr cctx) args
    pure (tcCon0 "any")
  R.HostExpr _ args -> do
    mapM_ (typeOfExpr cctx) args
    pure (tcCon0 "any")
  R.FunRefExpr qn arity -> do
    argTypeVars <- chrOp (replicateM arity newVar)
    retTypeVar <- chrOp newVar
    emitFunctionRef cctx (Types.qualifiedToName qn) argTypeVars retTypeVar
    pure (VTerm (tcAtom "fun") [valueList argTypeVars, retTypeVar])
  R.LambdaExpr params body -> do
    -- Lambda parameters shadow same-named enclosing variables: each
    -- name gets a fresh flexible slot (spec §Lambdas — "each
    -- parameter is typed by a fresh flexible variable"), so the
    -- lambda neither inherits the outer variable's type nor leaks
    -- its own back out. The runtime shadows too: the lifter
    -- subtracts parameter names from the captured set. A repeated
    -- parameter name shares one slot across its positions, keeping
    -- the two positions' types linked (as a named equation's
    -- repeated pattern variable does through its shared varTypes
    -- entry).
    (paramBindings, paramTypeVars) <- foldParams params
    let bodyCctx = cctx {varTypes = Map.union paramBindings cctx.varTypes}
        -- Type each non-final body item; the lambda's value type is
        -- the type of its trailing return expression.
        initExprs = NE.init body
        lastExpr = NE.last body
    mapM_ (typeOfExpr bodyCctx) initExprs
    bodyType <- typeOfExpr bodyCctx lastExpr
    pure (VTerm (tcAtom "fun") [valueList paramTypeVars, bodyType])
  where
    foldParams ps = do
      (m, slotsRev) <- foldM step (Map.empty, []) (NE.toList ps)
      pure (m, reverse slotsRev)
      where
        step (m, acc) (HeadVar v)
          | Just slot <- Map.lookup v m = pure (m, slot : acc)
          | otherwise = do
              slot <- chrOp newVar
              pure (Map.insert v slot m, slot : acc)
        step (m, acc) HeadWildcard = do
          slot <- chrOp newVar
          pure (m, slot : acc)

-- | Type a 'CtorExpr' application, recursing into the arguments with
-- the given typing function so both the evaluated and the structural
-- expression modes share the constructor logic: constructors with a
-- known declared arity emit @check_constructor_use@; everything else
-- falls back to @any@.
typeOfCtorWith ::
  (CheckCtx -> D.Expr -> TC Value) ->
  CheckCtx ->
  Name ->
  [D.Expr] ->
  TC Value
typeOfCtorWith recur cctx name args = do
  env <- ask
  let arity = length args
      canonical = canonicalizeConName env name
  if knownConstructorWithArity env canonical arity
    then do
      argTypes <- traverse (recur cctx) args
      resultType <- chrOp newVar
      ctx <- freshCtxHandle cctx
      chrOp $
        tellConstraint
          (Qualified "$typechecker" "check_constructor_use")
          [ VAtom (runtimeName canonical),
            valueList argTypes,
            resultType,
            ctxHandleValue ctx
          ]
      pure resultType
    else do
      mapM_ (recur cctx) args
      pure (tcCon0 "any")

-- | Type a 'CtorExpr' application in evaluated mode. Mirrors
-- 'typeOfTermCtor' for the typed-expression side.
typeOfExprCtor :: CheckCtx -> Name -> [D.Expr] -> TC Value
typeOfExprCtor = typeOfCtorWith typeOfExpr

-- | Type an expression in /structural/ mode: the typing of the
-- operands of @=@ (spec §Expression Typing). The runtime treats these
-- positions structurally ('YCHR.Internal.Compile' lowers them through
-- 'R.exprToTerm'), so the checker must too: a compound whose functor
-- names a declared function or class is a symbolic, evaluable-headed
-- term typed @any@ — not a call, so no @check_function_use@ is
-- emitted and no warning is drawn. Host calls and @'$call'@s under
-- @=@ likewise become symbolic compounds typed @any@. Constructor
-- typing still applies (structural positions are typed by
-- constructor typing alone), recursing structurally into the fields.
--
-- 'R.FunRefExpr' and 'R.LambdaExpr' delegate to the evaluated mode:
-- under @=@ they lower to callable values (the canonical
-- @'/'(name, arity)@ dispatch compound and the lifted closure), not
-- dead data, so they keep their @fun@ types.
typeOfExprStructural :: CheckCtx -> D.Expr -> TC Value
typeOfExprStructural cctx e = case e of
  R.VarExpr v -> chrOp (varType cctx v)
  R.IntExpr _ -> pure (tcCon0 "int")
  R.FloatExpr _ -> pure (tcCon0 "float")
  R.TextExpr _ -> pure (tcCon0 "string")
  R.WildcardExpr -> chrOp newVar
  R.CtorExpr name args -> typeOfCtorWith typeOfExprStructural cctx name args
  R.CallExpr _ args -> do
    mapM_ (typeOfExprStructural cctx) args
    pure (tcCon0 "any")
  R.ApplyExpr f args -> do
    _ <- typeOfExprStructural cctx f
    mapM_ (typeOfExprStructural cctx) args
    pure (tcCon0 "any")
  R.HostExpr _ args -> do
    mapM_ (typeOfExprStructural cctx) args
    pure (tcCon0 "any")
  R.FunRefExpr {} -> typeOfExpr cctx e
  R.LambdaExpr {} -> typeOfExpr cctx e

-- ---------------------------------------------------------------------------
-- Variable collection
-- ---------------------------------------------------------------------------

collectVarsInRule :: D.Rule -> Set Text
collectVarsInRule rule =
  let AnnP hd _ _ = rule.head
      AnnP guards _ _ = rule.guard
      AnnP body _ _ = rule.body
      headCs = map headConstraintToConstraint (hd.kept ++ hd.removed)
   in mconcat
        [ foldMap collectVarsInConstraint headCs,
          foldMap collectVarsInGuard guards,
          foldMap collectVarsInBodyGoal body
        ]

collectVarsInEq :: D.Equation -> Set Text
collectVarsInEq eq =
  mconcat
    [ foldMap collectVarsInHeadArg eq.params,
      foldMap collectVarsInGuard eq.guards,
      foldMap collectVarsInFunStmt eq.prelude,
      collectVarsInExpr eq.rhs
    ]

collectVarsInFunStmt :: D.FunStmt -> Set Text
collectVarsInFunStmt (D.FunIs v e) = Set.singleton v <> collectVarsInExpr e
collectVarsInFunStmt (D.FunHostStmt _ args) = foldMap collectVarsInExpr args
collectVarsInFunStmt (D.FunCall _ args) = foldMap collectVarsInExpr args
collectVarsInFunStmt (D.FunApply f args) =
  collectVarsInExpr f <> foldMap collectVarsInExpr args

collectVarsInConstraint :: Types.QualifiedConstraint -> Set Text
collectVarsInConstraint c = foldMap collectVarsInTerm c.args

collectVarsInHeadArg :: HeadArg -> Set Text
collectVarsInHeadArg (HeadVar v) = Set.singleton v
collectVarsInHeadArg HeadWildcard = Set.empty

collectVarsInGuard :: D.Guard -> Set Text
collectVarsInGuard (D.GuardEqual e1 e2) = collectVarsInExpr e1 <> collectVarsInExpr e2
collectVarsInGuard (D.GuardMatch e _ _) = collectVarsInExpr e
collectVarsInGuard (D.GuardGetArg v e _) = Set.singleton v <> collectVarsInExpr e
collectVarsInGuard (D.GuardExpr e) = collectVarsInExpr e

collectVarsInBodyGoal :: D.BodyGoal -> Set Text
collectVarsInBodyGoal D.BodyTrue = Set.empty
collectVarsInBodyGoal (D.BodyTell _ args) = foldMap collectVarsInExpr args
collectVarsInBodyGoal (D.BodyUnify e1 e2) = collectVarsInExpr e1 <> collectVarsInExpr e2
collectVarsInBodyGoal (D.BodyHostStmt _ args) = foldMap collectVarsInExpr args
collectVarsInBodyGoal (D.BodyIs v e) = Set.singleton v <> collectVarsInExpr e
collectVarsInBodyGoal (D.BodyCall _ args) = foldMap collectVarsInExpr args
collectVarsInBodyGoal (D.BodyApply f args) =
  collectVarsInExpr f <> foldMap collectVarsInExpr args

collectVarsInTerm :: Term -> Set Text
collectVarsInTerm (VarTerm v) = Set.singleton v
collectVarsInTerm (CompoundTerm _ args) = foldMap collectVarsInTerm args
collectVarsInTerm _ = Set.empty

-- | Collect every variable name an expression mentions, including
-- lambda parameter names. Type-slot allocation needs *all* names
-- (lambda params become local bindings the typechecker must type),
-- which is wider than what the lambda lifter uses when computing
-- captures.
collectVarsInExpr :: D.Expr -> Set Text
collectVarsInExpr (R.VarExpr v) = Set.singleton v
collectVarsInExpr (R.CtorExpr _ args) = foldMap collectVarsInExpr args
collectVarsInExpr (R.CallExpr _ args) = foldMap collectVarsInExpr args
collectVarsInExpr (R.ApplyExpr f args) =
  collectVarsInExpr f <> foldMap collectVarsInExpr args
collectVarsInExpr (R.HostExpr _ args) = foldMap collectVarsInExpr args
collectVarsInExpr (R.LambdaExpr params body) =
  Set.fromList [v | HeadVar v <- NE.toList params]
    <> foldMap collectVarsInExpr (NE.toList body)
collectVarsInExpr _ = Set.empty

-- ---------------------------------------------------------------------------
-- Diagnostic collection
-- ---------------------------------------------------------------------------

-- | Drain both accumulators and apply per-unit warning suppression: a
-- unit that reports an error omits its warnings (spec §Inaccessible
-- branches). Warnings never suppress errors, so the error list passes
-- through untouched.
collectDiagnostics :: TC TypeCheckResult
collectDiagnostics = do
  store <- getStore
  let hsErrs = reverse store.hsDiags
  chrErrs <- collectErrors
  warns <- collectWarnings
  let errs = hsErrs ++ chrErrs
      errorUnits = Set.fromList (map fst errs)
  pure
    TypeCheckResult
      { errors = map snd errs,
        warnings = [w | (unit, w) <- warns, not (Set.member unit errorUnits)]
      }

collectErrors :: TC [(UnitId, Diagnostic TypeCheckError)]
collectErrors = do
  errVar <- chrOp newVar
  chrOp (tellConstraint (Qualified "$typechecker" "collect") [errVar])
  errVal <- chrOp (deref errVar)
  store <- getStore
  chrOp (decodeDiagnosticList (tcAtom "error") decodeError store.ctxMap errVal)

collectWarnings :: TC [(UnitId, Diagnostic TypeCheckWarning)]
collectWarnings = do
  warnVar <- chrOp newVar
  chrOp (tellConstraint (Qualified "$typechecker" "collect_warnings") [warnVar])
  warnVal <- chrOp (deref warnVar)
  store <- getStore
  chrOp (decodeDiagnosticList (tcAtom "warning") decodeWarning store.ctxMap warnVal)

-- | Decode one accumulator's list. Both accumulators hold terms of the
-- same @f(Ctx, Code, Detail)@ shape; @functor@ names the expected one
-- and @decodeBody@ turns a decoded @(Code, Detail)@ pair into the
-- diagnostic payload.
decodeDiagnosticList ::
  Text ->
  (Value -> Value -> Chr a) ->
  CtxMap ->
  Value ->
  Chr [(UnitId, Diagnostic a)]
decodeDiagnosticList functor decodeBody ctxMap val =
  case fromValueList val of
    Just items -> traverse decodeItem items
    Nothing -> pure []
  where
    decodeItem item = do
      item' <- deref item
      case item' of
        VTerm f [ctxValRaw, codeVal, detailVal]
          | f == functor -> do
              ctxVal <- deref ctxValRaw
              let info = lookupCtxInfo ctxMap ctxVal
              code <- deref codeVal
              detail <- deref detailVal
              payload <- decodeBody code detail
              pure (info.unit, Diagnostic info.label (AnnP payload info.loc info.origin))
        _ ->
          error
            ( "TypeCheck.decodeDiagnosticList: malformed "
                <> T.unpack (displayQualifiedAtom functor)
                <> " term: "
                <> showValueShape item'
            )

-- | Recover a handle's source-location info. A handle that is not in
-- the map (or not an integer at all) means the CHR program invented a
-- @Ctx@ value, which no rule may do.
lookupCtxInfo :: CtxMap -> Value -> CtxInfo
lookupCtxInfo ctxMap ctxVal = case ctxVal of
  VInt n ->
    Map.findWithDefault
      (error ("TypeCheck.lookupCtxInfo: orphan Ctx handle " <> show n))
      (CtxHandle (fromInteger n))
      ctxMap
  _ ->
    error
      ( "TypeCheck.lookupCtxInfo: non-Int Ctx value: "
          <> showValueShape ctxVal
      )

decodeError :: Value -> Value -> Chr TypeCheckError
decodeError code detail = case code of
  VAtom c | c == tcAtom "inconsistent" -> do
    (t1text, t2text) <- decodeTypePair detail
    pure (InconsistentTypes t1text t2text)
  VAtom c
    | c == tcAtom "no_matching_overload" ->
        NoMatchingOverload <$> showValue detail
  VAtom c
    | c == tcAtom "bound_unsatisfied" ->
        BoundUnsatisfied <$> showValue detail
  VAtom c ->
    error
      ( "TypeCheck.decodeError: unknown error code "
          <> T.unpack (displayQualifiedAtom c)
      )
  _ -> error "TypeCheck.decodeError: malformed error code value"

decodeWarning :: Value -> Value -> Chr TypeCheckWarning
decodeWarning code detail = case code of
  VAtom c | c == tcAtom "inaccessible" -> do
    (t1text, t2text) <- decodeTypePair detail
    pure (InaccessibleBranch t1text t2text)
  VAtom c ->
    error
      ( "TypeCheck.decodeWarning: unknown warning code "
          <> T.unpack (displayQualifiedAtom c)
      )
  _ -> error "TypeCheck.decodeWarning: malformed warning code value"

-- | Render a @pair(T1, T2)@ detail as the two types' source syntax.
decodeTypePair :: Value -> Chr (Text, Text)
decodeTypePair detail = case detail of
  VTerm pf [t1, t2] | pf == tcAtom "pair" -> do
    t1' <- deepDerefType t1
    t2' <- deepDerefType t2
    pure (showType t1', showType t2')
  _ -> pure ("?", "?")

-- | Dereference a type value through every nesting level, so
-- 'showType' (a pure function) sees the solved types rather than
-- bound-variable placeholders. This is what lets a pinned rigid's
-- cell, or a solved type-constructor argument, print as its type
-- instead of @_@.
deepDerefType :: Value -> Chr Value
deepDerefType v = do
  v' <- deref v
  case v' of
    VTerm f args -> VTerm f <$> traverse deepDerefType args
    _ -> pure v'

-- | One-line description of a runtime 'Value''s outer shape, used only
-- in 'error' messages for broken-invariant cases while decoding the
-- diagnostic accumulators.
showValueShape :: Value -> String
showValueShape (VTerm f xs) =
  "VTerm " <> T.unpack f <> "/" <> show (length xs)
showValueShape (VAtom a) = "VAtom " <> T.unpack a
showValueShape (VInt _) = "VInt"
showValueShape (VFloat _) = "VFloat"
showValueShape (VText _) = "VText"
showValueShape (VBool _) = "VBool"
showValueShape (VVar _) = "VVar"
showValueShape VWildcard = "VWildcard"

showType :: Value -> Text
showType (VAtom a) = displayTypeAtom a
showType (VTerm functor [a, b])
  | functor == tcAtom "tcon" =
      let name = showTypeName a
       in case fromValueList b of
            Just [] -> name
            Just as -> name <> "(" <> T.intercalate ", " (map showType as) <> ")"
            Nothing -> name <> "(?)"
  | functor == tcAtom "fun" =
      case fromValueList a of
        Just as -> "fun(" <> T.intercalate ", " (map showType as) <> ") -> " <> showType b
        Nothing -> "fun(?) -> " <> showType b
-- Rigid type variable: rendered with its synthetic id so distinct
-- rigids are distinguishable in inconsistency messages. The original
-- source-level tvar name (@T@, @A@, ...) is not preserved because the
-- driver does not currently maintain an id-to-name map; @T#<n>@ is
-- enough to communicate "this is a polymorphic type variable" to the
-- reader. A skolem pinned by guard-derived evidence is rendered as
-- the type it was pinned to — that is the type the reader's guard
-- established. ('decodeTypePair' deep-dereferences first, so a bound
-- cell arrives here as a concrete type rather than a variable.)
showType (VTerm functor [cell, VInt n])
  | functor == tcAtom "rigid" = case cell of
      VVar _ -> "T#" <> T.pack (show n)
      pinned -> showType pinned
showType (VVar _) = "_"
showType (VInt n) = T.pack (show n)
showType _ = "?"

showTypeName :: Value -> Text
showTypeName (VAtom a) = displayTypeAtom a
showTypeName _ = "?"

showValue :: Value -> Chr Text
showValue v = do
  v' <- deref v
  case v' of
    VAtom a -> pure (displayQualifiedAtom a)
    _ -> pure "?"

-- | Convert a runtime-flattened qualified atom (@m__n@) back to the
-- source-level display form (@m:n@). No-op when the atom doesn't
-- contain @__@. Used in error messages so users see familiar syntax.
-- Inverse of 'runtimeName'.
displayQualifiedAtom :: Text -> Text
displayQualifiedAtom = T.replace "__" ":"

-- | Like 'displayQualifiedAtom', but additionally undoes the internal
-- spelling of the built-in types: the @'$typechecker'@ module
-- qualifier and the @ty_@ constructor prefix both come off, so
-- @$typechecker__ty_int@ renders as @int@. User-defined types stay
-- module-qualified. Inverse of 'tcBaseAtom'; this is the only place a
-- @$typechecker@ atom becomes user-visible text, so it is the only
-- place that has to know about the prefix.
displayTypeAtom :: Text -> Text
displayTypeAtom t =
  let q = displayQualifiedAtom t
   in case T.stripPrefix "$typechecker:" q of
        Nothing -> q
        Just base -> fromMaybe base (T.stripPrefix "ty_" base)

-- ---------------------------------------------------------------------------
-- Type definition validation (pure, Haskell-side)
-- ---------------------------------------------------------------------------

validateTypeDefinitions ::
  [TypeDefinition] ->
  Map (Name, Int) TypeDefinition ->
  [Diagnostic TypeCheckError]
validateTypeDefinitions tds typeMap =
  concatMap (validateTypeDef typeMap) tds

validateTypeDef ::
  Map (Name, Int) TypeDefinition -> TypeDefinition -> [Diagnostic TypeCheckError]
validateTypeDef typeMap td =
  concatMap (validateConstructor typeMap td) (typeConstructors td)

validateConstructor ::
  Map (Name, Int) TypeDefinition ->
  TypeDefinition ->
  DataConstructor ->
  [Diagnostic TypeCheckError]
validateConstructor typeMap td dc =
  concatMap (validateFieldType typeMap td dc) dc.conArgs

-- | The validation map is keyed by (name, arity) — the identity the
-- renamer and the collision checks commit to — so arity-overloaded
-- types (wrap/1 alongside wrap/2) validate correctly. A reference
-- found under its exact key is well-formed by construction; a miss
-- dispatches between the arity-mismatch and undefined-type
-- diagnostics.
validateFieldType ::
  Map (Name, Int) TypeDefinition ->
  TypeDefinition ->
  DataConstructor ->
  TypeExpr ->
  [Diagnostic TypeCheckError]
validateFieldType typeMap td dc fieldTy = case fieldTy of
  TypeVar v
    | v `elem` td.typeVars -> []
    | otherwise ->
        [fieldDiag (UnboundTypeVar (flattenName td.name) (flattenName dc.conName) v)]
  -- Function type: fun(A, B) -> C is parsed as
  -- TypeCon "->" [TypeCon "fun" [A, B], C]; mirror 'encodeTypeExpr'.
  TypeCon (Unqualified "->") [TypeCon (Unqualified "fun") argTys, retTy] ->
    concatMap recur (argTys ++ [retTy])
  TypeCon name args ->
    let arityDiag declared =
          fieldDiag
            ( TypeRefArityMismatch
                (flattenName td.name)
                (flattenName dc.conName)
                (flattenName name)
                (length args)
                declared
            )
        isBuiltin = case name of
          Unqualified n -> n `elem` ["int", "float", "string", "any"]
          Qualified _ _ -> False
        nameErrors
          | Map.member (name, length args) typeMap = []
          | isBuiltin = if null args then [] else [arityDiag 0]
          -- The renamer resolves type names by (name, arity), so a
          -- reference at the wrong arity stays Unqualified and
          -- misses the typeMap. When a declaration with the same
          -- base name exists at exactly one other arity, report the
          -- arity mismatch it denotes rather than a misleading
          -- UndefinedType (spec: "bar(list) is an error if list is
          -- declared as list(A)").
          | [declared] <- baseNameArities = [arityDiag declared]
          | otherwise =
              [ fieldDiag
                  ( UndefinedType
                      (flattenName td.name)
                      (flattenName dc.conName)
                      (flattenName name)
                  )
              ]
     in nameErrors ++ concatMap recur args
  where
    recur = validateFieldType typeMap td dc
    fieldDiag err =
      Diagnostic Nothing (AnnP err td.loc (Atom (flattenName td.name)))
    baseNameArities = case fieldTy of
      TypeCon name _ ->
        List.nub
          [ arity
          | ((declName, arity), _) <- Map.toList typeMap,
            typeBaseName declName == typeBaseName name
          ]
      _ -> []
    typeBaseName (Qualified _ n) = n
    typeBaseName (Unqualified n) = n

-- ---------------------------------------------------------------------------
-- Constructor arity validation (pure, Haskell-side)
-- ---------------------------------------------------------------------------

-- | Every use of a known data constructor at the wrong arity in one
-- rule. Computed in Haskell rather than by a CHR rule so the
-- diagnostic is a direct ConstructorArityMismatch rather than a
-- downstream tcon inconsistency: the check phase silently skips
-- wrong-arity sites (treating them as @any@), so this error is the
-- only one reported for such uses.
--
-- Reported per checking unit — 'checkRule' and 'checkEquation' record
-- these against the unit they are checking — so that warning
-- suppression sees them (a unit with an error omits its warnings;
-- were these still a whole-program pre-pass, a unit whose /only/
-- error is an arity mismatch would emit no CHR error and its warnings
-- would survive).
ruleConstructorArities :: TypeCheckEnv -> D.Rule -> [Diagnostic TypeCheckError]
ruleConstructorArities env rule =
  let AnnP hd headLoc headOrigin = rule.head
      AnnP guards guardLoc guardOrigin = rule.guard
      AnnP body bodyLoc bodyOrigin = rule.body
      ruleLabel = fmap (\n -> "rule " <> n) rule.name
      headArgs = concatMap (map headArgToTerm . (.args)) (hd.kept ++ hd.removed)
      inHead = foldMap (termArity env) headArgs
      inGuards = foldMap (guardArity env) guards
      inBody = foldMap (bodyArity env) body
   in mkArityDiags ruleLabel headLoc headOrigin inHead
        ++ mkArityDiags ruleLabel guardLoc guardOrigin inGuards
        ++ mkArityDiags ruleLabel bodyLoc bodyOrigin inBody

-- | The same, for one equation of a function. All equations of a
-- function share the declaration's 'AnnP', so the diagnostics of two
-- equations differ only in their content.
equationConstructorArities ::
  TypeCheckEnv -> D.Function -> D.Equation -> [Diagnostic TypeCheckError]
equationConstructorArities env func eq =
  let AnnP _ loc origin = func.equations
      funLabel = Just ("function " <> flattenName (Types.qualifiedToName func.name))
   in mkArityDiags funLabel loc origin (eqArity env eq)

-- | The equations of a whole function. Used for multi-signature class
-- functions, whose equations are checked in throwaway per-signature
-- sessions: their diagnostics are discarded, so these must be
-- collected at program level instead.
functionConstructorArities :: TypeCheckEnv -> D.Function -> [Diagnostic TypeCheckError]
functionConstructorArities env func =
  let AnnP eqs _ _ = func.equations
   in concatMap (equationConstructorArities env func) eqs

-- | One @(constructor, use arity, declared arity)@ triple per
-- offending use site.
type ArityUse = (Name, Int, Int)

eqArity :: TypeCheckEnv -> D.Equation -> [ArityUse]
eqArity env eq =
  foldMap (termArity env . headArgToTerm) eq.params
    <> foldMap (guardArity env) eq.guards
    <> exprArity env eq.rhs

guardArity :: TypeCheckEnv -> D.Guard -> [ArityUse]
guardArity env (D.GuardEqual e1 e2) = exprArity env e1 <> exprArity env e2
guardArity env (D.GuardMatch e conName arity) =
  checkArity env conName arity <> exprArity env e
guardArity env (D.GuardGetArg _ e _) = exprArity env e
guardArity env (D.GuardExpr e) = exprArity env e

bodyArity :: TypeCheckEnv -> D.BodyGoal -> [ArityUse]
bodyArity _ D.BodyTrue = mempty
bodyArity env (D.BodyTell _ args) = foldMap (exprArity env) args
bodyArity env (D.BodyUnify e1 e2) = exprArity env e1 <> exprArity env e2
bodyArity env (D.BodyIs _ e) = exprArity env e
bodyArity env (D.BodyCall _ args) = foldMap (exprArity env) args
bodyArity env (D.BodyApply f args) = exprArity env f <> foldMap (exprArity env) args
bodyArity env (D.BodyHostStmt _ args) = foldMap (exprArity env) args

-- | An atom is a 0-arity constructor use; a 'R.CtorExpr' is an n-arity
-- use. 'R.CallExpr', 'R.ApplyExpr', 'R.HostExpr', 'R.FunRefExpr', and
-- 'R.LambdaExpr' are not constructor applications: their children are
-- walked, but the heads themselves are not subjected to the arity
-- check.
exprArity :: TypeCheckEnv -> D.Expr -> [ArityUse]
exprArity env (R.CtorExpr name args) =
  checkArity env name (length args) <> foldMap (exprArity env) args
exprArity env (R.CallExpr _ args) = foldMap (exprArity env) args
exprArity env (R.ApplyExpr f args) = exprArity env f <> foldMap (exprArity env) args
exprArity env (R.HostExpr _ args) = foldMap (exprArity env) args
exprArity env (R.LambdaExpr _ body) = foldMap (exprArity env) (NE.toList body)
exprArity _ _ = mempty

-- | Walks the surviving 'Term'-typed positions in the desugared AST
-- (equation parameters). Pattern shapes that 'headTermToExpr' would
-- otherwise round-trip through @fun(...) -> body@ / @name/arity@ are
-- short-circuited here.
termArity :: TypeCheckEnv -> Term -> [ArityUse]
termArity
  _
  ( CompoundTerm
      (Unqualified "/")
      [CompoundTerm (Unqualified _) [], IntTerm _]
    ) = mempty
termArity env (CompoundTerm (Unqualified "->") [CompoundTerm (Unqualified "fun") _, body]) =
  termArity env body
termArity env (CompoundTerm name args) =
  checkArity env name (length args) <> foldMap (termArity env) args
termArity _ _ = mempty

checkArity :: TypeCheckEnv -> Name -> Int -> [ArityUse]
checkArity env name useArity =
  let canonical = canonicalizeConName env name
   in case Map.lookup canonical env.conMap of
        Just (_, dc)
          | length dc.conArgs /= useArity ->
              [(canonical, useArity, length dc.conArgs)]
        _ -> []

mkArityDiags ::
  Maybe Text -> SourceLoc -> PExpr -> [ArityUse] -> [Diagnostic TypeCheckError]
mkArityDiags lbl loc origin =
  map
    ( \(name, useArity, declaredArity) ->
        Diagnostic
          lbl
          ( AnnP
              (ConstructorArityMismatch (flattenName name) useArity declaredArity)
              loc
              origin
          )
    )
