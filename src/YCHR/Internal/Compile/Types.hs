-- | Internal types for the CHR-to-VM compiler.
module YCHR.Internal.Compile.Types
  ( -- * Errors
    CompileError (..),

    -- * Semantic newtypes
    OccurrenceNumber (..),
    HeadPosition (..),
    PartnerIndex (..),

    -- * Data types
    Occurrence (..),
    occurrenceArity,
    GoalOccurrence (..),
    activeHeadPosition,
    Partner (..),
    AggregatePlan (..),
    ResultMatch (..),
    IndexCondition (..),
    CompiledGuards (..),
    CheckGuards (..),

    -- * Partner index conditions
    PartnerCondMap,

    -- * Occurrence map
    OccurrenceMap,
    occMapEmpty,
    occMapAppend,
    occMapMap,
    lookupOccurrences,
    CollectedOccurrences (..),

    -- * Variable map
    VarMap,
    varMapFromList,
    lookupVar,
    insertVar,
    notMemberVar,
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Types
  ( AggregateKind,
    HeadArg,
    HeadConstraint,
    Identifier,
    Name,
    RuleId,
    Term,
  )
import YCHR.Internal.Types qualified as Types
import YCHR.Internal.VM (ArgIndex, BoolExpr, ConstraintType, Stmt, ValExpr)
import YCHR.Internal.VM qualified as VM

-- | Errors raised by any pass in the CHR-to-VM compiler. Wrapped in
-- 'YCHR.Internal.Parsed.AnnP' at the use site to carry the source location and
-- original parsed expression for diagnostics.
data CompileError
  = -- | A head constraint references a constraint type that is not in
    -- the symbol table. Raised by 'YCHR.Internal.Compile.Occurrences'.
    UnknownConstraintType Types.Name
  | -- | A guard or body term references a variable that is not bound
    -- by the rule head. Raised by 'YCHR.Internal.Compile' while compiling
    -- terms.
    UnboundVariable Text
  | -- | A local variable of an aggregate is used in the rule's guard or
    -- body. Raised by 'YCHR.Internal.Compile.Aggregate'.
    AggregateLocalEscapes Text
  | -- | A recognized aggregate form the compiler does not implement yet,
    -- with the form's name and arity. Raised by
    -- 'YCHR.Internal.Compile.Aggregate'.
    AggregateNotImplemented Text Int
  | -- | A rule has an aggregate but the program does not declare
    -- @maybe:just/1@, the constructor an aggregator's @Final@ closure has
    -- to return. Raised by 'YCHR.Internal.Compile.Aggregate'.
    AggregateResultNotMaybe
  deriving (Show)

-- | 1-based occurrence number within a constraint type's occurrence list.
newtype OccurrenceNumber = OccurrenceNumber {unOccurrenceNumber :: Int}
  deriving (Show, Eq, Ord, Num, Enum)

-- | 0-based position in the combined (removed ++ kept) head list.
newtype HeadPosition = HeadPosition {unHeadPosition :: Int}
  deriving (Show, Eq, Ord, Num, Enum)

-- | 0-based index into the partners list of an occurrence.
newtype PartnerIndex = PartnerIndex {unPartnerIndex :: Int}
  deriving (Show, Eq, Ord, Num, Enum)

-- | One occurrence of a single head constraint within a rule. The
-- compiler emits one @occurrence_c_j@ procedure per 'Occurrence'.
data Occurrence = Occurrence
  { -- | Source name of the constraint this occurrence belongs to.
    conName :: Name,
    -- | 1-based position within the constraint's occurrence list.
    -- Assigned top-down in 'YCHR.Internal.Compile.collectOccurrences'.
    number :: OccurrenceNumber,
    -- | The full rule this occurrence belongs to. Carried so that
    -- 'genFireStmts' can read its guard, body, and head shape.
    rule :: D.Rule,
    -- | Numeric identifier of the rule, used as the propagation
    -- history key. Assigned by 'YCHR.Internal.Compile.collectOccurrences'
    -- from the rule's program-wide source position.
    ruleId :: RuleId,
    -- | Display name of the rule, used for diagnostics and
    -- 'YCHR.Internal.VM.StackFrame' labels. Equals @rule.name@ when
    -- the rule was explicitly named, otherwise a synthetic
    -- @__rule_N@ fallback.
    ruleDisplay :: Text,
    -- | Position of the active head constraint inside the rule's
    -- combined (removed ++ kept) head list.
    activeIdx :: HeadPosition,
    -- | Whether the active constraint is kept (@True@) or removed
    -- (@False@) when the rule fires.
    isKept :: Bool,
    -- | Arguments of the active head constraint, in source order.
    -- Narrowed to 'HeadArg' so the HNF invariant ("head args are
    -- variables or wildcards") is enforced by the type.
    activeArgs :: [HeadArg],
    -- | The other head constraints, in the order they will be iterated
    -- by nested 'YCHR.Internal.VM.Foreach' loops.
    partners :: [Partner],
    -- | The rule head's aggregates, planned once for the rule and carried
    -- by each of its occurrences. Empty for a rule without any.
    aggregates :: [AggregatePlan],
    -- | Whether ωr guarantees this occurrence can never fire with the
    -- active constraint in this role. Every occurrence is born active
    -- ('False') in 'YCHR.Internal.Compile.Occurrences.mkOccurrence'; the passivity
    -- pass 'YCHR.Internal.Compile.Passive.markPassive' flips it. A passive
    -- occurrence keeps its ωr 'number' (numbering runs first) but
    -- contributes no @occurrence_c_j@ procedure and no call from
    -- @activate_c@. See "YCHR.Internal.Compile.Passive" and
    -- @dev-docs/passive-occurrences.md@.
    passive :: Bool,
    -- | 'Just' for a goal occurrence: one CHR constraint conjunct of an
    -- aggregate goal, tried when a constraint of its type is activated.
    -- 'Nothing' for an ordinary head occurrence.
    --
    -- A goal occurrence's active constraint is not one of the rule's
    -- heads, so 'activeIdx' is meaningless for it: use
    -- 'activeHeadPosition'. 'isKept' is always 'True' (firing never
    -- removes the active goal constraint), and 'partners' is still only
    -- the regular heads, so every consumer that must see heads alone
    -- keeps working unchanged.
    goalOcc :: Maybe GoalOccurrence
  }

-- | What a goal occurrence matches: the conjunct of an aggregate goal
-- whose type this occurrence belongs to.
--
-- The active conjunct's arguments are carried by the occurrence
-- ('activeArgs'); its own HNF guards are the entry at 'goalActiveIndex'
-- of 'goalAll'. The location phase loops the other conjuncts of the goal
-- around the active conjunct's guards, so a guard that compares a
-- variable of an earlier conjunct with a fresh name sees the earlier
-- binding, and a later conjunct sees whatever the active guards bound.
data GoalOccurrence = GoalOccurrence
  { -- | Source index of the enclosing aggregate within the rule head.
    -- Used as the label prefix of the goal's loops.
    goalIndex :: Int,
    -- | Position of the active conjunct in 'goalAll'.
    goalActiveIndex :: Int,
    -- | Every conjunct of the goal, in goal order, including the active
    -- one. The location phase skips the active conjunct's loop (the
    -- active constraint already is it) but evaluates its guards in
    -- place.
    goalAll :: [D.AggregateConjunct],
    -- | The conjuncts of each enclosing goal, outermost first. Always
    -- empty until nested aggregates land.
    goalEnclosing :: [[D.AggregateConjunct]]
  }
  deriving (Show, Eq)

-- | Arity of an occurrence's active constraint, derived from
-- 'activeArgs'. This is a function rather than a stored field so the
-- two can never drift: 'YCHR.Internal.Desugar.normalizeArg' maps every
-- head term to exactly one 'HeadArg', so the active constraint's arity
-- always equals the length of 'activeArgs'.
occurrenceArity :: Occurrence -> Int
occurrenceArity occ = length occ.activeArgs

-- | The position of the occurrence's active /regular/ head, or
-- 'Nothing' for a goal occurrence, whose active constraint is not a
-- head. This is what every head-only consumer of 'activeIdx' —
-- 'YCHR.Internal.Compile.buildHistoryIds' and
-- 'YCHR.Internal.Compile.Passive.isLaterOccurrence' — has to go
-- through.
activeHeadPosition :: Occurrence -> Maybe HeadPosition
activeHeadPosition occ = case occ.goalOcc of
  Just _ -> Nothing
  Nothing -> Just occ.activeIdx

-- | One partner constraint of an 'Occurrence' — i.e. a head constraint
-- of the same rule that is /not/ the active one.
data Partner = Partner
  { -- | Position in the rule's combined (removed ++ kept) head list.
    idx :: HeadPosition,
    -- | The original constraint as it appears in the head, narrowed
    -- to 'HeadConstraint' (post-HNF).
    constraint :: HeadConstraint,
    -- | Whether the partner is kept (@True@) or removed (@False@) when
    -- the rule fires. Removed partners are killed before the body runs
    -- and skipped during backjumping (they are guaranteed dead).
    isKept :: Bool,
    -- | Constraint-type index used by 'YCHR.Internal.VM.Foreach' to look the
    -- partner up in the constraint store.
    cType :: ConstraintType
  }

-- | One head aggregate of a rule, as the compiler needs it: which
-- variables are inputs, which the procedure has to bind, and the goal its
-- fold runs over.
--
-- A plan is a function of the rule alone. Which of an aggregate's
-- variables are shared follows the spec's definition — the variables that
-- also occur in the rule's regular heads or in an earlier aggregate's
-- result — so it does not depend on which occurrence is active. One plan
-- therefore serves every occurrence of the rule and one procedure serves
-- them all.
data AggregatePlan = AggregatePlan
  { -- | Source order of this aggregate within the rule head.
    planIndex :: Int,
    planKind :: AggregateKind,
    -- | The procedure that computes it.
    planProcName :: VM.Name,
    planAgg :: Maybe D.Expr,
    planElement :: D.Expr,
    planGoal :: [D.AggregateConjunct],
    planResult :: Term,
    -- | Source variables the aggregate reads as inputs, in the canonical
    -- order the procedure's @aggregate_shared_N@ parameters and every call
    -- site use.
    planShared :: [Text],
    -- | Result variables the procedure binds, in the canonical order its
    -- @aggregate_out_N@ parameters use. Every other variable of the
    -- result pattern is either an input or a goal-local, so it is matched
    -- with an equality instead of bound.
    planBind :: [Text],
    -- | What the procedure does with the computed result: the tests the
    -- pattern has to pass and the out-cell bindings that follow them.
    planResultMatch :: ResultMatch
  }
  deriving (Show, Eq)

-- | A result pattern compiled against the computed payload: the tests it
-- has to pass, and the bindings of the variables it introduces.
--
-- The two lists are kept apart because every test runs before any
-- binding. A pattern that fails part way through therefore binds nothing:
-- the rule does not apply, and nothing is left half-done for the guard's
-- soft failure to abandon.
data ResultMatch = ResultMatch
  { -- | Structural tests, in pattern order.
    resultTests :: [BoolExpr],
    -- | One entry per variable the pattern binds, in traversal order: the
    -- source variable and the value subterm it has to agree with. The
    -- procedure binds it with @bunify\<out-cell\> \<subterm\>@, in the
    -- same order as 'planBind'.
    resultBinds :: [(Text, ValExpr)]
  }
  deriving (Show, Eq)

instance Semigroup ResultMatch where
  a <> b = ResultMatch (a.resultTests ++ b.resultTests) (a.resultBinds ++ b.resultBinds)

instance Monoid ResultMatch where
  mempty = ResultMatch [] []

-- | A single index condition lifted out of an equality check guard onto
-- a partner 'YCHR.Internal.VM.Foreach' loop: argument @argIndex@ of the partner
-- must be 'YCHR.Internal.VM.Equal' to @expectedValue@. Produced by
-- 'YCHR.Internal.Compile.classifyEqual' and consumed by
-- 'YCHR.Internal.Compile.wrapInPartnerLoops', which projects it back to the
-- @(ArgIndex, ValExpr)@ pair the VM 'YCHR.Internal.VM.Foreach' instruction expects.
data IndexCondition = IndexCondition
  { argIndex :: ArgIndex,
    expectedValue :: ValExpr
  }

-- | Per-partner index conditions lifted out of check guards by the
-- 'YCHR.Internal.VM.Foreach' index-condition pushdown optimization. Each entry
-- maps a partner index @k@ to the list of conditions that becomes
-- 'YCHR.Internal.VM.Foreach' @k@'s index-conditions argument.
type PartnerCondMap = Map PartnerIndex [IndexCondition]

-- | Result of compiling a guard conjunction. Threaded out of
-- 'YCHR.Internal.Compile.compileGuards' to its two callers (occurrence bodies
-- and function equations).
data CompiledGuards = CompiledGuards
  { -- | Wrapper that nests an inner statement block inside the
    -- structural @if@s and let-bindings introduced by match guards
    -- ('YCHR.Internal.Desugared.GuardMatch', 'YCHR.Internal.Desugared.GuardGetArg').
    matchWrapper :: [Stmt] -> [Stmt],
    -- | Index conditions lifted onto the surrounding partner
    -- 'YCHR.Internal.VM.Foreach' loops by 'YCHR.Internal.Compile.classifyEqual'. Empty
    -- when no occurrence context is available (function equations).
    indexConditions :: PartnerCondMap,
    -- | Residual boolean check that did not lift into the index map.
    -- 'Nothing' when every check guard lifted or when there were no
    -- check guards.
    residualCheck :: Maybe BoolExpr,
    -- | 'VarMap' extended with the bindings introduced by match
    -- guards.
    extendedVarMap :: VarMap
  }

-- | Result of compiling an occurrence's check guards: the index
-- conditions lifted onto partner loops, and the residual boolean
-- check that stays at the innermost guard position.
data CheckGuards = CheckGuards
  { indexConditions :: PartnerCondMap,
    residualCheck :: Maybe BoolExpr
  }

-- | Occurrences grouped by the constraint identifier they belong to
-- (constraint name and arity), in the order they were collected.
newtype OccurrenceMap = OccurrenceMap (Map.Map Identifier [Occurrence])

-- | The empty occurrence map.
occMapEmpty :: OccurrenceMap
occMapEmpty = OccurrenceMap Map.empty

-- | Add one occurrence to the list for its constraint identifier.
-- 'Data.Map.Strict.insertWith' prepends, so within a key the list is in
-- reverse insertion order until
-- 'YCHR.Internal.Compile.Occurrences.collectOccurrences' reverses and
-- numbers it.
occMapAppend :: Identifier -> Occurrence -> OccurrenceMap -> OccurrenceMap
occMapAppend k occ (OccurrenceMap m) = OccurrenceMap (Map.insertWith (++) k [occ] m)

-- | Map a function over every constraint's occurrence list.
occMapMap :: ([Occurrence] -> [Occurrence]) -> OccurrenceMap -> OccurrenceMap
occMapMap f (OccurrenceMap m) = OccurrenceMap (Map.map f m)

-- | The occurrences recorded for a constraint identifier, or the empty
-- list when the type has none.
lookupOccurrences :: Identifier -> OccurrenceMap -> [Occurrence]
lookupOccurrences k (OccurrenceMap m) = Map.findWithDefault [] k m

-- | Result of 'YCHR.Internal.Compile.Occurrences.collectOccurrences':
-- occurrences grouped by constraint type, plus the per-rule display
-- names used to populate 'YCHR.Internal.VM.Program''s @ruleNames@.
data CollectedOccurrences = CollectedOccurrences
  { -- | Occurrences grouped by constraint type and numbered in ωr order.
    occurrenceMap :: OccurrenceMap,
    -- | Display name of each rule, indexed by its 'RuleId'.
    ruleDisplayNames :: [Text],
    -- | Each rule's aggregates, planned once and indexed by its 'RuleId'.
    -- A rule without aggregates contributes an empty list, so a program
    -- that uses none carries no plan and generates no aggregate procedure.
    aggregatePlans :: [[AggregatePlan]]
  }

-- | Map from source-level variable names to the 'ValExpr' that holds
-- their value. The compiler stores only value bindings here; constraint
-- identifiers (partner ids, the active id) are referenced by their
-- generated names directly via 'YCHR.Internal.VM.IdVar' and never enter the map.
newtype VarMap = VarMap (Map.Map Text ValExpr)

-- | Build a 'VarMap' from source-variable/value pairs. A later
-- duplicate wins, as in 'Data.Map.Strict.fromList'.
varMapFromList :: [(Text, ValExpr)] -> VarMap
varMapFromList = VarMap . Map.fromList

-- | The 'ValExpr' bound to a source variable, if any.
lookupVar :: Text -> VarMap -> Maybe ValExpr
lookupVar k (VarMap m) = Map.lookup k m

-- | Bind a source variable to a 'ValExpr', replacing any existing
-- binding.
insertVar :: Text -> ValExpr -> VarMap -> VarMap
insertVar k v (VarMap m) = VarMap (Map.insert k v m)

-- | Whether a source variable is unbound in the map.
notMemberVar :: Text -> VarMap -> Bool
notMemberVar k (VarMap m) = Map.notMember k m
