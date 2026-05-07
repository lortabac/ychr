{-# LANGUAGE DuplicateRecordFields #-}

-- | Internal types for the CHR-to-VM compiler.
module YCHR.Compile.Types
  ( -- * Errors
    CompileError (..),

    -- * Semantic newtypes
    OccurrenceNumber (..),
    HeadPosition (..),
    PartnerIndex (..),

    -- * Data types
    Occurrence (..),
    Partner (..),
    IndexCondition (..),
    CompiledGuards (..),

    -- * Partner index conditions
    PartnerCondMap,

    -- * Occurrence map
    OccurrenceMap,
    occMapEmpty,
    occMapAppend,
    occMapMap,
    lookupOccurrences,

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
import YCHR.Desugared qualified as D
import YCHR.Types (Identifier, Name, QualifiedConstraint, RuleId, Term)
import YCHR.Types qualified as Types
import YCHR.VM (ArgIndex, ConstraintType, Expr, Stmt)

-- | Errors raised by any pass in the CHR-to-VM compiler. Wrapped in
-- 'YCHR.Parsed.AnnP' at the use site to carry the source location and
-- original parsed expression for diagnostics.
data CompileError
  = -- | A head constraint references a constraint type that is not in
    -- the symbol table. Raised by 'YCHR.Compile.Occurrences'.
    UnknownConstraintType Types.Name
  | -- | A guard or body term references a variable that is not bound
    -- by the rule head. Raised by 'YCHR.Compile' while compiling
    -- terms.
    UnboundVariable Text
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
    -- | Arity of the constraint (used for procedure-name encoding).
    conArity :: Int,
    -- | 1-based position within the constraint's occurrence list.
    -- Assigned top-down in 'YCHR.Compile.collectOccurrences'.
    number :: OccurrenceNumber,
    -- | The full rule this occurrence belongs to. Carried so that
    -- 'genFireStmts' can read its guard, body, and head shape.
    rule :: D.Rule,
    -- | Numeric identifier of the rule, used as the propagation
    -- history key. Assigned by 'YCHR.Compile.collectOccurrences'
    -- from the rule's program-wide source position.
    ruleId :: RuleId,
    -- | Display name of the rule, used for diagnostics and
    -- 'YCHR.VM.StackFrame' labels. Equals @rule.name@ when
    -- the rule was explicitly named, otherwise a synthetic
    -- @__rule_N@ fallback.
    ruleDisplay :: Text,
    -- | Position of the active head constraint inside the rule's
    -- combined (removed ++ kept) head list.
    activeIdx :: HeadPosition,
    -- | Whether the active constraint is kept (@True@) or removed
    -- (@False@) when the rule fires.
    isKept :: Bool,
    -- | Argument terms of the active head constraint, in source order.
    -- Always 'VarTerm' or 'Wildcard' thanks to HNF.
    activeArgs :: [Term],
    -- | The other head constraints, in the order they will be iterated
    -- by nested 'YCHR.VM.Foreach' loops.
    partners :: [Partner]
  }

-- | One partner constraint of an 'Occurrence' — i.e. a head constraint
-- of the same rule that is /not/ the active one.
data Partner = Partner
  { -- | Position in the rule's combined (removed ++ kept) head list.
    idx :: HeadPosition,
    -- | The original constraint as it appears in the head.
    constraint :: QualifiedConstraint,
    -- | Whether the partner is kept (@True@) or removed (@False@) when
    -- the rule fires. Removed partners are killed before the body runs
    -- and skipped during backjumping (they are guaranteed dead).
    isKept :: Bool,
    -- | Constraint-type index used by 'YCHR.VM.Foreach' to look the
    -- partner up in the constraint store.
    cType :: ConstraintType
  }

-- | A single index condition lifted out of an equality check guard onto
-- a partner 'YCHR.VM.Foreach' loop: argument @argIndex@ of the partner
-- must be 'YCHR.VM.Equal' to @expectedValue@. Produced by
-- 'YCHR.Compile.classifyEqual' and consumed by
-- 'YCHR.Compile.wrapInPartnerLoops', which projects it back to the
-- @(ArgIndex, Expr)@ pair the VM 'YCHR.VM.Foreach' instruction expects.
data IndexCondition = IndexCondition
  { argIndex :: ArgIndex,
    expectedValue :: Expr
  }

-- | Per-partner index conditions lifted out of check guards by the
-- 'YCHR.VM.Foreach' index-condition pushdown optimization. Each entry
-- maps a partner index @k@ to the list of conditions that becomes
-- 'YCHR.VM.Foreach' @k@'s index-conditions argument.
type PartnerCondMap = Map PartnerIndex [IndexCondition]

-- | Result of compiling a guard conjunction. Threaded out of
-- 'YCHR.Compile.compileGuards' to its two callers (occurrence bodies
-- and function equations).
data CompiledGuards = CompiledGuards
  { -- | Wrapper that nests an inner statement block inside the
    -- structural @if@s and let-bindings introduced by match guards
    -- ('YCHR.Desugared.GuardMatch', 'YCHR.Desugared.GuardGetArg').
    matchWrapper :: [Stmt] -> [Stmt],
    -- | Index conditions lifted onto the surrounding partner
    -- 'YCHR.VM.Foreach' loops by 'YCHR.Compile.classifyEqual'. Empty
    -- when no occurrence context is available (function equations).
    indexConditions :: PartnerCondMap,
    -- | Residual boolean check that did not lift into the index map.
    -- 'Nothing' when every check guard lifted or when there were no
    -- check guards.
    residualCheck :: Maybe Expr,
    -- | 'VarMap' extended with the bindings introduced by match
    -- guards.
    extendedVarMap :: VarMap
  }

newtype OccurrenceMap = OccurrenceMap (Map.Map Identifier [Occurrence])

occMapEmpty :: OccurrenceMap
occMapEmpty = OccurrenceMap Map.empty

occMapAppend :: Identifier -> Occurrence -> OccurrenceMap -> OccurrenceMap
occMapAppend k occ (OccurrenceMap m) = OccurrenceMap (Map.insertWith (++) k [occ] m)

occMapMap :: ([Occurrence] -> [Occurrence]) -> OccurrenceMap -> OccurrenceMap
occMapMap f (OccurrenceMap m) = OccurrenceMap (Map.map f m)

lookupOccurrences :: Identifier -> OccurrenceMap -> [Occurrence]
lookupOccurrences k (OccurrenceMap m) = Map.findWithDefault [] k m

newtype VarMap = VarMap (Map.Map Text Expr)

varMapFromList :: [(Text, Expr)] -> VarMap
varMapFromList = VarMap . Map.fromList

lookupVar :: Text -> VarMap -> Maybe Expr
lookupVar k (VarMap m) = Map.lookup k m

insertVar :: Text -> Expr -> VarMap -> VarMap
insertVar k v (VarMap m) = VarMap (Map.insert k v m)

notMemberVar :: Text -> VarMap -> Bool
notMemberVar k (VarMap m) = Map.notMember k m
