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

import Data.Map.Strict qualified as Map
import Data.Text (Text)
import YCHR.Desugared qualified as D
import YCHR.PExpr (PExpr)
import YCHR.Parsed qualified as P
import YCHR.Types (Constraint, Identifier, Name, Term)
import YCHR.Types qualified as Types
import YCHR.VM (ConstraintType, Expr, RuleName)

-- | Errors raised by any pass in the CHR-to-VM compiler. Both
-- constructors carry the source location and the pretty-printed origin
-- of the offending fragment so that the diagnostic can quote the user's
-- own input.
data CompileError
  = -- | A head constraint references a constraint type that is not in
    -- the symbol table. Raised by 'YCHR.Compile.Occurrences'.
    UnknownConstraintType P.SourceLoc PExpr Types.Name
  | -- | A guard or body term references a variable that is not bound
    -- by the rule head. Raised by 'YCHR.Compile' while compiling
    -- terms.
    UnboundVariable P.SourceLoc PExpr Text
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
    -- | Resolved name of the rule for propagation-history bookkeeping.
    -- Equals @rule.name@ if the rule was explicitly named, otherwise a
    -- synthetic @rule_N@ name unique within the program (assigned by
    -- 'YCHR.Compile.collectOccurrences' from the rule's source position).
    ruleName :: RuleName,
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
    constraint :: Constraint,
    -- | Whether the partner is kept (@True@) or removed (@False@) when
    -- the rule fires. Removed partners are killed before the body runs
    -- and skipped during backjumping (they are guaranteed dead).
    isKept :: Bool,
    -- | Constraint-type index used by 'YCHR.VM.Foreach' to look the
    -- partner up in the constraint store.
    cType :: ConstraintType
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
