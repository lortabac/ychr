-- | Type-check error and warning variants. Lives in its own module so
-- that both "YCHR.Internal.TypeCheck" and "YCHR.Internal.Compile.Pipeline" can
-- refer to the types without forming an import cycle
-- ("YCHR.Internal.TypeCheck" already depends on
-- "YCHR.Internal.Compile.Pipeline" for 'CompiledProgram').
module YCHR.Internal.TypeCheck.Error
  ( TypeCheckError (..),
    TypeCheckWarning (..),
    TypeCheckResult (..),
  )
where

import Data.Text (Text)
import YCHR.Internal.Diagnostic (Diagnostic)

-- | Errors reported by the type-checker pass.
data TypeCheckError
  = InconsistentTypes Text Text
  | NoMatchingOverload Text
  | UnboundTypeVar Text Text Text
  | UndefinedType Text Text Text
  | -- | A constructor name is declared by more than one type.
    -- Carries the flattened constructor name and the
    -- @(typeName, arity)@ pairs of every declaration.
    DuplicateConstructor Text [(Text, Int)]
  | -- | A known data constructor used with the wrong number of
    -- arguments. Carries the flattened constructor name, the
    -- use-site arity, and the declared arity. Constructors are
    -- name-only in YCHR's type system, so the declared arity is
    -- part of a constructor's identity and any mismatch is an
    -- error rather than a fall-through to @any@.
    ConstructorArityMismatch Text Int Int
  | -- | A use site of a bounded function or constraint infers a
    -- substitution whose required signatures cannot be satisfied by
    -- any declared signature of the bound's named function. Carries
    -- the bound function's flattened name. Emitted at the call site
    -- (or head/body occurrence for a bounded constraint).
    BoundUnsatisfied Text
  | -- | A constructor field references a type constructor applied to
    -- a different number of arguments than its declaration has
    -- parameters (base types have zero). Carries the enclosing type
    -- name, the constructor name, the referenced type name, the
    -- use-site arity, and the declared arity.
    TypeRefArityMismatch Text Text Text Int Int
  deriving (Show, Eq)

-- | Non-fatal diagnostics reported by the type-checker pass. A
-- warning never suppresses an error; the converse does hold — a unit
-- (rule, function equation, or top-level goal) that reports an error
-- omits its warnings, so a warning always describes a unit that is
-- otherwise well-typed (see
-- @docs\/reference\/type-system.md@ §Inaccessible branches).
data TypeCheckWarning
  = -- | The unit can never fire in the typed fragment: an evidence
    -- form (a refinement-predicate guard, a @GuardMatch@, or an
    -- ask-equality between head positions) contributes a typing fact
    -- that contradicts an already-known concrete type. Carries the two
    -- contradicting types, rendered. That is dead code rather than a
    -- type error, because a gradually-typed program can still reach
    -- the unit by flowing @any@-typed values into it.
    InaccessibleBranch Text Text
  deriving (Show, Eq)

-- | What a type-check pass produces: the errors that must abort
-- compilation, and the warnings that need not.
data TypeCheckResult = TypeCheckResult
  { errors :: [Diagnostic TypeCheckError],
    warnings :: [Diagnostic TypeCheckWarning]
  }
  deriving (Show, Eq)
