-- | Type-check error variants. Lives in its own module so that both
-- "YCHR.TypeCheck" and "YCHR.Compile.Pipeline" can refer to the type
-- without forming an import cycle ("YCHR.TypeCheck" already depends on
-- "YCHR.Compile.Pipeline" for 'CompiledProgram').
module YCHR.TypeCheck.Error
  ( TypeCheckError (..),
  )
where

import Data.Text (Text)

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
  deriving (Show, Eq)
