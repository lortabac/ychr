-- | The embedder-facing core types: the 'Term' values that cross the
-- program boundary, the 'Name's inside them, the 'Constraint' shape of
-- a raw goal, and the type-declaration vocabulary used by "YCHR.DSL".
--
-- This is the supported, version-policy-covered subset of the
-- compiler's shared type module. The compiler-internal remainder
-- (symbol tables, qualified-name forms, post-HNF head shapes, …) lives
-- in "YCHR.Internal.Types" and is not covered by the package version
-- policy.
module YCHR.Types
  ( -- * Terms
    Term (..),

    -- * Names
    Name (..),
    flattenName,

    -- * Constraints
    Constraint (..),

    -- * Type declarations
    TypeDefinition,
    TypeKind (..),
    typeConstructors,
    DataConstructor,
    TypeExpr (..),
  )
where

import YCHR.Internal.Types
