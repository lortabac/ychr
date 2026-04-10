-- | CHR Virtual Machine — type definitions.
--
-- This module defines the abstract VM that serves as the intermediate
-- representation for the CHR compiler. The VM is a small imperative
-- language with domain-specific instructions for CHR constraint store
-- operations, logical variables, term manipulation, and propagation
-- history management.
--
-- Architecture:
--
--   CHR source (Prolog-compatible syntax)
--     → CHR compiler (Haskell)
--       → VM program (this representation)
--         → Backend: JavaScript code + JS runtime
--         → Backend: Scheme code + Scheme runtime
--         → Backend: Haskell interpreter + Haskell runtime
--
-- Design principles:
--
--   1. The VM instruction set is the complete interface between the
--      compiler and the runtime. The compiler never emits calls to
--      runtime functions by name.
--
--   2. CallExpr is used exclusively for calling compiler-generated
--      procedures (occurrence procedures, activate, tell, etc.).
--
--   3. HostCall is used for calling host language functions (arithmetic,
--      user-written guards and body expressions, etc.).
--
--   4. Logical variables and algebraic terms are opaque values from the
--      VM's perspective. The runtime provides NewVar, Unify, Equal,
--      MakeTerm, MatchTerm, and GetArg as primitives.
--
--   5. Recursion optimizations (trampolining, explicit stack) are the
--      responsibility of each backend, not the VM.
module YCHR.VM.Types
  ( -- * Program structure
    Program (..),
    Procedure (..),

    -- * Statements
    Stmt (..),

    -- * Expressions
    Expr (..),

    -- * Supporting types
    ConstraintType (..),
    Field (..),
    Literal (..),
    ArgIndex (..),
    Name (..),
    Label (..),
    RuleName (..),
  )
where

import Data.String (IsString (..))
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Types (ConstraintType (..))

-- | A VM program is a collection of named procedures.
data Program = Program
  { -- | Number of distinct constraint types (for pre-allocating the store).
    numTypes :: !Int,
    -- | Source names of constraint types, indexed by the 'ConstraintType'
    -- integer. @typeNames !! i@ is the flattened source name (e.g.
    -- @"Module:foo"@) of the type with index @i@. Used by runtime
    -- introspection (e.g. @print_store@) and preserved across VM
    -- serialization.
    typeNames :: ![Text],
    -- | The procedures that make up the program.
    procedures :: [Procedure]
  }
  deriving (Show, Eq)

-- | A named procedure with parameters and a body.
--
-- The compiler generates procedures for:
--   * @tell_c@: adding a constraint from host language or rule bodies
--   * @activate_c@: trying all occurrences for a constraint
--   * @occurrence_c_j@: checking one occurrence of a constraint
--   * @reactivate_dispatch@: dispatching reactivation by constraint type
--
-- Note: @reactivate_all@ (paper §5.1–5.2) is not generated.  YCHR
-- implements the /Selective Constraint Reactivation/ optimization
-- (paper §5.3, observer pattern): 'Store' registers constraints as
-- observers of their arguments, 'Unify' populates the reactivation
-- queue for affected constraints, and 'DrainReactivationQueue'
-- processes only those constraints.
data Procedure = Procedure
  { -- | Procedure name
    name :: Name,
    -- | Parameter names
    params :: [Name],
    -- | Body statements
    body :: [Stmt]
  }
  deriving (Show, Eq)

-- | Statements (imperative, side-effecting).
data Stmt
  = -- General control flow

    -- | Bind a local variable to the result of an expression.
    Let Name Expr
  | -- | Mutate an existing variable.
    Assign Name Expr
  | -- | Conditional: condition, then-branch, else-branch.
    If Expr [Stmt] [Stmt]
  | -- | Labeled loop over constraint store.
    --
    -- @Foreach label constraintType suspVar indexConditions body@
    --
    -- Iterates over all stored constraints of the given type that
    -- satisfy the index conditions. Each condition @(i, expr)@ requires
    -- that argument @i@ of the constraint is 'Equal' to @expr@.
    --
    -- The current constraint suspension is bound to @suspVar@ in each
    -- iteration. Use 'FieldGet' to access its fields.
    --
    -- The iterator must satisfy the robustness, correctness,
    -- completeness, and weak termination properties as specified
    -- in the CHR compilation literature.
    Foreach Label ConstraintType Name [(ArgIndex, Expr)] [Stmt]
  | -- | Jump to the next iteration of the labeled 'Foreach' loop.
    Continue Label
  | -- | Exit the labeled 'Foreach' loop.
    Break Label
  | -- | Return a value from the current procedure.
    Return Expr
  | -- | Evaluate an expression for its side effects, discard the result.
    ExprStmt Expr
  | -- Constraint store operations

    -- | Add a constraint suspension to the constraint store.
    -- The argument should be a constraint identifier (as returned
    -- by 'CreateConstraint'). This also registers the constraint
    -- as an observer of its arguments for reactivation purposes.
    Store Expr
  | -- | Remove a constraint from the constraint store and mark it
    -- as no longer alive. The argument is a constraint identifier.
    Kill Expr
  | -- Propagation history

    -- | Record that a rule has fired with the given combination
    -- of constraint identifiers, to prevent redundant re-firing
    -- of propagation rules.
    AddHistory RuleName [Expr]
  | -- Reactivation

    -- | Process all constraints pending reactivation.
    --
    -- @DrainReactivationQueue suspVar body@
    --
    -- Iterates over the reactivation queue (populated as a side
    -- effect of 'Unify'), binding each pending constraint suspension
    -- to @suspVar@ and executing @body@. The body typically dispatches
    -- to the appropriate @activate_c@ procedure based on constraint type.
    DrainReactivationQueue Name [Stmt]
  deriving (Show, Eq)

-- | Expressions (side-effect-free, except for 'Unify' and 'HostCall').
data Expr
  = -- General

    -- | Reference to a variable (local or parameter).
    Var Name
  | -- | A literal value.
    Lit Literal
  | -- | Call a compiler-generated procedure and return its result.
    CallExpr Name [Expr]
  | -- | Call a host language function. Used for arithmetic operators,
    -- comparisons, and user-written expressions in guards and bodies.
    HostCall Name [Expr]
  | -- | Switch evaluation into deep deref-aware mode for the nested
    -- expression: 'Var' references are dereferenced (following binding
    -- chains) before use, and this mode propagates recursively into
    -- sub-expressions ('CallExpr', 'MakeTerm', etc.). Used for guard
    -- expressions and the right-hand side of @is@.
    EvalDeep Expr
  | -- Boolean operations

    -- | Logical negation.
    Not Expr
  | -- | Logical conjunction (short-circuiting).
    And Expr Expr
  | -- | Logical disjunction (short-circuiting).
    Or Expr Expr
  | -- Logical variables

    -- | Create a fresh unbound logical variable.
    NewVar
  | -- Term operations

    -- | Construct a compound term: @MakeTerm functor args@.
    MakeTerm Name [Expr]
  | -- | Check whether a value is a compound term with the given
    -- functor and arity: @MatchTerm expr functor arity@.
    -- Returns a boolean.
    MatchTerm Expr Name Int
  | -- | Extract an argument from a compound term by index (0-based).
    GetArg Expr Int
  | -- Constraint operations

    -- | Create a new constraint suspension with the given type and
    -- arguments. Returns a constraint identifier. The constraint
    -- is not yet stored; use 'Store' to add it to the constraint store.
    CreateConstraint ConstraintType [Expr]
  | -- | Check whether a constraint (identified by its constraint
    -- identifier) is still alive in the constraint store.
    Alive Expr
  | -- | Compare two constraint identifiers for equality.
    IdEqual Expr Expr
  | -- | Check whether a constraint suspension has the given type.
    -- Used for dispatching in the reactivation procedure.
    IsConstraintType Expr ConstraintType
  | -- Propagation history

    -- | Check that a rule has not previously fired with the given
    -- combination of constraint identifiers. Returns a boolean.
    NotInHistory RuleName [Expr]
  | -- Unification and equality

    -- | Unify two terms (tell semantics). Returns a boolean indicating
    -- success. May mutate logical variables as a side effect. On
    -- success, also pushes affected constraints onto the reactivation
    -- queue (see 'DrainReactivationQueue').
    Unify Expr Expr
  | -- | Check equality of two terms (ask semantics). Returns a boolean.
    -- No mutation. Uses Prolog @==@ semantics: two distinct unbound
    -- variables are not equal.
    Equal Expr Expr
  | -- Suspension field access

    -- | Access a field of a constraint suspension.
    FieldGet Expr Field
  deriving (Show, Eq)

-- | Fields of a constraint suspension.
data Field
  = -- | The unique constraint identifier.
    FieldId
  | -- | A constraint argument by index.
    FieldArg ArgIndex
  | -- | The constraint type (for dispatch in reactivation).
    FieldType
  deriving (Show, Eq)

-- | Literal values.
data Literal
  = -- | Integer literal.
    IntLit Int
  | -- | Atom literal (symbolic constant).
    AtomLit Text
  | -- | Text (string) literal.
    TextLit Text
  | -- | Boolean literal.
    BoolLit Bool
  | -- | Wildcard literal: evaluates to 'VWildcard'.
    WildcardLit
  deriving (Show, Eq)

-- | Zero-based index into a constraint's argument list.
newtype ArgIndex = ArgIndex Int
  deriving (Show, Eq)

-- | Variable or procedure name.
newtype Name = Name {unName :: Text}
  deriving (Show, Eq, Ord)

instance IsString Name where fromString = Name . T.pack

-- | Label for 'Foreach' loops, used with 'Continue' and 'Break'.
newtype Label = Label {unLabel :: Text}
  deriving (Show, Eq, Ord)

instance IsString Label where fromString = Label . T.pack

-- | Rule identifier, used for propagation history.
newtype RuleName = RuleName {unRuleName :: Text}
  deriving (Show, Eq, Ord)

instance IsString RuleName where fromString = RuleName . T.pack
