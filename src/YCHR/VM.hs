-- | CHR Virtual Machine
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

module YCHR.VM
  ( -- * Program structure
    Program (..)
  , Procedure (..)

    -- * Statements
  , Stmt (..)

    -- * Expressions
  , Expr (..)

    -- * Supporting types
  , Field (..)
  , Literal (..)
  , ArgIndex (..)
  , Name (..)
  , Label (..)
  , RuleName (..)
  ) where

import Data.String (IsString (..))


-- | A VM program is a collection of named procedures.
data Program = Program [Procedure]
  deriving (Show, Eq)


-- | A named procedure with parameters and a body.
-- 
-- The compiler generates procedures for:
--   * @tell_c@: adding a constraint from host language or rule bodies
--   * @activate_c@: trying all occurrences for a constraint
--   * @occurrence_c_j@: checking one occurrence of a constraint
--   * @reactivate_dispatch@: dispatching reactivation by constraint type
--   * @reactivate_all@: reactivating all constraints in the store
data Procedure = Procedure
  { procName   :: Name      -- ^ Procedure name
  , procParams :: [Name]    -- ^ Parameter names
  , procBody   :: [Stmt]    -- ^ Body statements
  }
  deriving (Show, Eq)


-- | Statements (imperative, side-effecting).
data Stmt

  -- General control flow

  = Let Name Expr
    -- ^ Bind a local variable to the result of an expression.

  | Assign Name Expr
    -- ^ Mutate an existing variable.

  | If Expr [Stmt] [Stmt]
    -- ^ Conditional: condition, then-branch, else-branch.

  | Foreach Label Name Name [(ArgIndex, Expr)] [Stmt]
    -- ^ Labeled loop over constraint store.
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

  | Continue Label
    -- ^ Jump to the next iteration of the labeled 'Foreach' loop.

  | Break Label
    -- ^ Exit the labeled 'Foreach' loop.

  | Return Expr
    -- ^ Return a value from the current procedure.

  | ExprStmt Expr
    -- ^ Evaluate an expression for its side effects, discard the result.

  -- Constraint store operations

  | Store Expr
    -- ^ Add a constraint suspension to the constraint store.
    -- The argument should be a constraint identifier (as returned
    -- by 'CreateConstraint'). This also registers the constraint
    -- as an observer of its arguments for reactivation purposes.

  | Kill Expr
    -- ^ Remove a constraint from the constraint store and mark it
    -- as no longer alive. The argument is a constraint identifier.

  -- Propagation history

  | AddHistory RuleName [Expr]
    -- ^ Record that a rule has fired with the given combination
    -- of constraint identifiers, to prevent redundant re-firing
    -- of propagation rules.

  -- Reactivation

  | DrainReactivationQueue Name [Stmt]
    -- ^ Process all constraints pending reactivation.
    --
    -- @DrainReactivationQueue suspVar body@
    --
    -- Iterates over the reactivation queue (populated as a side
    -- effect of 'Unify'), binding each pending constraint suspension
    -- to @suspVar@ and executing @body@. The body typically dispatches
    -- to the appropriate @activate_c@ procedure based on constraint type.

  deriving (Show, Eq)


-- | Expressions (side-effect-free, except for 'Unify' and 'HostCall').
data Expr

  -- General

  = Var Name
    -- ^ Reference to a variable (local or parameter).

  | Lit Literal
    -- ^ A literal value.

  | CallExpr Name [Expr]
    -- ^ Call a compiler-generated procedure and return its result.

  | HostCall Name [Expr]
    -- ^ Call a host language function. Used for arithmetic operators,
    -- comparisons, and user-written expressions in guards and bodies.

  -- Boolean operations

  | Not Expr
    -- ^ Logical negation.

  | And Expr Expr
    -- ^ Logical conjunction (short-circuiting).

  | Or Expr Expr
    -- ^ Logical disjunction (short-circuiting).

  -- Logical variables

  | NewVar
    -- ^ Create a fresh unbound logical variable.

  -- Term operations

  | MakeTerm Name [Expr]
    -- ^ Construct a compound term: @MakeTerm functor args@.

  | MatchTerm Expr Name Int
    -- ^ Check whether a value is a compound term with the given
    -- functor and arity: @MatchTerm expr functor arity@.
    -- Returns a boolean.

  | GetArg Expr Int
    -- ^ Extract an argument from a compound term by index (0-based).

  -- Constraint operations

  | CreateConstraint Name [Expr]
    -- ^ Create a new constraint suspension with the given type and
    -- arguments. Returns a constraint identifier. The constraint
    -- is not yet stored; use 'Store' to add it to the constraint store.

  | Alive Expr
    -- ^ Check whether a constraint (identified by its constraint
    -- identifier) is still alive in the constraint store.

  | IdEqual Expr Expr
    -- ^ Compare two constraint identifiers for equality.

  | IsConstraintType Expr Name
    -- ^ Check whether a constraint suspension has the given type.
    -- Used for dispatching in the reactivation procedure.

  -- Propagation history

  | NotInHistory RuleName [Expr]
    -- ^ Check that a rule has not previously fired with the given
    -- combination of constraint identifiers. Returns a boolean.

  -- Unification and equality

  | Unify Expr Expr
    -- ^ Unify two terms (tell semantics). Returns a boolean indicating
    -- success. May mutate logical variables as a side effect. On
    -- success, also pushes affected constraints onto the reactivation
    -- queue (see 'DrainReactivationQueue').

  | Equal Expr Expr
    -- ^ Check equality of two terms (ask semantics). Returns a boolean.
    -- No mutation. Uses Prolog @==@ semantics: two distinct unbound
    -- variables are not equal.

  -- Suspension field access

  | FieldGet Expr Field
    -- ^ Access a field of a constraint suspension.

  deriving (Show, Eq)


-- | Fields of a constraint suspension.
data Field
  = FieldId
    -- ^ The unique constraint identifier.
  | FieldArg ArgIndex
    -- ^ A constraint argument by index.
  | FieldType
    -- ^ The constraint type (for dispatch in reactivation).
  deriving (Show, Eq)


-- | Literal values.
data Literal
  = IntLit Int
    -- ^ Integer literal.
  | AtomLit String
    -- ^ Atom literal (symbolic constant).
  | BoolLit Bool
    -- ^ Boolean literal.
  deriving (Show, Eq)


-- | Zero-based index into a constraint's argument list.
newtype ArgIndex = ArgIndex Int
  deriving (Show, Eq)


-- | Variable or procedure name.
newtype Name = Name { unName :: String }
  deriving (Show, Eq, Ord)

instance IsString Name where fromString = Name

-- | Label for 'Foreach' loops, used with 'Continue' and 'Break'.
newtype Label = Label { unLabel :: String }
  deriving (Show, Eq, Ord)

instance IsString Label where fromString = Label

-- | Rule identifier, used for propagation history.
newtype RuleName = RuleName { unRuleName :: String }
  deriving (Show, Eq, Ord)

instance IsString RuleName where fromString = RuleName
