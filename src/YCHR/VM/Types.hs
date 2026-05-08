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
--
--   6. Expressions are split by the kind of value they produce:
--      'ValExpr' produces an ordinary 'Value' (the unification domain),
--      while 'IdExpr' produces a constraint identifier. Constraint
--      identifiers cannot flow into unification or term construction;
--      the type system enforces this.
module YCHR.VM.Types
  ( -- * Program structure
    Program (..),
    Procedure (..),

    -- * Statements
    Stmt (..),

    -- * Expressions
    ValExpr (..),
    IdExpr (..),
    CallArg (..),

    -- * Runtime call stack frames
    StackFrame (..),

    -- * Supporting types
    ConstraintType (..),
    RuleId (..),
    Literal (..),
    ArgIndex (..),
    Name (..),
    Label (..),
  )
where

import Data.String (IsString (..))
import Data.Text (Text)
import Data.Text qualified as T
import Language.Haskell.TH.Syntax (Lift)
import YCHR.Loc (SourceLoc)
import YCHR.Types (ConstraintType (..), RuleId (..))
import YCHR.Types qualified as Types

-- | A runtime call stack frame.
--
-- Emitted by the compiler at rule fire and function entry points.
-- The interpreter maintains a stack of these for error reporting.
data StackFrame = StackFrame
  { -- | Human-readable label (e.g. @"rule transitivity"@ or @"function factorial\/1"@).
    frameLabel :: Text,
    -- | Source file location.
    frameSourceLoc :: SourceLoc,
    -- | Pretty-printed source code (from the parsed expression).
    frameSourceCode :: Text
  }
  deriving (Show, Eq, Lift)

-- | A VM program is a collection of named procedures.
data Program = Program
  { -- | Number of distinct constraint types (for pre-allocating the store).
    numTypes :: !Int,
    -- | Source names of constraint types, indexed by the 'ConstraintType'
    -- integer. @typeNames !! i@ is the structured source name of the
    -- type with index @i@. Used by runtime introspection (e.g.
    -- @print_store@) and preserved across VM serialization.
    typeNames :: ![Types.Name],
    -- | Number of rules in the program.
    numRules :: !Int,
    -- | Display names of rules, indexed by the 'RuleId' integer.
    -- @ruleNames !! i@ is the source name (or synthetic @__rule_N@
    -- fallback for anonymous rules) of the rule with id @i@. Used
    -- by runtime introspection and preserved across VM serialization.
    ruleNames :: ![Text],
    -- | The procedures that make up the program.
    procedures :: [Procedure]
  }
  deriving (Show, Eq, Lift)

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
  deriving (Show, Eq, Lift)

-- | Statements (imperative, side-effecting).
data Stmt
  = -- General control flow

    -- | Bind a local variable to the result of a value expression.
    LetVal Name ValExpr
  | -- | Bind a local variable to the result of an id expression.
    LetId Name IdExpr
  | -- | Mutate an existing value-bound variable.
    AssignVal Name ValExpr
  | -- | Mutate an existing id-bound variable.
    AssignId Name IdExpr
  | -- | Conditional: condition, then-branch, else-branch.
    If ValExpr [Stmt] [Stmt]
  | -- | Labeled loop over constraint store.
    --
    -- @Foreach label constraintType suspVar indexConditions body@
    --
    -- Iterates over all stored constraints of the given type that
    -- satisfy the index conditions. Each condition @(i, expr)@ requires
    -- that argument @i@ of the constraint is 'Equal' to @expr@.
    --
    -- The current constraint suspension is bound to @suspVar@ in each
    -- iteration; references it via 'IdVar' inside the body, and use
    -- 'FieldArg'/'FieldType' to access its fields.
    --
    -- The iterator must satisfy the robustness, correctness,
    -- completeness, and weak termination properties as specified
    -- in the CHR compilation literature.
    Foreach Label ConstraintType Name [(ArgIndex, ValExpr)] [Stmt]
  | -- | Jump to the next iteration of the labeled 'Foreach' loop.
    Continue Label
  | -- | Exit the labeled 'Foreach' loop.
    Break Label
  | -- | Return a value from the current procedure.
    Return ValExpr
  | -- | Evaluate a value expression for its side effects, discard the result.
    ExprStmt ValExpr
  | -- Constraint store operations

    -- | Add a constraint suspension to the constraint store.
    -- The argument is a constraint identifier (as returned
    -- by 'CreateConstraint'). This also registers the constraint
    -- as an observer of its arguments for reactivation purposes.
    Store IdExpr
  | -- | Remove a constraint from the constraint store and mark it
    -- as no longer alive.
    Kill IdExpr
  | -- Propagation history

    -- | Record that a rule has fired with the given combination
    -- of constraint identifiers, to prevent redundant re-firing
    -- of propagation rules.
    AddHistory RuleId [IdExpr]
  | -- Reactivation

    -- | Process all constraints pending reactivation.
    --
    -- @DrainReactivationQueue suspVar body@
    --
    -- Iterates over the reactivation queue (populated as a side
    -- effect of 'Unify'), binding each pending constraint suspension
    -- to @suspVar@ (referenced via 'IdVar') and executing @body@.
    -- The body typically dispatches to the appropriate @activate_c@
    -- procedure based on constraint type.
    DrainReactivationQueue Name [Stmt]
  | -- Call stack frames

    -- | Push a frame onto the runtime call stack.
    -- Emitted by the compiler at rule fire and function entry points.
    -- The interpreter automatically pops frames when a procedure
    -- returns (save\/restore around 'callProc').
    PushFrame StackFrame
  deriving (Show, Eq, Lift)

-- | Value-producing expressions: everything that evaluates to an
-- ordinary 'Value' from the unification domain.
data ValExpr
  = -- | Reference to a value-bound variable (local or parameter).
    Var Name
  | -- | A literal value.
    Lit Literal
  | -- | Call a compiler-generated procedure and return its result.
    CallExpr Name [CallArg]
  | -- | Call a host language function. Used for arithmetic operators,
    -- comparisons, and user-written expressions in guards and bodies.
    -- Host functions return values; they cannot return constraint
    -- identifiers.
    HostCall Name [ValExpr]
  | -- | Switch evaluation into deep deref-aware mode for the nested
    -- expression: 'Var' references are dereferenced (following binding
    -- chains) before use, and this mode propagates recursively into
    -- sub-expressions ('CallExpr', 'MakeTerm', etc.). Used for guard
    -- expressions and the right-hand side of @is@.
    EvalDeep ValExpr
  | -- Boolean operations

    -- | Logical negation.
    Not ValExpr
  | -- | Logical conjunction (short-circuiting).
    And ValExpr ValExpr
  | -- | Logical disjunction (short-circuiting).
    Or ValExpr ValExpr
  | -- Logical variables

    -- | Create a fresh unbound logical variable.
    NewVar
  | -- Term operations

    -- | Construct a compound term: @MakeTerm functor args@.
    MakeTerm Name [ValExpr]
  | -- | Check whether a value is a compound term with the given
    -- functor and arity: @MatchTerm expr functor arity@.
    -- Returns a boolean.
    MatchTerm ValExpr Name Int
  | -- | Extract an argument from a compound term by index (0-based).
    GetArg ValExpr Int
  | -- Constraint observation

    -- | Check whether a constraint (identified by its constraint
    -- identifier) is still alive in the constraint store.
    Alive IdExpr
  | -- | Compare two constraint identifiers for equality.
    IdEqual IdExpr IdExpr
  | -- | Check whether a constraint suspension has the given type.
    -- Used for dispatching in the reactivation procedure.
    IsConstraintType IdExpr ConstraintType
  | -- Propagation history

    -- | Check that a rule has not previously fired with the given
    -- combination of constraint identifiers. Returns a boolean.
    NotInHistory RuleId [IdExpr]
  | -- Unification and equality

    -- | Unify two terms (tell semantics). Returns a boolean indicating
    -- success. May mutate logical variables as a side effect. On
    -- success, also pushes affected constraints onto the reactivation
    -- queue (see 'DrainReactivationQueue').
    Unify ValExpr ValExpr
  | -- | Check equality of two terms (ask semantics). Returns a boolean.
    -- No mutation. Uses Prolog @==@ semantics: two distinct unbound
    -- variables are not equal.
    Equal ValExpr ValExpr
  | -- Suspension field access

    -- | Extract a constraint argument from a suspension by index.
    FieldArg IdExpr ArgIndex
  | -- | Extract the constraint type tag from a suspension.
    FieldType IdExpr
  deriving (Show, Eq, Lift)

-- | Constraint-identifier-producing expressions.
--
-- Constraint identifiers are produced in only three ways: by
-- 'CreateConstraint', by referencing an id-bound variable
-- ('IdVar' — populated by the parameter list, 'Foreach',
-- 'DrainReactivationQueue', or a 'LetId' binding), or by
-- a procedure that returns one (currently no such procedure
-- is generated, but the constructor is reserved).
data IdExpr
  = -- | Reference to an id-bound variable (local or parameter).
    IdVar Name
  | -- | Create a new constraint suspension with the given type and
    -- arguments. Returns a constraint identifier. The constraint
    -- is not yet stored; use 'Store' to add it to the constraint store.
    CreateConstraint ConstraintType [ValExpr]
  deriving (Show, Eq, Lift)

-- | Procedure-call argument. Procedures may take a heterogeneous
-- mix of value and id parameters; this wrapper makes the kind
-- explicit at every call site.
data CallArg
  = AVal ValExpr
  | AId IdExpr
  deriving (Show, Eq, Lift)

-- | Literal values.
data Literal
  = -- | Integer literal.
    IntLit Int
  | -- | Floating-point literal.
    FloatLit Double
  | -- | Atom literal (symbolic constant).
    AtomLit Text
  | -- | Text (string) literal.
    TextLit Text
  | -- | Boolean literal.
    BoolLit Bool
  | -- | Wildcard literal: evaluates to 'VWildcard'.
    WildcardLit
  deriving (Show, Eq, Lift)

-- | Zero-based index into a constraint's argument list.
newtype ArgIndex = ArgIndex Int
  deriving (Show, Eq, Lift)

-- | Variable or procedure name.
newtype Name = Name {unName :: Text}
  deriving (Show, Eq, Ord, Lift)

instance IsString Name where fromString = Name . T.pack

-- | Label for 'Foreach' loops, used with 'Continue' and 'Break'.
newtype Label = Label {unLabel :: Text}
  deriving (Show, Eq, Ord, Lift)

instance IsString Label where fromString = Label . T.pack
