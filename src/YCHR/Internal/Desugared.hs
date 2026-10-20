{-# LANGUAGE DuplicateRecordFields #-}

-- | CHR Abstract Syntax Tree
--
-- This module defines the internal AST for CHR programs. This is not
-- the direct output of the parser, but a desugared and semantically
-- precise representation that guides compilation to the VM.
--
-- Desugaring already performed at this stage:
--
--   * Simplification and propagation rules are represented uniformly
--     as simpagation rules. A simplification rule has an empty 'kept'
--     list; a propagation rule has an empty 'removed' list. The
--     compiler checks whether 'removed' is empty to decide whether
--     propagation history maintenance is needed.
--
--   * Guards and body goals are represented with distinct types
--     ('Guard' and 'BodyGoal') to enforce that only semantically
--     appropriate goals appear in each position.
--
--   * Constraint head names and function names are 'QualifiedName',
--     so the qualification invariant established by the renamer and
--     committed by the resolver is reflected in the type system.
module YCHR.Internal.Desugared
  ( -- * Program structure
    Program (..),
    Rule (..),
    Head (..),
    Function (..),
    Equation (..),

    -- * Goals
    Guard (..),
    BodyGoal (..),
    FunStmt (..),

    -- * Aggregates
    Aggregate (..),
    AggregateConjunct (..),
    AggregateResult (..),

    -- * Expressions
    Expr (..),

    -- * Re-exports from CHR.Types
    QualifiedConstraint (..),
    QualifiedName (..),
    HeadConstraint (..),
    HeadArg (..),
    Term (..),
    TypeExpr (..),
    TypeDefinition (..),
    BoundSig (..),
    AggregateKind (..),
  )
where

import Data.List.NonEmpty (NonEmpty)
import Data.Map.Strict (Map)
import Data.Text (Text)
import YCHR.Internal.Parsed (AnnP)
import YCHR.Internal.Resolved (Expr (..))
-- The desugared 'Aggregate' and 'AggregateConjunct' below replace the
-- surface ones in "YCHR.Internal.Types"; 'AggregateKind' is shared.
import YCHR.Internal.Types hiding (Aggregate (..), AggregateConjunct (..))

-- | A whole desugared program, ready for symbol-table extraction and
-- compilation.
data Program = Program
  { rules :: [Rule],
    functions :: [Function],
    constraintTypes :: Map ConstraintKey [TypeExpr],
    -- | Bounds declared on each @:- chr_constraint@ that carries a
    -- @requiring@ clause. See 'YCHR.Internal.Resolved.Program' for the
    -- bounded-vs-unbounded convention (constraints without bounds are
    -- absent from the map).
    constraintBounds :: Map ConstraintKey [BoundSig],
    -- | See 'YCHR.Internal.Resolved.Program'.
    constraintUses :: Map ConstraintKey ConstraintUse,
    -- | See 'YCHR.Internal.Resolved.Program'.
    nameVisibility :: Map Text (Map (Text, Int) [QualifiedName]),
    typeDefinitions :: [TypeDefinition]
  }
  deriving (Show)

-- | A desugared rule, with its head normalized and its guards and body
-- goals typed.
data Rule = Rule
  { name :: Maybe Text,
    head :: AnnP Head,
    guard :: AnnP [Guard],
    body :: AnnP [BodyGoal]
  }
  deriving (Show)

-- | A rule head split into the constraints kept after firing, the
-- constraints removed by it, and its aggregates.
--
-- An aggregate is neither kept nor removed: it reads the store, and the
-- constraints of its goal stay there (except for a @takemin@/@takemax@,
-- which removes the selected match). Keeping the three lists separate
-- means every walker that only cares about head occurrences still sees
-- exactly what it saw before aggregates existed.
data Head = Head
  { kept :: [HeadConstraint],
    removed :: [HeadConstraint],
    -- | The rule's aggregates, in source order. Empty for a program
    -- without aggregates.
    aggregates :: [Aggregate]
  }
  deriving (Show, Eq)

-- | A desugared aggregate: the same shape as
-- 'YCHR.Internal.Types.Aggregate', with the expressions the compiler
-- needs instead of their surface 'Term' spellings.
--
-- 'agg' is 'Nothing' for a selection form, which has no aggregator; for
-- a selection form 'element' is the selection key and 'result' is
-- unused.
data Aggregate = Aggregate
  { kind :: AggregateKind,
    agg :: Maybe Expr,
    element :: Expr,
    goal :: [AggregateConjunct],
    -- | The result pattern, kept as a 'Term' like a head argument: it
    -- is matched, not evaluated.
    result :: Term,
    -- | The names it reads from the enclosing scope, sorted: the ones it
    -- mentions that are bound before it runs.
    aggShared :: [Text],
    -- | The names that get a fresh slot in its own scope, sorted: the
    -- variables of its @element@, of its constraint conjuncts and their
    -- HNF guards, and of its @?@ guards, plus what its nested aggregates
    -- bind, less 'aggShared'. A selection's visible variables are
    -- 'aggBinds', not locals, so its locals are its goal's @$hnf_N@
    -- names. @agg@ is not included: it is evaluated in the enclosing
    -- scope. A nested aggregate's own locals are not included either.
    aggLocals :: [Text],
    -- | The names it binds in the enclosing scope: the new variables of
    -- a plain form's result pattern, in pattern order, or a selection's
    -- goal variables, sorted. The compiler's out-cells follow this
    -- order.
    aggBinds :: [Text],
    -- | The result pattern in head normal form. 'Nothing' for a
    -- selection form.
    --
    -- The four fields above are filled by
    -- "YCHR.Internal.Desugar.AggregateScope" at the end of desugaring a
    -- rule; until then they are empty.
    aggResult :: Maybe AggregateResult
  }
  deriving (Show, Eq)

-- | An aggregate's result pattern in head normal form, as HNF treats a
-- head argument: a variable the payload is bound to, plus the guards
-- that check it. A variable bound before the aggregate becomes a
-- 'GuardEqual', a compound a 'GuardMatch' with its 'GuardGetArg's. A
-- fresh source variable is its own 'resultVar', with no guard;
-- otherwise 'resultVar' is a fresh @$res_N@ name. Both are slots of the
-- enclosing scope.
data AggregateResult = AggregateResult
  { resultVar :: Text,
    resultGuards :: [Guard]
  }
  deriving (Show, Eq)

-- | A desugared aggregate-goal conjunct.
data AggregateConjunct
  = -- | A CHR constraint, a /goal occurrence/ of its type, in head normal
    -- form: its arguments are variables or wildcards, and the guards HNF
    -- emitted for it — one per compound or duplicated argument it had —
    -- are carried alongside. Those guards are evaluated in place, inside
    -- the loop that matches this conjunct, so they filter matches before
    -- the conjuncts after it are searched and never join the rule's
    -- guard.
    AggConstraint HeadConstraint [Guard]
  | -- | A nested aggregate.
    AggNested Aggregate
  | -- | A @? Guard@, checked in place left to right.
    AggGuard Guard
  deriving (Show, Eq)

-- | Guards over the typed 'Expr' AST. 'GuardMatch' and 'GuardGetArg'
-- always carry a 'VarExpr' as their operand: HNF only introduces
-- match/getarg guards for fresh variables it has just bound. The
-- operand type is left as 'Expr' rather than 'Text' so the lambda
-- lifter and pretty-printer can walk guards uniformly.
data Guard
  = GuardEqual Expr Expr
  | GuardMatch Expr Name Word
  | GuardGetArg Text Expr Word
  | GuardExpr Expr
  deriving (Show, Eq)

-- | Body goals over the typed 'Expr' AST.
--
-- 'BodyTell' is a tell of a user-declared constraint. Its arguments
-- are 'Expr' and are evaluated at runtime, like every other expression
-- position in the language (function args, constructor args, @is@ RHS,
-- @=@ operands). Head patterns and equation patterns still carry
-- 'Term' (see 'HeadConstraint' / 'Equation'); the call-vs-constructor
-- question is decided structurally for tells but does not arise for
-- patterns.
--
-- 'BodyCall' is a static user-function call; 'BodyApply' is dynamic
-- dispatch ('$call').
--
-- 'BodyOr' is the surface @;@ operator: a choice between two or more
-- body conjunctions, flattened out of the right-nested @;@ the parser
-- produces. It survives only as far as
-- \"YCHR.Internal.Desugar.Disjunction\", which lifts each branch into
-- its own constraint and rewrites the node into a @search:alt@ tell;
-- the type checker sees the pre-lowering form, where each branch is
-- still in the enclosing rule's scope. The 'NonEmpty' is the parser's
-- guarantee made structural: a @;@ has at least two branches, and a
-- node with none would silently mean \"fail\".
data BodyGoal
  = BodyTrue
  | BodyTell QualifiedName [Expr]
  | BodyUnify Expr Expr
  | BodyHostStmt Text [Expr]
  | BodyIs Text Expr
  | BodyCall QualifiedName [Expr]
  | BodyApply Expr [Expr]
  | -- | A dynamic @tell(G, A1, …, Ak)@: evaluate @G@ to a constraint
    -- term, append @A1..Ak@ to its arguments, and tell the result. The
    -- 'Text' is the calling module — the scope the term's functor is
    -- resolved in at run time — or @\<query\>@ for a query goal. A
    -- @tell@ whose goal is written literally never gets here: the
    -- renamer turns it into the plain tell it denotes.
    BodyTellDynamic Text Expr [Expr]
  | BodyOr (NonEmpty [BodyGoal])
  deriving (Show, Eq)

-- | A function declaration with its equations grouped under it. Also
-- describes lambdas lifted out of rule bodies.
data Function = Function
  { name :: QualifiedName,
    arity :: Int,
    signatures :: [([TypeExpr], TypeExpr)],
    -- | Bounds declared on this function via @requiring@. Empty when
    -- the function is unbounded.
    requiring :: [BoundSig],
    -- | The refinement type declared via @refining@, trusted as an
    -- axiom by the type checker. 'Nothing' for an ordinary function.
    refining :: Maybe TypeExpr,
    -- | For a lambda lifted by the desugarer (@__lambda_N@), the
    -- number of parameters the source lambda declared. The lifted
    -- function's 'arity' counts those parameters /plus/ the captured
    -- free variables the lifter prepends, and the closure term it
    -- builds has the captures as its only payload. A closure can
    -- therefore only be invoked with exactly this many arguments;
    -- 'YCHR.Internal.Compile.genLambdaBranch' uses that to skip
    -- dispatch branches no call can reach. 'Nothing' for an ordinary
    -- function.
    lambdaArity :: Maybe Int,
    -- | Whether this function is a candidate for inlining at eligible
    -- call sites, carried over from 'YCHR.Internal.Resolved.FunctionDef.inline'.
    -- Always 'False' for a lifted lambda. See 'YCHR.Internal.Desugar.Inline',
    -- which does the remaining eligibility checks and the substitution.
    inline :: Bool,
    -- | The function's equations, each carrying the source location and
    -- original p-expr of the declaration that wrote it. Keeping the
    -- annotation per equation lets a diagnostic about an equation from
    -- another module's @:- extend_function@ point at that equation
    -- rather than at the owning declaration's first equation.
    equations :: [AnnP Equation]
  }
  deriving (Show)

-- | One equation of a 'Function': pattern parameters, guards, a prelude
-- of statements, and a return expression.
data Equation = Equation
  { params :: [HeadArg],
    guards :: [Guard],
    -- | Statements executed before evaluating 'rhs'. Empty for
    -- single-expression bodies. The desugarer is responsible for
    -- restricting which 'R.Expr' shapes are accepted in non-final
    -- position; see 'FunStmt'.
    prelude :: [FunStmt],
    rhs :: Expr
  }
  deriving (Show)

-- | A statement appearing in non-final position of a function equation's
-- right-hand side. Strictly a subset of 'BodyGoal' — rule-body-only forms
-- like 'BodyTell', 'BodyUnify', and 'BodyTrue' are intentionally not
-- representable.
data FunStmt
  = -- | @X is E@. The LHS must be a variable; the desugarer rejects
    -- non-variable LHS in this position.
    FunIs Text Expr
  | -- | @host:f(args)@ evaluated for side effects.
    FunHostStmt Text [Expr]
  | -- | Statically resolved user-function call; result discarded.
    FunCall QualifiedName [Expr]
  | -- | Dynamic dispatch (@'$call'(F, args)@); result discarded.
    FunApply Expr [Expr]
  deriving (Show, Eq)
