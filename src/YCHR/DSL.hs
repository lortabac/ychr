{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Build CHR programs in Haskell instead of @.chr@ source: assemble
-- 'Module' values, then compile and run them with 'runDSL'. Reference and
-- examples:
-- <https://github.com/lortabac/ychr/blob/master/docs/reference/dsl.md>.
--
-- Every combinator is a pure function producing the
-- 'YCHR.Internal.Parsed.Module' AST the parser would produce from text.
-- Nothing is validated here: undeclared constraints, ill-typed bodies,
-- etc. are caught downstream by 'compileParsedModules', as for parsed input.
--
-- = Two things to know before you start
--
-- __Constraint positions are partial.__ '<=>', '==>', @\\\\@ and 'runDSL'
-- expect each rule-head and goal 'Term' to be a compound or an atom — the
-- shapes 'term', 'qterm' and 'atom' build. A bare 'var' or 'int' there
-- throws an 'error': a pure combinator has no failure channel. (The same
-- mistake through "YCHR.Convert" is a @MalformedGoal@
-- 'YCHR.Convert.ConvertError'.) Malformed /programs/ are still reported by
-- the pipeline; only malformed /Haskell/ fails this way.
--
-- __This module defines an orphan @instance Num Term@__ so numeric
-- literals and @+@ \/ @-@ \/ @*@ work in term position. Anywhere both this
-- module and 'Term' are in scope, @1 + 2 :: Term@ builds the /symbolic/
-- compound @+(1, 2)@; it does not evaluate to @3@.
--
-- Negative literals work (@-1 :: Term@ is @'IntTerm' (-1)@: GHC routes
-- them through 'negate', which folds them into the literal). 'negate' on a
-- /non-literal/, 'abs', and 'signum' build @-(x)@, @abs(x)@, @sign(x)@,
-- which the prelude does not declare — they work only if your module
-- declares @-\/1@, @abs\/1@, @sign\/1@. Prefer '.-' and friends. There is
-- no 'Fractional' instance; use 'float' for fractional literals.
module YCHR.DSL
  ( -- * Modules
    Module,
    module',
    importing,
    library,
    declaring,
    defining,
    withEquations,
    withExtensions,
    withClassExtensions,
    chrType,
    exporting,

    -- * Declarations
    Declaration,
    (//),
    function,
    openFunction,
    class_,
    openClass,
    extendClassType,
    typeExport,
    typeExportWith,
    op,
    OpType (..),

    -- * Type definitions
    TypeDefinition,
    TypeKind (..),
    DataConstructor,
    TypeExpr (..),
    tyDef,
    tyOpaque,
    dataCtor,

    -- * Rules
    Rule,
    Simpa,
    IsRuleHead,
    (@:),
    (<=>),
    (==>),
    (\\),
    (|-),

    -- * Terms
    Term,
    term,
    qterm,
    quote,
    var,
    atom,
    int,
    float,
    bool,
    text,
    wildcard,

    -- * Goal sugar
    (.=.),
    is,
    hostCall,

    -- * Function equations and lambdas
    FunctionEquation,
    equation,
    equationSeq,
    lambda,
    funRef,
    call_,

    -- * Numeric and comparison sugar

    --
    -- $numericSugar
    (.+),
    (.-),
    (.*),
    (./),
    (.<),
    (.<=),
    (.>),
    (.>=),
    (.==),

    -- * Compiling and running
    runDSL,
    runDSLWithHostCallRegistry,
    HostCallRegistry,
  )
where

import Control.Exception (throwIO)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Text (Text)
import YCHR.Convert (quote)
import YCHR.Internal.Parsed
import YCHR.Internal.Runtime.Registry (HostCallRegistry)
import YCHR.Internal.Runtime.Search (defaultHostCallRegistry)
import YCHR.Run
  ( CompiledProgram,
    Warning,
    compileParsedModules,
    runProgramWithGoalDSL,
  )

-- ---------------------------------------------------------------------------
-- Modules
-- ---------------------------------------------------------------------------

-- | An empty module with the given name.
module' :: Text -> Module
module' name =
  Module
    { name = name,
      nameLoc = dummyLoc,
      imports = [],
      decls = [],
      extensionTypes = [],
      typeDecls = [],
      rules = [],
      equations = [],
      extensions = [],
      classExtensions = [],
      exports = Nothing
    }

-- | Append plain @use_module(M)@ imports.
--
-- > module' "Logic" `importing` ["Order", "Util"]
importing :: Module -> [Text] -> Module
importing m imps =
  m {imports = m.imports ++ map (noAnnP . (`ModuleImport` Nothing)) imps}

-- | Append one @use_module(library(L))@ import (a stdlib or bundled
-- library, as opposed to a user-written sibling module).
library :: Module -> Text -> Module
library m libName =
  m {imports = m.imports ++ [noAnnP (LibraryImport libName Nothing)]}

-- | Append constraint, function, operator, or type-export declarations.
declaring :: Module -> [Declaration] -> Module
declaring m ds = m {decls = m.decls ++ map noAnn ds}

-- | Append rules to a module.
defining :: Module -> [Rule] -> Module
defining m rls = m {rules = m.rules ++ rls}

-- | Append function-definition equations.
withEquations :: Module -> [FunctionEquation] -> Module
withEquations m eqs = m {equations = m.equations ++ map noAnnP eqs}

-- | Append @:- extend_function name(args) -> body@ equations: they extend
-- an open function declared in another module, resolved through this
-- module's imports.
withExtensions :: Module -> [FunctionEquation] -> Module
withExtensions m eqs = m {extensions = m.extensions ++ map noAnnP eqs}

-- | Append @:- extend_class name(args) -> body@ equations; the open-class
-- counterpart of 'withExtensions'.
withClassExtensions :: Module -> [FunctionEquation] -> Module
withClassExtensions m eqs =
  m {classExtensions = m.classExtensions ++ map noAnnP eqs}

-- | Append a CHR-type definition (@:- chr_type ...@).
chrType :: Module -> TypeDefinition -> Module
chrType m ty = m {typeDecls = m.typeDecls ++ [noAnn ty]}

-- | Set the export list; further calls append. Without one (the default
-- after 'module'') the module exports everything.
exporting :: Module -> [Declaration] -> Module
exporting m ds = case m.exports of
  Nothing -> m {exports = Just (noAnnP ds)}
  Just (AnnP existing loc origin) ->
    m {exports = Just (AnnP (existing ++ ds) loc origin)}

-- ---------------------------------------------------------------------------
-- Declarations
-- ---------------------------------------------------------------------------

-- | Constraint declaration: @:- chr_constraint name/arity@.
(//) :: Text -> Int -> Declaration
(//) name arity = ConstraintDecl name arity Nothing Nothing

-- | Function declaration: @:- function name/arity@.
function :: Text -> Int -> Declaration
function name arity =
  FunctionDecl
    { name = name,
      arity = arity,
      argTypes = Nothing,
      returnType = Nothing,
      isOpen = False,
      kind = DKFunction,
      requiring = Nothing
    }

-- | Open-function declaration: @:- open_function name/arity@ (extensible
-- from other modules via 'withExtensions').
openFunction :: Text -> Int -> Declaration
openFunction name arity =
  FunctionDecl
    { name = name,
      arity = arity,
      argTypes = Nothing,
      returnType = Nothing,
      isOpen = True,
      kind = DKFunction,
      requiring = Nothing
    }

-- | Class declaration: @:- class name/arity@ (multi-signature overloading).
class_ :: Text -> Int -> Declaration
class_ name arity =
  FunctionDecl
    { name = name,
      arity = arity,
      argTypes = Nothing,
      returnType = Nothing,
      isOpen = False,
      kind = DKClass,
      requiring = Nothing
    }

-- | Open-class declaration: @:- open_class name/arity@ (extensible with
-- signatures and equations from other modules).
openClass :: Text -> Int -> Declaration
openClass name arity =
  FunctionDecl
    { name = name,
      arity = arity,
      argTypes = Nothing,
      returnType = Nothing,
      isOpen = True,
      kind = DKClass,
      requiring = Nothing
    }

-- | @:- extend_class_type (name(args) -> ret)@: adds a signature to an
-- open class declared in another module, resolved through this module's
-- imports.
extendClassType :: Text -> [TypeExpr] -> TypeExpr -> Declaration
extendClassType name argTypes returnType =
  ExtendClassTypeDecl
    { name = name,
      arity = length argTypes,
      argTypes = Just argTypes,
      returnType = Just returnType,
      target = Nothing
    }

-- | @:- module(m, [type(name/arity)])@: exports the type and all its
-- constructors.
typeExport :: Text -> Int -> Declaration
typeExport n a = TypeExportDecl n a Nothing

-- | @:- module(m, [type(name/arity, [c1, c2])])@: exports the type and
-- only the listed constructors; @[]@ exports the type alone.
typeExportWith :: Text -> Int -> [Text] -> Declaration
typeExportWith n a cs = TypeExportDecl n a (Just cs)

-- | Operator declaration: @:- op(Fixity, OpType, Name)@.
op :: Int -> OpType -> Text -> Declaration
op fixity opType opName = OperatorDecl OpDecl {fixity, opType, opName}

-- ---------------------------------------------------------------------------
-- Type definitions
-- ---------------------------------------------------------------------------

-- | Algebraic type definition: name, type variables, constructors.
tyDef :: Text -> [Text] -> [DataConstructor] -> TypeDefinition
tyDef n vs cs =
  TypeDefinition
    { name = Unqualified n,
      typeVars = vs,
      kind = Algebraic cs,
      loc = dummyLoc
    }

-- | Opaque type definition: a nominal name with type parameters and no
-- constructors.
tyOpaque :: Text -> [Text] -> TypeDefinition
tyOpaque n vs =
  TypeDefinition
    { name = Unqualified n,
      typeVars = vs,
      kind = Opaque,
      loc = dummyLoc
    }

-- | Data constructor: name and argument types.
dataCtor :: Text -> [TypeExpr] -> DataConstructor
dataCtor n args = DataConstructor {conName = Unqualified n, conArgs = args}

-- ---------------------------------------------------------------------------
-- Rules
-- ---------------------------------------------------------------------------

-- | A simpagation kept/removed pair from '\\', awaiting a body via '<=>'.
data Simpa = Simpa
  { kept :: [Term],
    removed :: [Term]
  }

-- | LHS of '<=>': a term list (simplification) or a 'Simpa' (simpagation).
class IsRuleHead h where
  toRuleHead :: h -> Head

instance IsRuleHead [Term] where
  toRuleHead = Simplification . map termToConstraint

instance IsRuleHead Simpa where
  toRuleHead s =
    Simpagation (map termToConstraint s.kept) (map termToConstraint s.removed)

-- | Head-constraint occurrence from a compound or atom 'Term'; anything
-- else throws (see the module header).
termToConstraint :: Term -> Constraint
termToConstraint (CompoundTerm n args) = Constraint n args
termToConstraint t =
  errorWithoutStackTrace $
    "YCHR.DSL: term is not a valid constraint occurrence: " <> show t

-- | Attach a name to a rule.
(@:) :: Text -> Rule -> Rule
n @: (Rule _ h g b) = Rule (Just (noAnn n)) h g b

-- | Simplification rule (@head \<=\> body@), or simpagation when the LHS is
-- a @kept \\\\ removed@ 'Simpa'.
(<=>) :: (IsRuleHead h) => h -> [Term] -> Rule
h <=> body =
  Rule Nothing (noAnnP (toRuleHead h)) (noAnnP []) (noAnnP body)

-- | Propagation rule (@head ==\> body@).
(==>) :: [Term] -> [Term] -> Rule
lhs ==> rhs =
  Rule
    Nothing
    (noAnnP (Propagation (map termToConstraint lhs)))
    (noAnnP [])
    (noAnnP rhs)

-- | Simpagation split @kept \\\\ removed@; follow with '<=>'.
(\\) :: [Term] -> [Term] -> Simpa
k \\ r = Simpa {kept = k, removed = r}

-- | Attach a guard to a rule (binds looser than '<=>' \/ '==>').
(|-) :: Rule -> [Term] -> Rule
r |- g = let Rule n h _ b = r in Rule n h (noAnnP g) b

infix 4 .=.

infix 4 .==, .<, .<=, .>, .>=

infixl 6 .+, .-

infixl 7 .*, ./

infixr 3 \\

infixr 3 `is`

infix 2 <=>, ==>

infixl 1 |-

infixr 0 @:

-- ---------------------------------------------------------------------------
-- Terms
-- ---------------------------------------------------------------------------

-- | Compound term with an unqualified functor. Serves for constraint
-- occurrences, function calls, and data constructors alike; the renamer
-- and desugarer classify it.
term :: Text -> [Term] -> Term
term n args = CompoundTerm (Unqualified n) args

-- | Compound term with a module-qualified functor.
qterm :: Text -> Text -> [Term] -> Term
qterm m n args = CompoundTerm (Qualified m n) args

-- | Variable term (surface @X@).
var :: Text -> Term
var = VarTerm

-- | Atom term: a 0-arity unqualified compound, as in the parsed AST.
atom :: Text -> Term
atom s = CompoundTerm (Unqualified s) []

-- | Integer literal term (arbitrary precision).
int :: Integer -> Term
int = IntTerm

-- | Floating-point literal term.
float :: Double -> Term
float = FloatTerm

-- | The @true@ \/ @false@ atom the renamer expects (same as 'atom').
bool :: Bool -> Term
bool True = CompoundTerm (Unqualified "true") []
bool False = CompoundTerm (Unqualified "false") []

-- | Text/string literal term.
text :: Text -> Term
text = TextTerm

-- | Wildcard pattern: matches anything without binding.
wildcard :: Term
wildcard = Wildcard

-- ---------------------------------------------------------------------------
-- Goal sugar
-- ---------------------------------------------------------------------------

-- | Structural unification goal, written @=@ in the surface language.
(.=.) :: Term -> Term -> Term
l .=. r = CompoundTerm (Unqualified "=") [l, r]

-- | Arithmetic-evaluation goal @V is Expr@.
is :: Term -> Term -> Term
is v e = CompoundTerm (Unqualified "is") [v, e]

-- | Host-language call @host:f(args)@.
hostCall :: Text -> [Term] -> Term
hostCall f args = CompoundTerm (Qualified "host" f) args

-- ---------------------------------------------------------------------------
-- Function equations and lambdas
-- ---------------------------------------------------------------------------

-- | Function equation: name, patterns, guards, single-expression body.
-- 'equationSeq' takes a sequenced body.
equation :: Text -> [Term] -> [Term] -> Term -> FunctionEquation
equation n args guard rhs = equationSeq n args guard (NE.singleton rhs)

-- | 'equation' with a sequenced body @A1, …, Return@: the last term is the
-- result; earlier terms must be @is@ bindings or actions (host call,
-- discardable function call). Validated by the desugarer.
equationSeq ::
  Text -> [Term] -> [Term] -> NE.NonEmpty Term -> FunctionEquation
equationSeq n args guard rhs =
  FunctionEquation
    { funName = Unqualified n,
      args = args,
      guard = noAnnP guard,
      rhs = noAnnP rhs
    }

-- | Lambda @fun(args) -> body end@: the compound @\'->\'(fun(args), body)@,
-- lifted during desugaring.
lambda :: [Term] -> Term -> Term
lambda args body =
  CompoundTerm
    (Unqualified "->")
    [CompoundTerm (Unqualified "fun") args, body]

-- | First-class reference to a named function, @fun name/arity@; call it
-- with 'call_'.
funRef :: Text -> Int -> Term
funRef n arity =
  CompoundTerm
    (Unqualified "fun")
    [ CompoundTerm
        (Unqualified "/")
        [CompoundTerm (Unqualified n) [], IntTerm (fromIntegral arity)]
    ]

-- | Call a 'lambda' or 'funRef' value: @'$call'(F, A1, …)@.
call_ :: Term -> [Term] -> Term
call_ f args = CompoundTerm (Unqualified "$call") (f : args)

-- ---------------------------------------------------------------------------
-- Numeric and comparison sugar
-- ---------------------------------------------------------------------------

-- $numericSugar
--
-- 'Term' is a 'Num' instance, so @var "X" `is` (1 + 2 * var "Y")@ works
-- without 'int' (caveats in the module header). The dotted operators build
-- the same compounds explicitly; the comparison ones build guard goals.

instance Num Term where
  fromInteger n = IntTerm n
  l + r = CompoundTerm (Unqualified "+") [l, r]
  l - r = CompoundTerm (Unqualified "-") [l, r]
  l * r = CompoundTerm (Unqualified "*") [l, r]

  -- @-1 :: Term@ arrives as @negate (IntTerm 1)@; fold it into the literal,
  -- since the prelude has no unary minus and a @-(1)@ compound dies with an
  -- arity error at tell time.
  negate (IntTerm n) = IntTerm (negate n)
  negate (FloatTerm x) = FloatTerm (negate x)
  -- Non-literals keep the compound form with an /unqualified/ functor, so
  -- they work only if the program declares @-\/1@, @abs\/1@, @sign\/1@;
  -- otherwise they fail at tell time.
  negate x = CompoundTerm (Unqualified "-") [x]
  abs x = CompoundTerm (Unqualified "abs") [x]
  signum x = CompoundTerm (Unqualified "sign") [x]

(.+), (.-), (.*), (./) :: Term -> Term -> Term
l .+ r = CompoundTerm (Unqualified "+") [l, r]
l .- r = CompoundTerm (Unqualified "-") [l, r]
l .* r = CompoundTerm (Unqualified "*") [l, r]
l ./ r = CompoundTerm (Unqualified "/") [l, r]

(.<), (.<=), (.>), (.>=), (.==) :: Term -> Term -> Term
l .< r = CompoundTerm (Unqualified "<") [l, r]
l .<= r = CompoundTerm (Unqualified "=<") [l, r]
l .> r = CompoundTerm (Unqualified ">") [l, r]
l .>= r = CompoundTerm (Unqualified ">=") [l, r]
l .== r = CompoundTerm (Unqualified "==") [l, r]

-- ---------------------------------------------------------------------------
-- Compiling and running
-- ---------------------------------------------------------------------------

-- | Compile the modules (stdlib included) and run one goal with the CLI's
-- default host-call registry. Returns the bindings of the goal's
-- variables. Compilation and runtime errors are thrown as 'YCHR.Run.Error'.
runDSL :: [Module] -> Term -> IO (Map Text Term)
runDSL =
  runDSLWithHostCallRegistry defaultHostCallRegistry

-- | 'runDSL' with an explicit host-call registry.
runDSLWithHostCallRegistry ::
  HostCallRegistry -> [Module] -> Term -> IO (Map Text Term)
runDSLWithHostCallRegistry hostCalls modules goal = do
  cp <- compileOrThrow modules
  runProgramWithGoalDSL cp hostCalls (termToConstraint goal)

compileOrThrow :: [Module] -> IO CompiledProgram
compileOrThrow modules = case compileParsedModules True modules of
  Left err -> throwIO err
  Right (cp, _warnings :: [Warning]) -> pure cp
