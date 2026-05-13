{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | A Haskell-embedded DSL for building CHR programs without going through
-- @.chr@ source files. Use it when @ychr@ is embedded as a library: build
-- one or more 'Module' values, then compile and run them with 'runDSL'.
--
-- = Worked example: less-than-or-equal
--
-- > {-# LANGUAGE OverloadedStrings #-}
-- > import YCHR.DSL
-- >
-- > orderModule :: Module
-- > orderModule =
-- >   module' "Order"
-- >     `declaring` ["leq" // 2]
-- >     `defining`
-- >       [ "refl" @: [term "leq" [var "X", var "X"]] <=> [bool True]
-- >       , "antisymm"
-- >           @: [term "leq" [var "X", var "Y"]] \\\\ [term "leq" [var "Y", var "X"]]
-- >             <=> [var "X" .=. var "Y"]
-- >       , "trans"
-- >           @: [term "leq" [var "X", var "Y"], term "leq" [var "Y", var "Z"]]
-- >             ==> [term "leq" [var "X", var "Z"]]
-- >       ]
-- >
-- > main :: IO ()
-- > main = do
-- >   bindings <- runDSL [orderModule] (term "leq" [var "A", var "B"])
-- >   print bindings
--
-- The DSL is a thin layer over 'YCHR.Parsed.Module': every combinator is a
-- pure function that builds AST nodes the parser would otherwise produce
-- from @.chr@ text. It does not validate the program — undeclared
-- constraints, ill-typed bodies, etc. are caught downstream by the
-- compilation pipeline ('compileParsedModules') exactly as for parsed
-- input.
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
    DataConstructor,
    TypeExpr (..),
    tyDef,
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
import Data.Map.Strict (Map)
import Data.Text (Text)
import YCHR.Meta (metaHostCallRegistry)
import YCHR.Parsed
import YCHR.Run
  ( CompiledProgram,
    Warning,
    compileParsedModules,
    runProgramWithGoalDSL,
  )
import YCHR.Runtime.Registry (HostCallRegistry, baseHostCallRegistry)

-- ---------------------------------------------------------------------------
-- Modules
-- ---------------------------------------------------------------------------

-- | An empty module with the given name.
module' :: Text -> Module
module' name =
  Module
    { name = name,
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

-- | Append plain @use_module(M)@ imports to a module.
--
-- > module' "Logic" `importing` ["Order", "Util"]
--
-- Note: this combinator appends to any imports already present.
importing :: Module -> [Text] -> Module
importing m imps =
  m {imports = m.imports ++ map (noAnnP . (`ModuleImport` Nothing)) imps}

-- | Append a single @use_module(library(L))@ import (a stdlib library or
-- bundled library, as opposed to a user-written sibling module).
--
-- > module' "MyApp" `library` "lists" `library` "math"
library :: Module -> Text -> Module
library m libName =
  m {imports = m.imports ++ [noAnnP (LibraryImport libName Nothing)]}

-- | Append constraint, function, operator, or type-export declarations.
--
-- > module' "M" `declaring` ["leq" // 2, function "factorial" 1]
declaring :: Module -> [Declaration] -> Module
declaring m ds = m {decls = m.decls ++ map noAnn ds}

-- | Append rules to a module.
defining :: Module -> [Rule] -> Module
defining m rls = m {rules = m.rules ++ rls}

-- | Append function-definition equations to a module.
--
-- > module' "M"
-- >   `declaring` [function "factorial" 1]
-- >   `withEquations`
-- >     [ equation "factorial" [int 0]    [] (int 1)
-- >     , equation "factorial" [var "N"]  [var "N" .> int 0]
-- >         (var "N" .* call_ (funRef "factorial" 1) [var "N" .- int 1])
-- >     ]
withEquations :: Module -> [FunctionEquation] -> Module
withEquations m eqs = m {equations = m.equations ++ map noAnnP eqs}

-- | Append function-equation /extensions/ to a module. Mirrors
-- @:- extend_function name(args) -> body@ directives in source
-- form: the equations contribute to an open function declared in
-- another module (resolved through this module's imports).
withExtensions :: Module -> [FunctionEquation] -> Module
withExtensions m eqs = m {extensions = m.extensions ++ map noAnnP eqs}

-- | Append class-equation /extensions/ to a module. Mirrors
-- @:- extend_class name(args) -> body@ directives in source form:
-- the equations contribute to an open class declared in another
-- module (resolved through this module's imports).
withClassExtensions :: Module -> [FunctionEquation] -> Module
withClassExtensions m eqs =
  m {classExtensions = m.classExtensions ++ map noAnnP eqs}

-- | Append a CHR-type definition (@:- chr_type ...@).
chrType :: Module -> TypeDefinition -> Module
chrType m ty = m {typeDecls = m.typeDecls ++ [noAnn ty]}

-- | Replace the export list of a module.
--
-- An absent export list (the default after 'module'') means the
-- module exports everything by name. Calling 'exporting' switches the
-- module to an explicit export list. Subsequent calls /append/ to that
-- list rather than replacing it.
exporting :: Module -> [Declaration] -> Module
exporting m ds = case m.exports of
  Nothing -> m {exports = Just (noAnnP ds)}
  Just (AnnP existing loc origin) ->
    m {exports = Just (AnnP (existing ++ ds) loc origin)}

-- ---------------------------------------------------------------------------
-- Declarations
-- ---------------------------------------------------------------------------

-- | Constraint declaration. Mirrors @:- chr_constraint name/arity@.
--
-- > "leq" // 2
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

-- | Open-function declaration: @:- open_function name/arity@. Open functions
-- can be extended with new equations from other modules.
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

-- | Class declaration: @:- class name/arity@. A class enables
-- multi-signature overloading.
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

-- | Open-class declaration: @:- open_class name/arity@. Open classes
-- can be extended with new signatures and equations from other modules.
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

-- | Extension type declaration: @:- extend_class_type (name(args) -> ret)@.
-- Adds an overloaded signature to an open class declared in another
-- module. The renamer resolves the class name through the importing
-- module's imports.
extendClassType :: Text -> [TypeExpr] -> TypeExpr -> Declaration
extendClassType name argTypes returnType =
  ExtendClassTypeDecl
    { name = name,
      arity = length argTypes,
      argTypes = Just argTypes,
      returnType = Just returnType,
      target = Nothing
    }

-- | Type-export declaration: @:- module(m, [type(name/arity)])@. Exports
-- the type and all of its data constructors.
typeExport :: Text -> Int -> Declaration
typeExport n a = TypeExportDecl n a Nothing

-- | Type-export declaration with a constructor allowlist:
-- @:- module(m, [type(name/arity, [c1, c2])])@. Exports the type and only
-- the listed constructors. Pass @[]@ to export the type without any
-- constructors.
typeExportWith :: Text -> Int -> [Text] -> Declaration
typeExportWith n a cs = TypeExportDecl n a (Just cs)

-- | Operator declaration. Mirrors @:- op(Fixity, OpType, Name)@.
--
-- > op 700 Xfx "is"
op :: Int -> OpType -> Text -> Declaration
op fixity opType opName = OperatorDecl OpDecl {fixity, opType, opName}

-- ---------------------------------------------------------------------------
-- Type definitions
-- ---------------------------------------------------------------------------

-- | Build a type definition: name, type variables, constructors.
--
-- > tyDef "color" [] [dataCtor "red" [], dataCtor "green" [], dataCtor "blue" []]
tyDef :: Text -> [Text] -> [DataConstructor] -> TypeDefinition
tyDef n vs cs =
  TypeDefinition
    { name = Unqualified n,
      typeVars = vs,
      constructors = cs,
      loc = dummyLoc
    }

-- | Build a data constructor: name and argument types.
--
-- > dataCtor "cons" [TypeVar "a", TypeCon (Unqualified "list") [TypeVar "a"]]
dataCtor :: Text -> [TypeExpr] -> DataConstructor
dataCtor n args = DataConstructor {conName = Unqualified n, conArgs = args}

-- ---------------------------------------------------------------------------
-- Rules
-- ---------------------------------------------------------------------------

-- | A simpagation kept/removed pair, awaiting a body via '<=>'.
--
-- Produced by '\\'; consumed by '<=>' through 'IsRuleHead'.
data Simpa = Simpa
  { kept :: [Term],
    removed :: [Term]
  }

-- | The left-hand side of a '<=>': either a list of terms (simplification)
-- or a 'Simpa' (simpagation).
class IsRuleHead h where
  toRuleHead :: h -> Head

instance IsRuleHead [Term] where
  toRuleHead = Simplification . map termToConstraint

instance IsRuleHead Simpa where
  toRuleHead s =
    Simpagation (map termToConstraint s.kept) (map termToConstraint s.removed)

-- | Convert a 'Term' built by 'term' / 'qterm' / 'atom' into a head
-- 'Constraint' occurrence. Compound and atom terms map to a constraint;
-- anything else (a bare variable, integer, etc.) is rejected with the
-- same shape of error the parser raises for a 'MalformedConstraint'.
termToConstraint :: Term -> Constraint
termToConstraint (CompoundTerm n args) = Constraint n args
termToConstraint (AtomTerm n) = Constraint (Unqualified n) []
termToConstraint t =
  errorWithoutStackTrace $
    "YCHR.DSL: term is not a valid constraint occurrence: " <> show t

-- | Attach a name to a rule.
--
-- > "trans" @: [term "leq" [var "X", var "Y"], ...] ==> [...]
(@:) :: Text -> Rule -> Rule
n @: (Rule _ h g b) = Rule (Just (noAnn n)) h g b

-- | Simplification rule (@head \<=\> body@) or simpagation rule
-- (@kept \\ removed \<=\> body@), depending on the LHS.
--
-- > [term "p" []]                <=> [bool True]   -- simplification
-- > [term "k" []] \\ [term "r" []] <=> [bool True] -- simpagation
(<=>) :: (IsRuleHead h) => h -> [Term] -> Rule
h <=> body =
  Rule Nothing (noAnnP (toRuleHead h)) (noAnnP []) (noAnnP body)

-- | Propagation rule (@head ==\> body@).
--
-- > [term "leq" [var "X", var "Y"], term "leq" [var "Y", var "Z"]]
-- >   ==> [term "leq" [var "X", var "Z"]]
(==>) :: [Term] -> [Term] -> Rule
lhs ==> rhs =
  Rule
    Nothing
    (noAnnP (Propagation (map termToConstraint lhs)))
    (noAnnP [])
    (noAnnP rhs)

-- | Simpagation split: @kept \\ removed@. Followed by '<=>' body.
(\\) :: [Term] -> [Term] -> Simpa
k \\ r = Simpa {kept = k, removed = r}

-- | Attach a guard to a rule.
--
-- > [term "p" [var "X"]] <=> [bool True] |- [var "X" .> int 0]
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

-- | Compound term with an unqualified functor.
--
-- The same constructor serves for constraint occurrences (in rule heads
-- or as body goals), function calls, and data-constructor terms — the
-- surface language draws no distinction between them, so the DSL doesn't
-- either. Classification happens later, in the renamer and desugarer.
--
-- > term "leq" [var "X", var "Y"]
term :: Text -> [Term] -> Term
term n args = CompoundTerm (Unqualified n) args

-- | Compound term with a fully-qualified functor.
--
-- > qterm "Order" "leq" [var "X", var "Y"]
qterm :: Text -> Text -> [Term] -> Term
qterm m n args = CompoundTerm (Qualified m n) args

-- | Variable term: 'var' \"X\" produces the same AST as the surface @X@.
var :: Text -> Term
var = VarTerm

-- | Atom term.
atom :: Text -> Term
atom = AtomTerm

-- | Integer literal term.
int :: Int -> Term
int = IntTerm

-- | Floating-point literal term.
float :: Double -> Term
float = FloatTerm

-- | Boolean literal — produces the canonical @true@ / @false@ atom term
-- the renamer expects. Equivalent to @atom \"true\"@ / @atom \"false\"@.
bool :: Bool -> Term
bool True = AtomTerm "true"
bool False = AtomTerm "false"

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

-- | Arithmetic-evaluation goal: @V is Expr@.
--
-- > var "X" `is` (int 1 .+ var "Y")
is :: Term -> Term -> Term
is v e = CompoundTerm (Unqualified "is") [v, e]

-- | Host-language call, written @host:f(args)@ in the surface language.
--
-- > hostCall "print" [var "X"]
hostCall :: Text -> [Term] -> Term
hostCall f args = CompoundTerm (Qualified "host" f) args

-- ---------------------------------------------------------------------------
-- Function equations and lambdas
-- ---------------------------------------------------------------------------

-- | A single function-defining equation.
--
-- > equation "factorial" [int 0]   [] (int 1)
-- > equation "factorial" [var "N"] [var "N" .> int 0]
-- >   (var "N" .* call_ (funRef "factorial" 1) [var "N" .- int 1])
equation :: Text -> [Term] -> [Term] -> Term -> FunctionEquation
equation n args guard rhs =
  FunctionEquation
    { funName = Unqualified n,
      args = args,
      guard = noAnnP guard,
      rhs = noAnnP rhs
    }

-- | An anonymous function (lambda) term. Mirrors @fun(args) -> body end@.
-- Internally a lambda is the compound @'->'(fun(args), body)@; lambda lifting
-- happens during desugaring.
--
-- > lambda [var "X"] (var "X" .+ int 1)
lambda :: [Term] -> Term -> Term
lambda args body =
  CompoundTerm
    (Unqualified "->")
    [CompoundTerm (Unqualified "fun") args, body]

-- | Reference a named function as a first-class value: @fun name/arity@.
--
-- The surface syntax @fun foo/2@ produces the AST below, callable via 'call_'.
funRef :: Text -> Int -> Term
funRef n arity =
  CompoundTerm
    (Unqualified "fun")
    [CompoundTerm (Unqualified "/") [AtomTerm n, IntTerm arity]]

-- | Call a first-class function value (a 'lambda' or 'funRef') with the
-- given arguments. Mirrors the surface @'$call'(F, A1, A2, ...)@.
call_ :: Term -> [Term] -> Term
call_ f args = CompoundTerm (Unqualified "$call") (f : args)

-- ---------------------------------------------------------------------------
-- Numeric and comparison sugar
-- ---------------------------------------------------------------------------

-- $numericSugar
--
-- The 'Term' type is an instance of 'Num' so integer literals can be
-- written without 'int' and the standard arithmetic operators
-- (@+@, @-@, @*@, 'negate') compile to the corresponding compound terms
-- the surface language recognises.
--
-- > var "X" `is` (1 + 2 * var "Y")
--
-- For users who prefer to keep the AST literal-explicit, the prefixed
-- operators ('.+', '.-', '.*', './') do the same job without the
-- 'Num' machinery, and the comparison operators ('.<', '.<=', '.>',
-- '.>=', '.==') build comparison goals usable in guards.

instance Num Term where
  fromInteger n = IntTerm (fromInteger n)
  l + r = CompoundTerm (Unqualified "+") [l, r]
  l - r = CompoundTerm (Unqualified "-") [l, r]
  l * r = CompoundTerm (Unqualified "*") [l, r]
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

-- | Compile DSL-built modules and run a single goal against them, using
-- the same default host-call registry as the @ychr@ CLI
-- (@baseHostCallRegistry <> metaHostCallRegistry@). Includes the stdlib.
--
-- The goal is built with 'term' / 'qterm' just like rule heads. Returns
-- the final unification map for the variables mentioned in the goal.
-- Compilation or runtime errors are raised as exceptions.
--
-- > main = do
-- >   bindings <- runDSL [orderModule] (term "leq" [var "A", var "B"])
-- >   print bindings
runDSL :: [Module] -> Term -> IO (Map Text Term)
runDSL = runDSLWithHostCallRegistry (baseHostCallRegistry <> metaHostCallRegistry)

-- | Like 'runDSL', but takes an explicit host-call registry. Use this when
-- the program calls custom @host:_@ functions registered by the embedder.
runDSLWithHostCallRegistry ::
  HostCallRegistry -> [Module] -> Term -> IO (Map Text Term)
runDSLWithHostCallRegistry hostCalls modules goal = do
  cp <- compileOrThrow modules
  snd <$> runProgramWithGoalDSL cp hostCalls (termToConstraint goal)

compileOrThrow :: [Module] -> IO CompiledProgram
compileOrThrow modules = case compileParsedModules True modules of
  Left err -> throwIO err
  Right (cp, _warnings :: [Warning]) -> pure cp
