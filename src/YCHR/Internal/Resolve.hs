{-# LANGUAGE OverloadedStrings #-}

-- | Post-rename resolution.
--
-- Flattens @[CollectedModule]@ into a single 'R.Program', grouping function
-- equations under their declarations and verifying that declaration
-- kinds are used consistently.
module YCHR.Internal.Resolve
  ( -- * Errors
    ResolveError (..),
    RefiningViolation (..),

    -- * Resolution
    resolveProgram,
    termToExpr,

    -- * Visibility
    FunVisibility,
    buildQueryFunctionVisibility,
  )
where

import Control.Monad (unless, when)
import Control.Monad.Trans.State.Strict
  ( State,
    evalState,
    execState,
    get,
    gets,
    modify',
    put,
  )
import Control.Monad.Trans.Writer.CPS (Writer, runWriter, tell)
import Data.List (nub)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, fromMaybe, listToMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
-- MicroHs's 'Data.Text' lacks 'breakOn'; the shim supplies it
-- (dev-docs/MICROHS_GAPS.md, gap 4).
import Data.Text.Shim qualified as T
import YCHR.Internal.Collected (CollectedImport (..), CollectedModule (..))
import YCHR.Internal.Diagnostic (Diagnostic, noDiag)
import YCHR.Internal.PExpr qualified as PExpr
import YCHR.Internal.Parsed (FunctionDeclKind (..))
import YCHR.Internal.Parsed qualified as P
import YCHR.Internal.Rename.Types (importListPermits, valueEntry)
import YCHR.Internal.Resolved qualified as R
import YCHR.Internal.Types
  ( Aggregate (..),
    AggregateConjunct (..),
    BoundSig (..),
    Constraint (..),
    ConstraintKey (..),
    ConstraintUse (..),
    DataConstructor (..),
    FunSignature (..),
    HeadArg (..),
    Name (..),
    QualifiedConstraint (..),
    QualifiedIdentifier (..),
    QualifiedName (..),
    Term (..),
    TypeExpr (..),
    UnqualifiedIdentifier (..),
    flattenName,
    qualifiedToName,
    typeConstructors,
    unqualifiedText,
  )
-- Hidden so '.head' resolves under MicroHs (dev-docs/MICROHS_GAPS.md, gap 1).
import Prelude hiding (head)

-- | Why a program's declarations or extension directives cannot be
-- resolved.
data ResolveError
  = -- | A name declared as a constraint has function equations.
    ConstraintHasEquations Name
  | -- | A name declared as a function appears in a rule head.
    FunctionInRuleHead Name
  | -- | A name collides with a reserved built-in.
    ReservedName Name
  | -- | A user module is declared with a reserved name (currently
    -- only @host@, which is wired in as the host-call qualifier).
    ReservedModuleName Text
  | -- | A constraint name reached the resolve phase without being
    -- module-qualified by the renamer. Indicates a renamer bug rather
    -- than user error.
    UnqualifiedConstraintName Name
  | -- | An @:- extend_class_type@, @:- extend_function@, or
    -- @:- extend_class@ directive targets a declaration that is not
    -- open (no @open_function@ / @open_class@ keyword).
    ExtendsClosedFunction Name
  | -- | A free-floating function equation appears in a module that is
    -- not the declaring module of the function. Carries the qualified
    -- function name and the module in which the equation was found.
    OrphanFunctionEquation Name Text
  | -- | An @:- extend_class_type@ directive targets an open class
    -- that itself carries a @requiring@ clause. The instance set of a
    -- bounded open class is determined by its bounds, not by
    -- enumerated extensions.
    ExtendTypeOnBoundedFunction Name
  | -- | A @requiring@ clause references a type variable that does not
    -- appear in the enclosing declaration's primary signature. Carries
    -- the enclosing declaration's flattened name and the offending
    -- variable name.
    UnboundBoundVariable Text Text
  | -- | A @requiring@ clause names a function that is not declared in
    -- the program (or is declared at a different arity). Carries the
    -- enclosing declaration's flattened name, the bound function's
    -- flattened name, and the bound's arity.
    UnknownBoundFunction Text Text Int
  | -- | The bound graph contains a cycle. Carries the flattened names
    -- of the declarations on the cycle in source order.
    BoundCycle [Text]
  | -- | A @:- function@ or @:- open_function@ declaration carries
    -- more than one signature for the same name and arity. Multiple
    -- signatures require the @:- class@ / @:- open_class@ form.
    MultiSigOnFunction Name
  | -- | The same name and arity is declared with both @:- function@
    -- / @:- open_function@ and @:- class@ / @:- open_class@. The two
    -- forms are mutually exclusive.
    MixedDeclKinds Name
  | -- | An @:- extend_class_type@ directive targets a declaration
    -- declared with @:- function@ / @:- open_function@. The type
    -- extension only makes sense against an @:- open_class@.
    ExtendClassTypeOnFunction Name
  | -- | An @:- extend_class@ directive targets a declaration
    -- declared with @:- function@ / @:- open_function@; use
    -- @:- extend_function@ instead.
    ExtendClassOnFunction Name
  | -- | An @:- extend_function@ directive targets a declaration
    -- declared with @:- class@ / @:- open_class@; use
    -- @:- extend_class@ instead.
    ExtendFunctionOnClass Name
  | -- | The same name and arity is declared as both
    -- @:- chr_constraint@ and @:- function@ / @:- open_function@ /
    -- @:- class@ / @:- open_class@ in a single module. Constraints
    -- and functions share the symbol namespace, so the collision is
    -- ambiguous regardless of whether the name is ever referenced.
    ConstraintFunctionCollision Name
  | -- | The same name is declared as a data constructor (via
    -- @:- chr_type@) and as a function-like form in a single module.
    -- Unlike the cross-module case — which stays legal, because
    -- @m:name@ says which namespace is meant and is reported per bare
    -- use as @ConstructorFunctionAmbiguity@ — qualification cannot
    -- tell these two apart: both spell as @m:name@. So the collision
    -- is rejected at the declaration, regardless of arity and
    -- regardless of whether the name is ever used.
    ConstructorFunctionCollision Name
  | -- | A @refining@ clause appears on a declaration that cannot
    -- carry one, or names a type that is not a valid refinement.
    -- Carries the declaration's flattened name and one violation; a
    -- declaration with several gets one error per violation.
    InvalidRefining Text RefiningViolation
  | -- | A lambda parameter is neither a variable nor a wildcard.
    -- Lambda params must be patterns; literals and compound terms
    -- are rejected here so the resolved AST guarantees well-formed
    -- 'R.LambdaExpr' values.
    LambdaParamError Term
  | -- | A lambda was written with an empty parameter list
    -- (@fun() -> Body end@). Lambdas must take at least one
    -- parameter; users who want a no-arg helper should declare a
    -- named function via @:- function@. The 'R.LambdaExpr' parameter
    -- list is 'NonEmpty', so the resolver substitutes a single
    -- wildcard for recovery.
    EmptyLambdaParams
  | -- | A @'$call'@ was used at an unsupported arity: zero (a missing
    -- callee or a callee with no arguments) or more than
    -- 'R.maxCallArity'. Carries the number of call arguments, so a
    -- bare @'$call'@ and @'$call'(F)@ both report zero. That range is
    -- the surface language's supported dynamic-call arity, so an
    -- out-of-range call is rejected here, where the @'$call'@ shape is
    -- recognized, so that programs, queries and generated drivers all
    -- see the error.
    UnsupportedCallArity Int
  | -- | An @:- inline@ directive names a @name\/arity@ that this
    -- module does not itself declare with @:- function@ \/
    -- @:- class@. Cross-module inlining is not supported: a bare
    -- name only says which function is meant via the declaring
    -- module's own declaration, so @:- inline@ can only target a
    -- local one. Carries the local name and arity as written.
    InlineUnknownFunction Text Int
  | -- | An @:- inline@ directive targets an @:- open_function@ \/
    -- @:- open_class@ declaration. An open function's equation set
    -- is not fixed in the declaring module, so there is nothing
    -- there to substitute at a call site. Carries the local name
    -- and arity as written.
    InlineOpenFunction Text Int
  | -- | A @:- constraint_use@ entry names a @name\/arity@ that this
    -- module does not itself declare with @:- chr_constraint@. The
    -- directive does not reach across modules, so a constraint's use
    -- policy has exactly one declaration site. Carries the local name
    -- and arity as written.
    ConstraintUseUnknownConstraint Text Int
  | -- | A @:- constraint_use@ entry names a constraint that an earlier
    -- entry in the same module already named, under the same tag or a
    -- different one. Reported on every entry after the first. Carries
    -- the local name and arity as written.
    ConstraintUseConflictingDeclaration Text Int
  deriving (Eq, Show)

-- | Why a @refining@ clause is rejected. A @refining@ clause is
-- permitted only on a closed @:- function@ carrying a single typed
-- signature of the exact shape @name(any) -> bool@, and the refined
-- type must be a base type or a type constructor applied to distinct
-- type variables. 'YCHR.Internal.Display' owns the wording.
data RefiningViolation
  = -- | Written on @:- class@ / @:- open_class@.
    RefiningOnClass
  | -- | Written on an open declaration (@:- open_function@ or
    -- @:- open_class@).
    RefiningOnOpenDeclaration
  | -- | Written on the untyped @name\/arity@ spelling.
    RefiningOnUntyped
  | -- | The declared arity is not 1. Carries the declared arity.
    RefiningArity Int
  | -- | The single argument type is not @any@.
    RefiningArgNotAny
  | -- | The return type is not @bool@.
    RefiningReturnNotBool
  | -- | The refined type is a bare type variable, which says nothing.
    RefiningBareVariable
  | -- | The refined type is @any@, which says nothing.
    RefiningAny
  | -- | The refined type is a function type.
    RefiningFunctionType
  | -- | A parameter of the refined type constructor is not a type
    -- variable. The solver pins only the outermost constructor, so
    -- @refining list(int)@ would silently mean @refining list(A)@.
    RefiningConcreteParameter
  | -- | A parameter variable of the refined type constructor occurs
    -- more than once. Carries the repeated variable's name.
    RefiningRepeatedParameter Text
  deriving (Eq, Show)

-- | Flatten modules into a single resolved program: collect the
-- constraint and function declarations, group equations under their
-- function declarations, translate guards and bodies to 'R.Expr', and
-- run the declaration checks below. Any check failing fails the whole
-- program.
resolveProgram :: [CollectedModule] -> Either [Diagnostic ResolveError] R.Program
resolveProgram mods =
  let constraintNames = buildConstraintNames mods
      functionNames = buildFunctionNames mods
      conTypes = collectConstraintTypes mods
      conBounds = collectConstraintBounds mods
      typeDefs = [td.node | m <- mods, td <- m.typeDecls]
      funcOpenness = buildFunctionOpenness mods
      funcKinds = buildFunctionKinds mods
      funcRequiring = buildFunctionRequiring mods
      eqErrors = checkEquations constraintNames mods
      headErrors = checkRuleHeads (Set.map qualifiedToName functionNames) mods
      reservedErrors = checkReservedNames mods
      reservedModuleErrors = checkReservedModuleNames mods
      orphanEqErrors = checkOrphanEquations functionNames mods
      extendsClosedErrors = checkExtendsClosed funcOpenness mods
      extendsBoundedErrors = checkExtendsBounded funcRequiring mods
      boundedDeclErrors = checkBoundedDeclarations functionNames mods
      refiningDeclErrors = checkRefiningDeclarations mods
      multiSigErrors = checkMultiSigOnFunction mods
      mixedKindErrors = checkMixedDeclKinds mods
      extensionKindErrors = checkExtensionKinds funcKinds mods
      collisionErrors = checkConstraintFunctionCollision mods
      conCollisionErrors = checkConstructorFunctionCollision mods
      inlineErrors = checkInlineDeclarations mods
      inlineSet = buildInlineSet mods
      constraintUseErrors = checkConstraintUseDeclarations mods
      funVisibility = buildFunctionVisibility mods
      (resolvedRules, ruleErrs) = runWriter (resolveRules funVisibility mods)
      (resolvedFunctions, funErrs) =
        runWriter (resolveFunctions funVisibility inlineSet mods)
      errs =
        eqErrors
          ++ headErrors
          ++ reservedErrors
          ++ reservedModuleErrors
          ++ orphanEqErrors
          ++ extendsClosedErrors
          ++ extendsBoundedErrors
          ++ boundedDeclErrors
          ++ refiningDeclErrors
          ++ multiSigErrors
          ++ mixedKindErrors
          ++ extensionKindErrors
          ++ collisionErrors
          ++ conCollisionErrors
          ++ inlineErrors
          ++ constraintUseErrors
          ++ ruleErrs
          ++ funErrs
   in if null errs
        then
          Right
            R.Program
              { rules = resolvedRules,
                functions = resolvedFunctions,
                constraintTypes = conTypes,
                constraintBounds = conBounds,
                constraintUses = buildConstraintUses mods,
                nameVisibility = buildNameVisibility mods,
                functionNames = functionNames,
                typeDefinitions = typeDefs
              }
        else Left errs

-- ---------------------------------------------------------------------------
-- Declaration collection
-- ---------------------------------------------------------------------------

buildConstraintNames :: [CollectedModule] -> Set QualifiedIdentifier
buildConstraintNames mods =
  Set.fromList
    [ QualifiedIdentifier m.name cd.name cd.arity
    | m <- mods,
      P.Ann d _ <- m.decls,
      P.ConstraintDecl cd <- [d]
    ]

buildFunctionNames :: [CollectedModule] -> Set QualifiedName
buildFunctionNames mods =
  Set.fromList
    [ QualifiedName m.name fd.name
    | m <- mods,
      P.Ann d _ <- m.decls,
      P.FunctionDecl fd <- [d]
    ]

{- Note [FunVisibility vs renamer visibility]

The renamer qualifies every constraint, type, and data-constructor
reference per-module: it knows which providers each module imports
and rewrites bare names to 'Qualified' form. So by the time we reach
Resolve, those three name classes are already disambiguated.

Functions are different. In @NoResolve@ positions (compound
arguments of tell-side body constraints and top-level goals) the
renamer deliberately leaves compound heads unqualified — the
call-vs-constructor decision is structural and gets made here in
'termToExpr'. To make that decision we need the same
function-visibility view the renamer uses for @ResolveAll@ /
@ResolveTop@ positions, but restricted to 'FunctionDecl': hence
'FunVisibility'.

The model is per-module: 'buildFunctionVisibility' produces one
table per source module, keyed by the local @(name, arity)@ a term
might mention; 'buildQueryFunctionVisibility' produces a single
combined table for the synthetic @<query>@ module the renamer
fabricates for top-level goals (see 'Rename.buildQueryRenameEnv'). Both
are read by 'termToExpr' to commit each compound to a 'CallExpr' or
'CtorExpr'.
-}

-- | Per-module function visibility. Maps each local @(name, arity)@
-- reachable from the module to the qualified names of the function
-- declarations that provide it.
-- See Note [FunVisibility vs renamer visibility].
type FunVisibility = Map UnqualifiedIdentifier [QualifiedName]

-- | Per-module constraint and function visibility: each local
-- @(name, arity)@ a module can name, with the qualified declarations
-- that provide it. Same shape as 'FunVisibility'; see
-- 'buildNameVisibility'.
type NameVisibility = Map UnqualifiedIdentifier [QualifiedName]

-- | Build a function-visibility map for every module in a program.
--
-- A function declared in module @P@ is visible in module @M@ iff
-- either @P == M@, or @M@ has a @use_module(P)@ import whose import
-- list permits the declared @(name, arity)@ and @P@'s export list
-- (if any) includes the declaration. By this stage
-- 'YCHR.Internal.Collect.rewriteImports' has collapsed every import into a
-- 'CollectedImport', so there is only one import kind to handle.
buildFunctionVisibility :: [CollectedModule] -> Map Text FunVisibility
buildFunctionVisibility = buildDeclVisibility functionKey
  where
    functionKey (P.FunctionDecl fd) = Just (UnqualifiedIdentifier fd.name fd.arity)
    functionKey _ = Nothing

-- | Per-module visibility of constraints and functions together, built
-- by the same rule as 'buildFunctionVisibility'. It is the namespace the
-- renamer resolves a goal's name in, so a bare name with both a
-- constraint and a function provider is ambiguous here as it is there.
-- Read by the compiler to build the tellables table a dynamic
-- @tell\/N@ resolves through (see 'YCHR.Internal.Compile.buildTellables').
buildNameVisibility :: [CollectedModule] -> Map Text NameVisibility
buildNameVisibility = buildDeclVisibility valueEntry

-- | The visibility rule shared by 'buildFunctionVisibility' and
-- 'buildNameVisibility', over the declarations @declKey@ selects.
-- A declaration in module @P@ is visible in module @M@ iff either
-- @P == M@, or @M@ has a @use_module(P)@ import whose import list
-- permits it and @P@'s export list (if any) includes it.
buildDeclVisibility ::
  (P.Declaration -> Maybe UnqualifiedIdentifier) ->
  [CollectedModule] ->
  Map Text (Map UnqualifiedIdentifier [QualifiedName])
buildDeclVisibility declKey mods =
  Map.fromList [(m.name, perModule m) | m <- mods]
  where
    perModule selfMod =
      Map.fromListWith
        (\a b -> nub (a ++ b))
        [ (key, [QualifiedName provider.name key.localName])
        | provider <- mods,
          P.Ann d _ <- provider.decls,
          Just key <- [declKey d],
          visibleTo selfMod provider key
        ]

    visibleTo selfMod provider key
      | provider.name == selfMod.name = True
      | not (importPermits selfMod provider key) = False
      | otherwise = exportPermits provider key

    importPermits selfMod provider key =
      any
        (matchesImport provider.name key)
        [im.node | im <- selfMod.imports]

    matchesImport providerName key im
      | im.importModule == providerName =
          importListPermits valueEntry key im.importItems
      | otherwise = False

    exportPermits provider key = case provider.exports of
      Nothing -> True
      Just annExports -> importListPermits valueEntry key (Just annExports.node)

-- | Look up the function-visibility table for a single module,
-- returning the empty map for unknown modules.
funVisibilityFor :: Map Text FunVisibility -> Text -> FunVisibility
funVisibilityFor mv m = Map.findWithDefault Map.empty m mv

-- | Visibility table for query-time term resolution. A query has no
-- enclosing module and sees every /exported/ function declared by any
-- loaded module, mirroring the synthetic @\<query\>@ module the
-- renamer builds in 'Rename.buildQueryRenameEnv' (which imports every
-- module with @use_module(M)@ and resolves names through each
-- module's export list). Used by 'YCHR.Run' to translate top-level
-- goal and argument terms.
--
-- See Note [FunVisibility vs renamer visibility].
buildQueryFunctionVisibility :: [CollectedModule] -> FunVisibility
buildQueryFunctionVisibility mods =
  Map.fromListWith
    (\a b -> nub (a ++ b))
    [ (UnqualifiedIdentifier fd.name fd.arity, [QualifiedName m.name fd.name])
    | m <- mods,
      P.Ann d _ <- m.decls,
      P.FunctionDecl fd <- [d],
      exportedBy m fd
    ]
  where
    exportedBy m fd = case m.exports of
      Nothing -> True
      Just annExports -> any (matchesFunDecl fd) annExports.node

    matchesFunDecl fd (P.FunctionDecl fd') =
      fd'.name == fd.name && fd'.arity == fd.arity
    matchesFunDecl fd (P.ConstraintDecl cd) =
      cd.name == fd.name && cd.arity == fd.arity
    matchesFunDecl _ _ = False

-- | Map each declared function to whether its declaration is open.
buildFunctionOpenness :: [CollectedModule] -> Map QualifiedName Bool
buildFunctionOpenness mods =
  Map.fromList
    [ (QualifiedName m.name fd.name, fd.isOpen)
    | m <- mods,
      P.Ann d _ <- m.decls,
      P.FunctionDecl fd <- [d]
    ]

-- | Map each declared function to the kind of its primary declaration.
-- When the same name is declared with both kinds, an arbitrary winner
-- is recorded here; the conflict is reported separately by
-- 'checkMixedDeclKinds'.
buildFunctionKinds :: [CollectedModule] -> Map QualifiedName FunctionDeclKind
buildFunctionKinds mods =
  Map.fromList
    [ (QualifiedName m.name fd.name, fd.kind)
    | m <- mods,
      P.Ann d _ <- m.decls,
      P.FunctionDecl fd <- [d]
    ]

collectConstraintTypes :: [CollectedModule] -> Map ConstraintKey [TypeExpr]
collectConstraintTypes mods =
  Map.fromList
    [ (ConstraintKey (QualifiedName m.name cd.name) cd.arity, ts)
    | m <- mods,
      P.Ann d _ <- m.decls,
      P.ConstraintDecl cd <- [d],
      let ts = case cd.argTypes of
            Just types -> types
            Nothing -> replicate cd.arity (TypeCon (Unqualified "any") [])
    ]

-- | Bounds declared on every @:- chr_constraint@ that carries a
-- @requiring@ clause. Unbounded constraints are absent from the map.
collectConstraintBounds :: [CollectedModule] -> Map ConstraintKey [BoundSig]
collectConstraintBounds mods =
  Map.fromList
    [ (ConstraintKey (QualifiedName m.name cd.name) cd.arity, bs)
    | m <- mods,
      P.Ann d _ <- m.decls,
      P.ConstraintDecl cd <- [d],
      Just bs <- [cd.requiring]
    ]

-- | Bounds declared on every @:- function@ / @:- open_function@ that
-- carries a @requiring@ clause. Unbounded functions are absent.
buildFunctionRequiring :: [CollectedModule] -> Map QualifiedName [BoundSig]
buildFunctionRequiring mods =
  Map.fromList
    [ (QualifiedName m.name fd.name, bs)
    | m <- mods,
      P.Ann d _ <- m.decls,
      P.FunctionDecl fd <- [d],
      Just bs <- [fd.requiring]
    ]

-- ---------------------------------------------------------------------------
-- Validation (integrated into resolution)
-- ---------------------------------------------------------------------------

-- | Check that no equation targets a constraint-declared name.
-- Reports only the first equation per name.
checkEquations ::
  Set QualifiedIdentifier -> [CollectedModule] -> [Diagnostic ResolveError]
checkEquations cNames mods =
  [ noDiag
      ( P.AnnP
          (ConstraintHasEquations annEq.node.funName)
          annEq.sourceLoc
          annEq.parsed
      )
  | annEq <- firstPerKey eqKey offending
  ]
  where
    offending =
      [ annEq
      | m <- mods,
        annEq <- m.equations,
        Just qid <- [eqKey annEq],
        qid `Set.member` cNames
      ]
    eqKey annEq = toQualId annEq.node.funName (length annEq.node.args)

-- | Check that no free-floating equation lives in a module that is not
-- the declaring module of the function. Equations contributed from
-- other modules must be wrapped in @:- extend_function ...@ directives.
-- Unknown function names are skipped here; they are reported by the
-- renamer as YCHR-20002.
checkOrphanEquations ::
  Set QualifiedName -> [CollectedModule] -> [Diagnostic ResolveError]
checkOrphanEquations functionNames mods =
  [ noDiag
      ( P.AnnP
          (OrphanFunctionEquation annEq.node.funName m.name)
          annEq.sourceLoc
          annEq.parsed
      )
  | m <- mods,
    annEq <- m.equations,
    Qualified targetMod baseName <- [annEq.node.funName],
    targetMod /= m.name,
    QualifiedName targetMod baseName `Set.member` functionNames
  ]

-- | Check that @:- extend_class_type@, @:- extend_function@, and
-- @:- extend_class@ directives only target open declarations.
-- Targets unknown to the compiler are already reported by the renamer.
checkExtendsClosed ::
  Map QualifiedName Bool -> [CollectedModule] -> [Diagnostic ResolveError]
checkExtendsClosed funcOpenness mods =
  let declErrs =
        [ noDiag
            (P.AnnP (ExtendsClosedFunction target) loc (PExpr.Atom ed.name))
        | m <- mods,
          P.Ann d loc <- m.extensionTypes,
          P.ExtendClassTypeDecl ed <- [d],
          Just target <- [ed.target],
          isKnownClosed funcOpenness target
        ]
      eqnErrs =
        [ noDiag
            ( P.AnnP
                (ExtendsClosedFunction annEq.node.funName)
                annEq.sourceLoc
                annEq.parsed
            )
        | m <- mods,
          annEq <- m.extensions ++ m.classExtensions,
          isKnownClosed funcOpenness annEq.node.funName
        ]
   in declErrs ++ eqnErrs
  where
    isKnownClosed openness (Qualified mn n) =
      case Map.lookup (QualifiedName mn n) openness of
        Just False -> True
        _ -> False
    isKnownClosed _ _ = False

-- | Reject @:- function@ / @:- open_function@ groups that carry more
-- than one typed signature for the same name and arity.
-- Multi-signature overloading requires @:- class@ / @:- open_class@.
-- Untyped declarations contribute no signature, so they are not
-- counted. One diagnostic is emitted per group, pointing at the
-- second offending declaration.
checkMultiSigOnFunction :: [CollectedModule] -> [Diagnostic ResolveError]
checkMultiSigOnFunction mods =
  [ declDiag MultiSigOnFunction entry
  | decls <- groupedFunctionDecls mods,
    let typedFunDecls =
          [ entry
          | entry <- decls,
            entry.decl.kind == DKFunction,
            Just _ <- [entry.decl.argTypes],
            Just _ <- [entry.decl.returnType]
          ],
    entry : _ <- [drop 1 typedFunDecls]
  ]

-- | Reject groups where the same name+arity is declared with both
-- @:- function@-style and @:- class@-style keywords. One diagnostic
-- is emitted per group, pointing at the first declaration whose kind
-- differs from the group's first declaration.
checkMixedDeclKinds :: [CollectedModule] -> [Diagnostic ResolveError]
checkMixedDeclKinds mods =
  [ declDiag MixedDeclKinds entry
  | decls@(first : _) <- groupedFunctionDecls mods,
    entry : _ <- [[e | e <- decls, e.decl.kind /= first.decl.kind]]
  ]

-- | Reject same name+arity declared as both @:- chr_constraint@ and a
-- function-like form (@:- function@, @:- open_function@, @:- class@,
-- @:- open_class@) in a single module. Constraints and functions share
-- the symbol namespace, so the collision is ambiguous regardless of
-- whether the name is ever referenced. One diagnostic per
-- @(module, name, arity)@ collision, pointed at the first
-- function-side declaration (subsequent function-side declarations of
-- the same name are suppressed to avoid duplicate diagnostics when a
-- name is declared as e.g. both @:- function@ and @:- class@).
checkConstraintFunctionCollision :: [CollectedModule] -> [Diagnostic ResolveError]
checkConstraintFunctionCollision mods =
  map (declDiag ConstraintFunctionCollision) (firstPerKey entryKey entries)
  where
    entries =
      [ entry
      | (i, m) <- zip [0 ..] mods,
        let conKeys =
              Set.fromList
                [ UnqualifiedIdentifier cd.name cd.arity
                | P.Ann c _ <- m.decls,
                  P.ConstraintDecl cd <- [c]
                ],
        entry <- moduleFunctionDecls i m,
        Set.member (UnqualifiedIdentifier entry.decl.name entry.decl.arity) conKeys
      ]

-- | Reject a data constructor whose name is also declared as a
-- function-like form (@:- function@, @:- open_function@, @:- class@,
-- @:- open_class@) in the /same/ module.
--
-- Arity plays no part on either side: data constructors are name-only
-- in the type system ('YCHR.Internal.Constructors.buildConMap' keys on
-- 'Name' alone), and a reader cannot tell which namespace @foo(X)@
-- means from the arity anyway.
--
-- Constraints are not compared here, and deliberately so: nothing is
-- ambiguous between them and constructors. 'termToExpr' never
-- resolves a compound to a constraint call, so the two never contend
-- for one reading, and a constraint may share a name with a data
-- constructor. Constraint-versus-/function/ is a third question
-- again, handled by 'checkConstraintFunctionCollision'.
--
-- The cross-module case is deliberately /not/ handled here. There the
-- two names are distinguishable — @a:foo@ calls, @b:foo@ builds data —
-- so only a bare reference is ambiguous, and the renamer reports that
-- per use site as @ConstructorFunctionAmbiguity@ (YCHR-20020). Within
-- one module both spell as @m:foo@ and nothing can separate them, so
-- the declaration itself is the error.
--
-- One diagnostic per @(module, constructorName)@, pointed at the type
-- declaration that introduces the constructor.
checkConstructorFunctionCollision :: [CollectedModule] -> [Diagnostic ResolveError]
checkConstructorFunctionCollision mods =
  [ noDiag
      ( P.AnnP
          (ConstructorFunctionCollision (qualifiedToName entry.node))
          entry.sourceLoc
          (PExpr.Atom entry.node.baseName)
      )
  | entry <- firstPerKey (.node) entries
  ]
  where
    entries =
      [ P.Ann (QualifiedName m.name n) loc
      | m <- mods,
        let funNames =
              Set.fromList
                [fn.name | P.Ann d _ <- m.decls, P.FunctionDecl fn <- [d]],
        P.Ann td loc <- m.typeDecls,
        dc <- typeConstructors td,
        let n = unqualifiedText dc.conName,
        Set.member n funNames
      ]

-- | Keep the first element for each key, in list order.
firstPerKey :: (Ord k) => (a -> k) -> [a] -> [a]
firstPerKey key = go Set.empty
  where
    go _ [] = []
    go seen (x : xs)
      | Set.member k seen = go seen xs
      | otherwise = x : go (Set.insert k seen) xs
      where
        k = key x

-- | Validate every @:- inline@ directive: the named @name\/arity@ must
-- be declared, by the /same/ module, with @:- function@ \/ @:- class@
-- (not @:- open_function@ \/ @:- open_class@). One diagnostic per
-- offending entry.
--
-- The remaining eligibility checks — exactly one equation, no guards,
-- no prelude, no inline-to-inline cycle — need the post-HNF shape of
-- the function's equations, which only exists after desugaring; see
-- 'YCHR.Internal.Desugar.Inline'.
checkInlineDeclarations :: [CollectedModule] -> [Diagnostic ResolveError]
checkInlineDeclarations mods =
  [ noDiag (P.AnnP err entry.sourceLoc (PExpr.Atom entry.node.name))
  | m <- mods,
    entry <- m.inlines,
    let spec = entry.node
        ownDecls =
          [ fd
          | P.Ann d _ <- m.decls,
            P.FunctionDecl fd <- [d],
            fd.name == spec.name,
            fd.arity == spec.arity
          ],
    err <- case ownDecls of
      [] -> [InlineUnknownFunction spec.name spec.arity]
      _ | any (.isOpen) ownDecls -> [InlineOpenFunction spec.name spec.arity]
      _ -> []
  ]

-- | The set of @(qualified name, arity)@ pairs named by a valid
-- @:- inline@ directive somewhere in the program. Built regardless of
-- 'checkInlineDeclarations'\'s errors; 'resolveProgram' only consults
-- the resulting 'R.Program' when that list is empty, so an invalid
-- entry here never reaches a 'R.FunctionDef'.
buildInlineSet :: [CollectedModule] -> Set ConstraintKey
buildInlineSet mods =
  Set.fromList
    [ ConstraintKey (QualifiedName m.name entry.node.name) entry.node.arity
    | m <- mods,
      entry <- m.inlines
    ]

-- | Validate every @:- constraint_use@ directive: the named
-- @name\/arity@ must be declared with @:- chr_constraint@ by the
-- /same/ module, and no constraint may be named twice within it. One
-- diagnostic per offending entry; a repeated entry is reported on each
-- occurrence after the first, whether or not its tag agrees.
--
-- Checking rule heads against the declared policy is a separate,
-- @--no-check@-gated pass; see "YCHR.Internal.ConstraintUse".
checkConstraintUseDeclarations :: [CollectedModule] -> [Diagnostic ResolveError]
checkConstraintUseDeclarations mods =
  [ noDiag (P.AnnP err entry.sourceLoc (PExpr.Atom spec.name))
  | m <- mods,
    let declared =
          Set.fromList
            [ UnqualifiedIdentifier cd.name cd.arity
            | P.Ann d _ <- m.decls,
              P.ConstraintDecl cd <- [d]
            ],
    (i, entry) <- zip [0 :: Int ..] m.constraintUses,
    let spec = entry.node
        earlier =
          [UnqualifiedIdentifier e.node.name e.node.arity | e <- take i m.constraintUses],
    err <- entryErrors declared earlier spec
  ]
  where
    entryErrors declared earlier spec
      | not (Set.member key declared) =
          [ConstraintUseUnknownConstraint spec.name spec.arity]
      | key `elem` earlier =
          [ConstraintUseConflictingDeclaration spec.name spec.arity]
      | otherwise = []
      where
        key = UnqualifiedIdentifier spec.name spec.arity

-- | The declared use policy of every constraint named by a
-- @:- constraint_use@ directive, keyed by its qualified name and arity.
-- A constraint absent from the map is 'UseAny', so explicit @any@
-- entries are left out. Built regardless of
-- 'checkConstraintUseDeclarations'\'s errors; 'resolveProgram' only
-- returns the program when that list is empty.
buildConstraintUses :: [CollectedModule] -> Map ConstraintKey ConstraintUse
buildConstraintUses mods =
  Map.fromList
    [ (ConstraintKey (QualifiedName m.name spec.name) spec.arity, spec.use)
    | m <- mods,
      entry <- m.constraintUses,
      let spec = entry.node,
      spec.use /= UseAny
    ]

-- | Reject extension directives whose declaration kind disagrees with
-- the target's kind:
--
--   * @:- extend_class_type@ on a @DKFunction@ target
--   * @:- extend_class@ on a @DKFunction@ target
--   * @:- extend_function@ on a @DKClass@ target
--
-- Targets unknown to the compiler are already reported by the renamer.
checkExtensionKinds ::
  Map QualifiedName FunctionDeclKind ->
  [CollectedModule] ->
  [Diagnostic ResolveError]
checkExtensionKinds funcKinds mods =
  classTypeErrs ++ extendFunErrs ++ extendClassErrs
  where
    classTypeErrs =
      [ noDiag
          (P.AnnP (ExtendClassTypeOnFunction target) loc (PExpr.Atom ed.name))
      | m <- mods,
        P.Ann d loc <- m.extensionTypes,
        P.ExtendClassTypeDecl ed <- [d],
        Just target <- [ed.target],
        targetKind target == Just DKFunction
      ]
    extendFunErrs =
      [ noDiag
          ( P.AnnP
              (ExtendFunctionOnClass annEq.node.funName)
              annEq.sourceLoc
              annEq.parsed
          )
      | m <- mods,
        annEq <- m.extensions,
        targetKind annEq.node.funName == Just DKClass
      ]
    extendClassErrs =
      [ noDiag
          ( P.AnnP
              (ExtendClassOnFunction annEq.node.funName)
              annEq.sourceLoc
              annEq.parsed
          )
      | m <- mods,
        annEq <- m.classExtensions,
        targetKind annEq.node.funName == Just DKFunction
      ]
    targetKind (Qualified mn n) = Map.lookup (QualifiedName mn n) funcKinds
    targetKind _ = Nothing

-- | A function declaration with its owning module and location.
data FunctionDeclEntry = FunctionDeclEntry
  { decl :: P.FunctionDeclBody,
    owner :: CollectedModule,
    -- | The owner's position in the input list. Tells two same-named
    -- modules apart.
    moduleIndex :: Int,
    loc :: P.SourceLoc
  }

-- | The function declarations of the module at position @i@, in source
-- order.
moduleFunctionDecls :: Int -> CollectedModule -> [FunctionDeclEntry]
moduleFunctionDecls i m =
  [ FunctionDeclEntry {decl = fd, owner = m, moduleIndex = i, loc = loc}
  | P.Ann d loc <- m.decls,
    P.FunctionDecl fd <- [d]
  ]

-- | Every function declaration of the program, in source order.
functionDeclEntries :: [CollectedModule] -> [FunctionDeclEntry]
functionDeclEntries mods = concat (zipWith moduleFunctionDecls [0 ..] mods)

-- | The module, name and arity of a function declaration.
entryKey :: FunctionDeclEntry -> QualifiedIdentifier
entryKey entry =
  QualifiedIdentifier entry.owner.name entry.decl.name entry.decl.arity

-- | A diagnostic about one function declaration, anchored at it.
declDiag :: (Name -> ResolveError) -> FunctionDeclEntry -> Diagnostic ResolveError
declDiag mkErr entry =
  noDiag
    ( P.AnnP
        (mkErr (Qualified entry.owner.name entry.decl.name))
        entry.loc
        (PExpr.Atom entry.decl.name)
    )

-- | Group every @FunctionDecl@ in the program by module, name and
-- arity. Used by the kind / cardinality checks above. Per-group
-- entries appear in source order (left-to-right across modules, then
-- top-to-bottom within each module), so callers that want "the
-- first/second offending declaration" can rely on list position.
groupedFunctionDecls :: [CollectedModule] -> [[FunctionDeclEntry]]
groupedFunctionDecls mods =
  -- 'Map.fromListWith (++)' would build groups in reverse source order
  -- (right-associative accumulation). To keep source order, build a
  -- difference list (left-to-right append) and materialize each group
  -- at the end.
  [vs [] | vs <- Map.elems grouped]
  where
    grouped =
      Map.fromListWith
        (\new old -> old . new)
        [ (entryKey entry, ([entry] ++))
        | entry <- functionDeclEntries mods
        ]

-- | Reject @:- extend_class_type@ directives that target a bounded
-- open function. The instance set of a bounded open function is
-- determined by its bound-named functions, not by enumerated extensions.
-- @:- extend_function@ / @:- extend_class@ (equation extension) are
-- /not/ rejected here — new equations of a bounded open function are
-- valid and are checked under the same ambient bound as the original
-- equations.
checkExtendsBounded ::
  Map QualifiedName [BoundSig] -> [CollectedModule] -> [Diagnostic ResolveError]
checkExtendsBounded funcRequiring mods =
  [ noDiag
      (P.AnnP (ExtendTypeOnBoundedFunction target) loc (PExpr.Atom ed.name))
  | m <- mods,
    P.Ann d loc <- m.extensionTypes,
    P.ExtendClassTypeDecl ed <- [d],
    Just target <- [ed.target],
    isBounded target
  ]
  where
    isBounded (Qualified mn n) =
      Map.member (QualifiedName mn n) funcRequiring
    isBounded _ = False

-- | Validate every @requiring@ clause in the program.
--
-- Reports three kinds of error:
--
--   * 'UnboundBoundVariable' — a type variable in the @requiring@
--     clause has no occurrence in the enclosing declaration's primary
--     signature.
--   * 'UnknownBoundFunction' — the bound's named function (with that
--     exact arity) is not declared anywhere in the program.
--   * 'BoundCycle' — the bound graph (with vertices for every function
--     and bounded constraint, and edges from each declaration to the
--     functions named in its @requiring@ clause) contains a cycle.
--
-- All three checks run together so the user sees every shape of bound
-- error in a single pass.
checkBoundedDeclarations ::
  Set QualifiedName -> [CollectedModule] -> [Diagnostic ResolveError]
checkBoundedDeclarations functionNames mods =
  let funcBounds =
        [ BoundedDecl
            { name = QualifiedName m.name fd.name,
              primaryVars = primaryVars,
              bounds = bs,
              origin = originForDecl m fd.name
            }
        | m <- mods,
          P.Ann d _ <- m.decls,
          P.FunctionDecl fd <- [d],
          Just bs <- [fd.requiring],
          let primaryVars =
                Set.fromList $
                  concatMap typeExprVars (fromMaybe [] fd.argTypes)
                    ++ maybe [] typeExprVars fd.returnType
        ]
      conBounds =
        [ BoundedDecl
            { name = QualifiedName m.name cd.name,
              primaryVars = primaryVars,
              bounds = bs,
              origin = originForDecl m cd.name
            }
        | m <- mods,
          P.Ann d _ <- m.decls,
          P.ConstraintDecl cd <- [d],
          Just bs <- [cd.requiring],
          let primaryVars =
                Set.fromList (concatMap typeExprVars (fromMaybe [] cd.argTypes))
        ]
      allBounded = funcBounds ++ conBounds
      varErrs =
        [ noDiag (P.AnnP (UnboundBoundVariable declText v) bs.loc bd.origin)
        | bd <- allBounded,
          let declText = qualifiedToLooseText bd.name,
          bs <- bd.bounds,
          let bsVars =
                Set.fromList
                  (concatMap typeExprVars bs.argTypes ++ typeExprVars bs.returnType),
          v <- Set.toList bsVars,
          Set.notMember v bd.primaryVars
        ]
      unknownErrs =
        [ noDiag
            ( P.AnnP
                (UnknownBoundFunction declText (flattenName bs.name) bs.arity)
                bs.loc
                bd.origin
            )
        | bd <- allBounded,
          let declText = qualifiedToLooseText bd.name,
          bs <- bd.bounds,
          not (boundResolvesToFunction bs)
        ]
      cycleErrs = detectBoundCycles allBounded
   in varErrs ++ unknownErrs ++ cycleErrs
  where
    qualifiedToLooseText qn = flattenName (qualifiedToName qn)
    boundResolvesToFunction bs = case bs.name of
      Qualified m n -> Set.member (QualifiedName m n) functionNames
      Unqualified _ ->
        -- If the renamer left the name 'Unqualified', no visible
        -- provider exposes a function (or anything else) at this
        -- name/arity, so the dedicated 'UnknownBoundFunction'
        -- diagnostic is ours to emit; the renamer does not report
        -- this case as the generic YCHR-20002.
        False
    -- Takes the declaration's name rather than the declaration record:
    -- a helper that projected @.name@ off its argument would be inferred
    -- as 'HasField'-polymorphic, which MicroHs does not generalize, so
    -- its two uses at different record types would fail to unify
    -- (dev-docs/MICROHS_GAPS.md, gap 10).
    originForDecl m n = PExpr.Atom (m.name <> ":" <> n)

-- | Validate every @refining@ clause in the program.
--
-- A @refining@ clause is an /axiom/: it promises that a successful
-- call of the function on a bare variable proves that variable's type,
-- and the checker never inspects the equations. The declaration's
-- shape is therefore all that can be enforced. It must be a closed
-- @:- function@ carrying a single typed signature of the exact shape
-- @name(any) -> bool@, and the refined type must be a base type or a
-- type constructor applied to distinct type variables — the solver
-- pins only the outermost constructor, so @refining list(int)@ could
-- only ever mean @refining list(A)@ and is rejected rather than
-- silently widened.
--
-- Every violation of a single declaration is reported, so one
-- compilation shows the user all of them.
checkRefiningDeclarations :: [CollectedModule] -> [Diagnostic ResolveError]
checkRefiningDeclarations mods =
  [ noDiag (P.AnnP (InvalidRefining declText v) loc origin)
  | m <- mods,
    P.Ann d loc <- m.decls,
    P.FunctionDecl fd <- [d],
    Just refined <- [fd.refining],
    let declText =
          flattenName (qualifiedToName (QualifiedName m.name fd.name)),
    let origin = PExpr.Atom (m.name <> ":" <> fd.name),
    v <- declViolations fd ++ refinedTypeViolations refined
  ]
  where
    declViolations fd =
      [RefiningOnClass | fd.kind == DKClass]
        ++ [RefiningOnOpenDeclaration | fd.isOpen]
        ++ [RefiningArity fd.arity | fd.arity /= 1]
        ++ case (fd.argTypes, fd.returnType) of
          (Just [argTy], Just retTy) ->
            [RefiningArgNotAny | not (isAnyType argTy)]
              ++ [RefiningReturnNotBool | not (isBoolType retTy)]
          -- The arity is already reported; the return type is still
          -- worth checking on its own.
          (Just _, Just retTy) -> [RefiningReturnNotBool | not (isBoolType retTy)]
          _ -> [RefiningOnUntyped]

    refinedTypeViolations (TypeVar _) = [RefiningBareVariable]
    refinedTypeViolations t
      | isAnyType t = [RefiningAny]
      | isFunctionType t = [RefiningFunctionType]
    refinedTypeViolations (TypeCon _ params) =
      [RefiningConcreteParameter | any (not . isTypeVar) params]
        ++ [RefiningRepeatedParameter v | v <- repeatedVars params]

    repeatedVars params =
      let vs = [v | TypeVar v <- params]
       in nub [v | v <- vs, length (filter (== v) vs) > 1]

    isTypeVar (TypeVar _) = True
    isTypeVar _ = False

    -- At any arity: @any(A)@ is not a type constructor the checker
    -- knows, and it would slip past the parameter rules below while
    -- proving no more than bare @any@ does.
    isAnyType (TypeCon (Unqualified "any") _) = True
    isAnyType _ = False

    -- The two-level spelling 'Encode.typeExpr' reads as a function
    -- type. Anything else headed by @->@ is an ordinary type
    -- reference, as it is everywhere else.
    isFunctionType
      (TypeCon (Unqualified "->") [TypeCon (Unqualified "fun") _, _]) = True
    isFunctionType _ = False

    -- The prelude import is unconditional, so after renaming @bool@
    -- resolves to the prelude's declaration. The unqualified spelling
    -- is accepted as well, which is what an undeclared type would
    -- leave behind.
    isBoolType (TypeCon (Qualified "prelude" "bool") []) = True
    isBoolType (TypeCon (Unqualified "bool") []) = True
    isBoolType _ = False

{- Note [Bound graph cycle detection]

Vertices of the bound graph are the qualified names of bounded
declarations (functions and constraints carrying a @requiring@
clause). There is an edge from @f@ to @g@ whenever @g@ appears in
@f@'s @requiring@ clause; bounded references always resolve to a
function per the spec.

Edges are derived from the @allBounded@ list assembled in
'checkBoundedDeclarations', which reads the @requiring@ field of every
function and constraint declaration.

Detection is a depth-first search that carries the current path. A
vertex is added to @visited@ only after its entire subtree has been
explored, so each simple cycle is reported exactly once even when
several starting vertices reach it.

'BoundCycle' carries the cycle in source order: 'dfs' builds the
cycle by reversing the current DFS path from the re-entered vertex
back to itself, which is the same order in which the bounds were
encountered while walking @requiring@ clauses top-to-bottom.
-}

-- | A declaration (function or constraint) that carries a @requiring@
-- clause.
data BoundedDecl = BoundedDecl
  { name :: QualifiedName,
    -- | The type variables of its primary signature.
    primaryVars :: Set Text,
    bounds :: [BoundSig],
    -- | The origin atom its diagnostics carry.
    origin :: PExpr.PExpr
  }

-- | Detect cycles in the bound graph by depth-first search.
-- See Note [Bound graph cycle detection].
detectBoundCycles :: [BoundedDecl] -> [Diagnostic ResolveError]
detectBoundCycles bounded =
  let graph :: Map QualifiedName [QualifiedName]
      graph =
        Map.fromList
          [ ( bd.name,
              [ QualifiedName m n
              | b <- bd.bounds,
                Qualified m n <- [b.name]
              ]
            )
          | bd <- bounded
          ]
      origins :: Map QualifiedName PExpr.PExpr
      origins = Map.fromList [(bd.name, bd.origin) | bd <- bounded]
      search =
        execState
          (mapM_ (dfs graph []) (Map.keys graph))
          CycleSearch {visited = Set.empty, cycles = []}
   in map (emitCycleDiag origins) search.cycles

-- | The state of 'dfs'.
data CycleSearch = CycleSearch
  { -- | Vertices whose whole subtree is explored.
    visited :: Set QualifiedName,
    -- | Cycles found so far, newest first.
    cycles :: [[QualifiedName]]
  }

-- | Depth-first search from @qn@, with @path@ the vertices above it.
-- Records every cycle it finds. See Note [Bound graph cycle detection].
dfs ::
  Map QualifiedName [QualifiedName] ->
  [QualifiedName] ->
  QualifiedName ->
  State CycleSearch ()
dfs graph path qn
  | qn `elem` path =
      let cycle_ = qn : reverse (takeWhile (/= qn) path) ++ [qn]
       in modify' (\s -> s {cycles = cycle_ : s.cycles})
  | otherwise = do
      seen <- gets (\s -> Set.member qn s.visited)
      unless seen $ do
        mapM_ (dfs graph (qn : path)) (Map.findWithDefault [] qn graph)
        modify' (\s -> s {visited = Set.insert qn s.visited})

emitCycleDiag ::
  Map QualifiedName PExpr.PExpr ->
  [QualifiedName] ->
  Diagnostic ResolveError
emitCycleDiag origins cycle_ =
  let names = map (flattenName . qualifiedToName) cycle_
      origin = case cycle_ of
        (q : _) -> Map.findWithDefault (PExpr.Atom "<bound_cycle>") q origins
        [] -> PExpr.Atom "<bound_cycle>"
      loc' = P.SourceLoc "<bound_cycle>" 0 0
   in noDiag (P.AnnP (BoundCycle names) loc' origin)

-- | Collect every type variable mentioned in a type expression.
typeExprVars :: TypeExpr -> [Text]
typeExprVars (TypeVar v) = [v]
typeExprVars (TypeCon _ args) = concatMap typeExprVars args

-- | Check that no rule head constraint is a function-declared name.
-- Reports only the first rule per name.
checkRuleHeads :: Set Name -> [CollectedModule] -> [Diagnostic ResolveError]
checkRuleHeads fNames mods =
  concat (evalState (traverse check [r | m <- mods, r <- m.rules]) Set.empty)
  where
    -- The state holds the names already reported. A name repeated in
    -- one head is reported once per occurrence.
    check r = do
      seen <- get
      let names =
            [ c.name
            | c <- headConstraints r.head.node,
              c.name `Set.member` fNames,
              c.name `Set.notMember` seen
            ]
      put (foldr Set.insert seen names)
      pure
        [ noDiag (P.AnnP (FunctionInRuleHead n) r.head.sourceLoc r.head.parsed)
        | n <- names
        ]

-- | Reserved names that cannot be used as constraint or function declarations.
reservedDeclNames :: Set Text
reservedDeclNames = Set.fromList ["quote", "tell"]

-- | Check that no declaration uses a reserved name.
checkReservedNames :: [CollectedModule] -> [Diagnostic ResolveError]
checkReservedNames mods =
  [ noDiag (P.AnnP (ReservedName (Qualified m.name n)) loc (PExpr.Atom ""))
  | m <- mods,
    P.Ann d loc <- m.decls,
    n <- declNames d,
    n `Set.member` reservedDeclNames
  ]
  where
    declNames (P.ConstraintDecl cd) = [cd.name]
    declNames (P.FunctionDecl fd) = [fd.name]
    declNames _ = []

-- | Reserved names that cannot be used as user module names. Currently
-- just @host@, which is wired in as the host-call qualifier in
-- @Resolve.termToExpr@; allowing it as a user module name would shadow
-- the user's own functions at their definition site.
reservedModuleNames :: Set Text
reservedModuleNames = Set.fromList ["host"]

-- | Check that no module uses a reserved name.
checkReservedModuleNames :: [CollectedModule] -> [Diagnostic ResolveError]
checkReservedModuleNames mods =
  [ noDiag (P.AnnP (ReservedModuleName m.name) m.nameLoc (PExpr.Atom ""))
  | m <- mods,
    m.name `Set.member` reservedModuleNames
  ]

headConstraints :: P.Head -> [P.Constraint]
headConstraints (P.Simplification cs _) = cs
headConstraints (P.Propagation cs _) = cs
headConstraints (P.Simpagation ks rs _) = ks ++ rs

toQualId :: Name -> Int -> Maybe QualifiedIdentifier
toQualId (Qualified m n) a = Just (QualifiedIdentifier m n a)
toQualId (Unqualified _) _ = Nothing

-- ---------------------------------------------------------------------------
-- Module flattening
-- ---------------------------------------------------------------------------

resolveRules ::
  Map Text FunVisibility ->
  [CollectedModule] ->
  Writer [Diagnostic ResolveError] [R.Rule]
resolveRules visMap mods =
  catMaybes <$> sequence [resolveRule m r | m <- mods, r <- m.rules]
  where
    -- A rule whose head fails is dropped; its guard and body are not
    -- looked at.
    resolveRule m r =
      let vis = funVisibilityFor visMap m.name
       in case resolveHead vis r.head.sourceLoc r.head.parsed r.head.node of
            Left errs -> Nothing <$ tell errs
            Right rh -> do
              guard' <- resolveAnnTerms vis r.guard
              body' <- resolveAnnTerms vis r.body
              pure $
                Just
                  R.Rule
                    { name = r.name,
                      moduleName = m.name,
                      head = P.AnnP rh r.head.sourceLoc r.head.parsed,
                      guard = guard',
                      body = body'
                    }

-- | Translate annotated terms with 'termToExpr', at their own location.
resolveAnnTerms ::
  (Traversable t) =>
  FunVisibility ->
  P.AnnP (t Term) ->
  Writer [Diagnostic ResolveError] (P.AnnP (t R.Expr))
resolveAnnTerms vis a = traverse (traverse (termToExpr vis a.sourceLoc a.parsed)) a

resolveHead ::
  FunVisibility ->
  P.SourceLoc ->
  PExpr.PExpr ->
  P.Head ->
  Either [Diagnostic ResolveError] R.Head
resolveHead vis loc origin h = failOnDiags $ case h of
  P.Simplification cs aggs ->
    R.Simplification <$> qualifyAll cs <*> resolveAll aggs
  P.Propagation cs aggs ->
    R.Propagation <$> qualifyAll cs <*> resolveAll aggs
  P.Simpagation ks rs aggs ->
    R.Simpagation <$> qualifyAll ks <*> qualifyAll rs <*> resolveAll aggs
  where
    qualifyAll = collect . map (qualifyConstraint loc origin)
    resolveAll = collect . map (resolveAggregate vis loc origin)

-- | Run a writer, and fail if it wrote any diagnostic.
failOnDiags :: Writer [e] a -> Either [e] a
failOnDiags w = case runWriter w of
  (a, []) -> Right a
  (_, errs) -> Left errs

-- | Keep the successful results and write the diagnostics, both in
-- order.
collect :: [Either [e] b] -> Writer [e] [b]
collect xs = catMaybes <$> traverse step xs
  where
    step (Right b) = pure (Just b)
    step (Left errs) = Nothing <$ tell errs

-- | Resolve an aggregate: qualify its goal's constraints, and type its
-- expressions. A malformed aggregate reports its own diagnostics and is
-- dropped, so one bad aggregate does not hide the others in the head.
--
-- The aggregator and the element are evaluated, so they go through
-- 'termToExpr', which types them against the module's function
-- visibility. The result stays a 'Term': it is a pattern matched
-- against the computed value, exactly as a head argument is.
resolveAggregate ::
  FunVisibility ->
  P.SourceLoc ->
  PExpr.PExpr ->
  Aggregate ->
  Either [Diagnostic ResolveError] R.Aggregate
resolveAggregate vis loc origin agg = failOnDiags $ do
  mAgg <- traverse (termToExpr vis loc origin) agg.agg
  element' <- termToExpr vis loc origin agg.element
  conjuncts <- collect (map resolveConjunct agg.goal)
  pure
    R.Aggregate
      { R.kind = agg.kind,
        R.agg = mAgg,
        R.element = element',
        R.goal = conjuncts,
        R.result = agg.result
      }
  where
    resolveConjunct (AggConstraint c) =
      R.AggConstraint <$> qualifyConstraint loc origin c
    resolveConjunct (AggNested a) =
      R.AggNested <$> resolveAggregate vis loc origin a
    resolveConjunct (AggGuard g) =
      R.AggGuard <$> failOnDiags (termToExpr vis loc origin g)

qualifyConstraint ::
  P.SourceLoc ->
  PExpr.PExpr ->
  Constraint ->
  Either [Diagnostic ResolveError] QualifiedConstraint
qualifyConstraint loc origin (Constraint n args) = case n of
  Qualified m b -> Right (QualifiedConstraint (QualifiedName m b) args)
  Unqualified _ ->
    Left [noDiag (P.AnnP (UnqualifiedConstraintName n) loc origin)]

resolveFunctions ::
  Map Text FunVisibility ->
  Set ConstraintKey ->
  [CollectedModule] ->
  Writer [Diagnostic ResolveError] [R.FunctionDef]
resolveFunctions visMap inlineSet mods = traverse build (Map.toList grouped)
  where
    -- Group by qualified name and arity. 'Map.fromListWith' leaves each
    -- group in reverse source order.
    grouped =
      Map.fromListWith
        (++)
        [(declKey entry, [entry]) | entry <- functionDeclEntries mods]
    declKey :: FunctionDeclEntry -> ConstraintKey
    declKey entry =
      ConstraintKey (QualifiedName entry.owner.name entry.decl.name) entry.decl.arity
    build (key, entries) = do
      let decls = map (.decl) entries
          -- 'gatherEquations' selects equations by (name, arity)
          -- from the declaring module. Module names are unique across
          -- a program that went through
          -- 'YCHR.Internal.Compile.Pipeline.finalizeCompilation',
          -- which rejects duplicates, so a group normally comes from
          -- one module and gathering once per declaration would
          -- suffice. Deduplicating by input position anyway keeps
          -- 'resolveProgram' safe for a direct caller that bypasses
          -- that check: the two same-named modules' equations are
          -- then both gathered rather than one module's being
          -- silently dropped. (A multi-signature @:- class@
          -- contributes one declaration per signature; gathering per
          -- distinct module, not per declaration, is what stops
          -- every equation being repeated N times.)
          declModules =
            Map.elems (Map.fromList [(entry.moduleIndex, entry) | entry <- entries])
      eqss <-
        traverse
          (\entry -> gatherEquations visMap mods entry.owner entry.decl)
          declModules
      pure
        R.FunctionDef
          { name = key.name,
            arity = key.arity,
            signatures =
              collectSignatures decls
                ++ collectExtensionSignatures mods key.name key.arity,
            isOpen = any (.isOpen) decls,
            requiring = concatMap (fromMaybe [] . (.requiring)) decls,
            -- At most one declaration of the group can carry
            -- one: 'checkRefiningDeclarations' rejects it on
            -- everything but a single-signature @:- function@,
            -- and 'checkMultiSigOnFunction' rejects a second
            -- signature for the same name and arity.
            refining = listToMaybe [t | fd <- decls, Just t <- [fd.refining]],
            inline = Set.member key inlineSet,
            equations = concat eqss
          }

-- | Collect type signatures from a group of declarations for the same function.
collectSignatures :: [P.FunctionDeclBody] -> [FunSignature]
collectSignatures decls =
  [ FunSignature argTys retTy
  | fd <- decls,
    Just argTys <- [fd.argTypes],
    Just retTy <- [fd.returnType]
  ]

-- | Collect signatures contributed by @:- extend_class_type@
-- directives in any module. Only signatures whose resolved target
-- matches the given qualified name and arity are included.
collectExtensionSignatures ::
  [CollectedModule] -> QualifiedName -> Int -> [FunSignature]
collectExtensionSignatures mods qn ar =
  [ FunSignature argTys retTy
  | m <- mods,
    P.Ann d _ <- m.extensionTypes,
    P.ExtendClassTypeDecl ed <- [d],
    ed.arity == ar,
    Just (Qualified tm tn) <- [ed.target],
    QualifiedName tm tn == qn,
    Just argTys <- [ed.argTypes],
    Just retTy <- [ed.returnType]
  ]

-- | Gather equations for a function declaration, stripping the funName.
-- Free-floating equations only come from the declaring module
-- (orphans are rejected by 'checkOrphanEquations'). Extension equations
-- contributed via @:- extend_function@ or @:- extend_class@ are pulled
-- from every module's @extensions@ and @classExtensions@ lists; the
-- @checkExtensionKinds@ pass rejects mismatches between the directive
-- and the target's kind, so by the time we get here either list is a
-- legitimate source for this declaration.
gatherEquations ::
  Map Text FunVisibility ->
  [CollectedModule] ->
  CollectedModule ->
  P.FunctionDeclBody ->
  Writer [Diagnostic ResolveError] [P.AnnP R.FunctionEquation]
gatherEquations visMap mods m fd =
  sequence $
    [strip m annEq | annEq <- m.equations, matches annEq]
      ++ [ strip srcMod annEq
         | srcMod <- mods,
           annEq <- srcMod.extensions ++ srcMod.classExtensions,
           matches annEq
         ]
  where
    qualName = Qualified m.name fd.name
    matches annEq =
      annEq.node.funName == qualName && length annEq.node.args == fd.arity
    strip srcMod = stripFunName (funVisibilityFor visMap srcMod.name)

stripFunName ::
  FunVisibility ->
  P.AnnP P.FunctionEquation ->
  Writer [Diagnostic ResolveError] (P.AnnP R.FunctionEquation)
stripFunName vis (P.AnnP eq loc parsed) = do
  guard' <- resolveAnnTerms vis eq.guard
  rhs' <- resolveAnnTerms vis eq.rhs
  pure (P.AnnP R.FunctionEquation {args = eq.args, guard = guard', rhs = rhs'} loc parsed)

-- | Flatten the top-level comma operator of a 'Term' into a non-empty
-- sequence. Used to give lambda bodies the same sequenced form as
-- top-level function equations.
flattenTermComma :: Term -> NonEmpty Term
flattenTermComma t = case t of
  CompoundTerm (Unqualified ",") [l, r] ->
    flattenTermComma l <> flattenTermComma r
  _ -> t :| []

-- ---------------------------------------------------------------------------
-- Term -> Expr translation
-- ---------------------------------------------------------------------------

-- | Translate a renamed surface 'Term' into the structurally typed
-- 'R.Expr'. The 'FunVisibility' says which qualified compounds
-- are static calls — every other qualified compound is a data
-- constructor. '$call', 'fun name/arity', lambdas, 'host:f' calls,
-- and the @quote/1@ quoting form are recognized by their canonical
-- post-rename shape.
--
-- See Note [FunVisibility vs renamer visibility] for why this pass
-- recomputes function visibility instead of relying on the renamer.
--
-- Diagnostics accumulate in the writer; the translator always returns
-- an 'R.Expr', substituting plausible placeholders so traversal can
-- continue. The enclosing call sites use the accumulated diagnostics
-- (combined with the rest of 'resolveProgram''s checks) to decide
-- whether to fail.
termToExpr ::
  FunVisibility ->
  P.SourceLoc ->
  PExpr.PExpr ->
  Term ->
  Writer [Diagnostic ResolveError] R.Expr
termToExpr vis loc origin = go
  where
    go t = case t of
      VarTerm v -> pure (R.VarExpr v)
      IntTerm n -> pure (R.IntExpr n)
      FloatTerm n -> pure (R.FloatExpr n)
      TextTerm s -> pure (R.TextExpr s)
      Wildcard -> pure R.WildcardExpr
      -- '$call'(F, A1..An) — surface dynamic dispatch. The callee is
      -- the first argument; the rest are the call's actual arguments.
      -- The supported dynamic-call arities are @1 .. 'R.maxCallArity'@
      -- (a surface-language limit aligned with the prelude's
      -- @call\/N@ family), so any other shape of the reserved
      -- @'$call'@ symbol is rejected here rather than silently
      -- becoming a data term. That includes @'$call'(F)@ (no
      -- arguments), a bare @'$call'@ atom, and @'$call'/11@ or wider.
      -- Traversal still yields an 'ApplyExpr' so later checks see the
      -- call's operands.
      CompoundTerm (Unqualified "$call") args -> do
        let callee = case args of
              f : _ -> f
              [] -> Wildcard
            callArity = max 0 (length args - 1)
        when (callArity < 1 || callArity > R.maxCallArity) $
          tell [noDiag (P.AnnP (UnsupportedCallArity callArity) loc origin)]
        R.ApplyExpr <$> go callee <*> traverse go (drop 1 args)
      -- 'fun name/arity' — canonicalized by the renamer to a single
      -- 0-arity compound holding the flat 'module:name'.
      CompoundTerm
        (Unqualified "/")
        [CompoundTerm (Unqualified flatName) [], IntTerm arity] ->
          pure (R.FunRefExpr (parseFlatName flatName) (fromInteger arity))
      -- Lambda 'fun(P1..Pn) -> body'. Params are patterns; invalid
      -- params get reported here and replaced with 'HeadWildcard' so
      -- traversal can keep going. An empty parameter list is rejected
      -- here ('EmptyLambdaParams', YCHR-16018) and replaced with a single
      -- wildcard, so the resulting 'R.LambdaExpr' satisfies the
      -- 'NonEmpty' invariant and downstream stages can continue.
      CompoundTerm
        (Unqualified "->")
        [CompoundTerm (Unqualified "fun") params, body] -> do
          body' <- traverse go (flattenTermComma body)
          case params of
            [] -> do
              tell [noDiag (P.AnnP EmptyLambdaParams loc origin)]
              pure (R.LambdaExpr (HeadWildcard :| []) body')
            p : ps -> do
              hargs <- traverse classifyParam (p :| ps)
              pure (R.LambdaExpr hargs body')
      -- 'quote(arg)' — quoting suppresses evaluation of the subtree;
      -- every compound inside is a data constructor.
      CompoundTerm (Unqualified "quote") [arg] ->
        pure (R.CtorExpr (Unqualified "quote") [quotedToExpr arg])
      -- 'host:f(args)' — host language call.
      CompoundTerm (Qualified "host" f) args ->
        R.HostExpr f <$> traverse go args
      -- Qualified compound: call if declared as a function visible to
      -- this module, else a data constructor application. Qualified
      -- references that survived the renamer are already
      -- visibility-validated, so the @elem@ check here is effectively
      -- a function-vs-constructor distinction.
      CompoundTerm name@(Qualified m b) args
        | QualifiedName m b
            `elem` Map.findWithDefault [] (UnqualifiedIdentifier b (length args)) vis ->
            R.CallExpr (QualifiedName m b) <$> traverse go args
        | otherwise ->
            R.CtorExpr name <$> traverse go args
      -- Unqualified compound. If exactly one declared function with
      -- this local name is visible to the current module, canonicalize
      -- to a 'CallExpr'; this is how nested function-call arguments
      -- of tell-side body constraints (and top-level goals) get
      -- evaluated, since the renamer's 'NoResolve' mode leaves
      -- body-compound children unqualified. Zero matches (the name
      -- is genuinely a data constructor or undefined) and ambiguous
      -- matches both fall through to 'CtorExpr'; the renamer is
      -- responsible for the corresponding diagnostics
      -- (@UnknownName@/@AmbiguousName@ in @ResolveAll@ positions,
      -- @UndeclaredDataConstructor@ in @NoResolve@).
      CompoundTerm name@(Unqualified n) args ->
        case Map.lookup (UnqualifiedIdentifier n (length args)) vis of
          Just [qn] -> R.CallExpr qn <$> traverse go args
          _ -> R.CtorExpr name <$> traverse go args

    classifyParam :: Term -> Writer [Diagnostic ResolveError] HeadArg
    classifyParam (VarTerm v) = pure (HeadVar v)
    classifyParam Wildcard = pure HeadWildcard
    classifyParam bad = do
      tell [noDiag (P.AnnP (LambdaParamError bad) loc origin)]
      pure HeadWildcard

-- | Translate a 'Term' that lives inside a @quote/1@ quotation. No
-- function-set lookup happens here: quoting suppresses evaluation, so
-- every compound is a data constructor.
quotedToExpr :: Term -> R.Expr
quotedToExpr (VarTerm v) = R.VarExpr v
quotedToExpr (IntTerm n) = R.IntExpr n
quotedToExpr (FloatTerm n) = R.FloatExpr n
quotedToExpr (TextTerm s) = R.TextExpr s
quotedToExpr Wildcard = R.WildcardExpr
quotedToExpr (CompoundTerm name args) =
  R.CtorExpr name (map quotedToExpr args)

-- | Recover a 'QualifiedName' from a flat @"module:name"@ atom emitted
-- by the renamer (see 'YCHR.Internal.Rename.renameTerm' for @fun name/arity@).
-- The renamer always emits a colon-separated form, so the missing-
-- separator case is an internal invariant violation rather than a
-- user-facing error.
parseFlatName :: Text -> QualifiedName
parseFlatName t = case T.breakOn ":" t of
  (m, rest) | not (T.null rest) -> QualifiedName m (T.drop 1 rest)
  _ ->
    error
      ( "YCHR.Internal.Resolve.parseFlatName: missing ':' separator in "
          <> T.unpack t
          <> " — renamer post-condition violated"
      )
