{-# LANGUAGE OverloadedStrings #-}

-- | Post-rename resolution.
--
-- Flattens @[P.Module]@ into a single 'R.Program', grouping function
-- equations under their declarations and verifying that declaration
-- kinds are used consistently. Replaces the former @YCHR.Validate@
-- pass with a transformation: the output is valid by construction.
module YCHR.Resolve
  ( ResolveError (..),
    resolveProgram,
  )
where

import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import YCHR.Diagnostic (Diagnostic, noDiag)
import YCHR.PExpr qualified as PExpr
import YCHR.Parsed qualified as P
import YCHR.Resolved qualified as R
import YCHR.Types
  ( BoundSig (..),
    Constraint (..),
    Name (..),
    QualifiedConstraint (..),
    QualifiedIdentifier (..),
    QualifiedName (..),
    TypeExpr (..),
    flattenName,
  )

data ResolveError
  = -- | A name declared as a constraint has function equations.
    ConstraintHasEquations Name
  | -- | A name declared as a function appears in a rule head.
    FunctionInRuleHead Name
  | -- | A name collides with a reserved built-in.
    ReservedName Name
  | -- | A constraint name reached the resolve phase without being
    -- module-qualified by the renamer. Indicates a renamer bug rather
    -- than user error.
    UnqualifiedConstraintName Name
  | -- | An @:- extend_function_type@ or @:- extend_function@ directive
    -- targets a function that was declared as closed (not @open_function@).
    ExtendsClosedFunction Name
  | -- | A free-floating function equation appears in a module that is
    -- not the declaring module of the function. Carries the qualified
    -- function name and the module in which the equation was found.
    OrphanFunctionEquation Name Text
  | -- | An @:- extend_function_type@ directive targets an open function
    -- that itself carries a @requiring@ clause. The instance set of a
    -- bounded open function is determined by its bounds, not by
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
  deriving (Eq, Show)

-- | Flatten modules into a single resolved program.
--
-- 1. Collect constraint and function declarations.
-- 2. Group equations under their function declarations.
-- 3. Check that no equation targets a constraint name.
-- 4. Check that no rule head references a function name.
resolveProgram :: [P.Module] -> Either [Diagnostic ResolveError] R.Program
resolveProgram mods =
  let constraintNames = buildConstraintNames mods
      functionNames = buildFunctionNames mods
      conTypes = collectConstraintTypes mods
      conBounds = collectConstraintBounds mods
      typeDefs = [td.node | m <- mods, td <- m.typeDecls]
      funcOpenness = buildFunctionOpenness mods
      funcRequiring = buildFunctionRequiring mods
      eqErrors = checkEquations constraintNames mods
      headErrors = checkRuleHeads (Set.map qualifiedNameToLooseName functionNames) mods
      reservedErrors = checkReservedNames mods
      orphanEqErrors = checkOrphanEquations functionNames mods
      extendsClosedErrors = checkExtendsClosed funcOpenness mods
      extendsBoundedErrors = checkExtendsBounded funcRequiring mods
      boundedDeclErrors = checkBoundedDeclarations functionNames mods
      (resolvedRules, ruleErrs) = resolveRules mods
      errs =
        eqErrors
          ++ headErrors
          ++ reservedErrors
          ++ orphanEqErrors
          ++ extendsClosedErrors
          ++ extendsBoundedErrors
          ++ boundedDeclErrors
          ++ ruleErrs
   in if null errs
        then
          Right
            R.Program
              { rules = resolvedRules,
                functions = resolveFunctions mods,
                constraintTypes = conTypes,
                constraintBounds = conBounds,
                functionNames = functionNames,
                typeDefinitions = typeDefs
              }
        else Left errs

qualifiedNameToLooseName :: QualifiedName -> Name
qualifiedNameToLooseName (QualifiedName m b) = Qualified m b

-- ---------------------------------------------------------------------------
-- Declaration collection
-- ---------------------------------------------------------------------------

buildConstraintNames :: [P.Module] -> Set QualifiedIdentifier
buildConstraintNames mods =
  Set.fromList
    [ QualifiedIdentifier m.name d.name d.arity
    | m <- mods,
      P.Ann d _ <- m.decls,
      P.ConstraintDecl {} <- [d]
    ]

buildFunctionNames :: [P.Module] -> Set QualifiedName
buildFunctionNames mods =
  Set.fromList
    [ QualifiedName m.name d.name
    | m <- mods,
      P.Ann d _ <- m.decls,
      P.FunctionDecl {} <- [d]
    ]

-- | Map each declared function to whether its declaration is open.
buildFunctionOpenness :: [P.Module] -> Map.Map QualifiedName Bool
buildFunctionOpenness mods =
  Map.fromList
    [ (QualifiedName m.name d.name, d.isOpen)
    | m <- mods,
      P.Ann d _ <- m.decls,
      P.FunctionDecl {} <- [d]
    ]

collectConstraintTypes :: [P.Module] -> Map.Map QualifiedName [TypeExpr]
collectConstraintTypes mods =
  Map.fromList
    [ (QualifiedName m.name d.name, ts)
    | m <- mods,
      P.Ann d _ <- m.decls,
      P.ConstraintDecl {} <- [d],
      let ts = case d.argTypes of
            Just types -> types
            Nothing -> replicate d.arity (TypeCon (Unqualified "any") [])
    ]

-- | Bounds declared on every @:- chr_constraint@ that carries a
-- @requiring@ clause. Unbounded constraints are absent from the map.
collectConstraintBounds :: [P.Module] -> Map.Map QualifiedName [BoundSig]
collectConstraintBounds mods =
  Map.fromList
    [ (QualifiedName m.name d.name, bs)
    | m <- mods,
      P.Ann d _ <- m.decls,
      P.ConstraintDecl {requiring = Just bs} <- [d]
    ]

-- | Bounds declared on every @:- function@ / @:- open_function@ that
-- carries a @requiring@ clause. Unbounded functions are absent.
buildFunctionRequiring :: [P.Module] -> Map.Map QualifiedName [BoundSig]
buildFunctionRequiring mods =
  Map.fromList
    [ (QualifiedName m.name d.name, bs)
    | m <- mods,
      P.Ann d _ <- m.decls,
      P.FunctionDecl {requiring = Just bs} <- [d]
    ]

-- ---------------------------------------------------------------------------
-- Validation (integrated into resolution)
-- ---------------------------------------------------------------------------

-- | Check that no equation targets a constraint-declared name.
-- Reports only the first equation per name.
checkEquations :: Set QualifiedIdentifier -> [P.Module] -> [Diagnostic ResolveError]
checkEquations cNames mods = snd $ foldl go (Set.empty, []) allEqs
  where
    allEqs = [annEq | m <- mods, annEq <- m.equations]
    go (seen, errs) annEq =
      case toQualId annEq.node.funName (length annEq.node.args) of
        Just qid
          | qid `Set.member` cNames,
            qid `Set.notMember` seen ->
              ( Set.insert qid seen,
                errs
                  ++ [ noDiag
                         ( P.AnnP
                             (ConstraintHasEquations annEq.node.funName)
                             annEq.sourceLoc
                             annEq.parsed
                         )
                     ]
              )
        _ -> (seen, errs)

-- | Check that no free-floating equation lives in a module that is not
-- the declaring module of the function. Equations contributed from
-- other modules must be wrapped in @:- extend_function ...@ directives.
-- Unknown function names are skipped here; they are reported by the
-- renamer as YCHR-20002.
checkOrphanEquations :: Set QualifiedName -> [P.Module] -> [Diagnostic ResolveError]
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

-- | Check that @:- extend_function_type@ and @:- extend_function@
-- directives only target open functions. Targets unknown to the
-- compiler are already reported by the renamer.
checkExtendsClosed ::
  Map.Map QualifiedName Bool -> [P.Module] -> [Diagnostic ResolveError]
checkExtendsClosed funcOpenness mods =
  let declErrs =
        [ noDiag
            (P.AnnP (ExtendsClosedFunction target) loc (PExpr.Atom d.name))
        | m <- mods,
          P.Ann d loc <- m.extensionTypes,
          Just target <- [d.target],
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
          annEq <- m.extensions,
          isKnownClosed funcOpenness annEq.node.funName
        ]
   in declErrs ++ eqnErrs
  where
    isKnownClosed openness (Qualified mn n) =
      case Map.lookup (QualifiedName mn n) openness of
        Just False -> True
        _ -> False
    isKnownClosed _ _ = False

-- | Reject @:- extend_function_type@ directives that target a bounded
-- open function. The instance set of a bounded open function is
-- determined by its bound-named functions, not by enumerated extensions.
-- @:- extend_function@ (equation extension) is /not/ rejected here —
-- new equations of a bounded open function are valid and are checked
-- under the same ambient bound as the original equations.
checkExtendsBounded ::
  Map.Map QualifiedName [BoundSig] -> [P.Module] -> [Diagnostic ResolveError]
checkExtendsBounded funcRequiring mods =
  [ noDiag
      (P.AnnP (ExtendTypeOnBoundedFunction target) loc (PExpr.Atom d.name))
  | m <- mods,
    P.Ann d loc <- m.extensionTypes,
    Just target <- [d.target],
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
  Set QualifiedName -> [P.Module] -> [Diagnostic ResolveError]
checkBoundedDeclarations functionNames mods =
  let funcBounds =
        [ (QualifiedName m.name d.name, primaryVars, bs, originForDecl m d)
        | m <- mods,
          P.Ann d _ <- m.decls,
          P.FunctionDecl {requiring = Just bs, argTypes, returnType} <- [d],
          let primaryVars =
                Set.fromList $
                  concatMap typeExprVars (maybe [] id argTypes)
                    ++ maybe [] typeExprVars returnType
        ]
      conBounds =
        [ (QualifiedName m.name d.name, primaryVars, bs, originForDecl m d)
        | m <- mods,
          P.Ann d _ <- m.decls,
          P.ConstraintDecl {requiring = Just bs, argTypes} <- [d],
          let primaryVars =
                Set.fromList (concatMap typeExprVars (maybe [] id argTypes))
        ]
      allBounded = funcBounds ++ conBounds
      varErrs =
        [ noDiag (P.AnnP (UnboundBoundVariable declText v) bs.loc origin)
        | (qn, primary, bsigs, origin) <- allBounded,
          let declText = qualifiedToLooseText qn,
          bs <- bsigs,
          let bsVars =
                Set.fromList
                  (concatMap typeExprVars bs.argTypes ++ typeExprVars bs.returnType),
          v <- Set.toList bsVars,
          Set.notMember v primary
        ]
      unknownErrs =
        [ noDiag
            ( P.AnnP
                (UnknownBoundFunction declText (flattenName bs.name) bs.arity)
                bs.loc
                origin
            )
        | (qn, _, bsigs, origin) <- allBounded,
          let declText = qualifiedToLooseText qn,
          bs <- bsigs,
          not (boundResolvesToFunction bs)
        ]
      cycleErrs = detectBoundCycles allBounded
   in varErrs ++ unknownErrs ++ cycleErrs
  where
    qualifiedToLooseText qn = flattenName (qualifiedNameToLooseName qn)
    boundResolvesToFunction bs = case bs.name of
      Qualified m n -> Set.member (QualifiedName m n) functionNames
      Unqualified _ ->
        -- The renamer should have qualified the name; if it did not,
        -- the renamer already reported YCHR-20002 for the unknown
        -- reference. We skip emitting our own bound-specific error
        -- in that case to avoid double-reporting.
        True
    originForDecl m d = PExpr.Atom (m.name <> ":" <> d.name)

-- | Detect cycles in the bound graph by depth-first search.
--
-- Vertices are the qualified names of bounded declarations. There is
-- an edge from @f@ to @g@ whenever @g@ appears in @f@'s @requiring@
-- clause (bounded names are always functions per the spec).
--
-- At most one diagnostic is emitted per simple cycle: subsequent
-- starting vertices that re-enter the same cycle hit it via the
-- 'visited' set and are skipped.
detectBoundCycles ::
  [(QualifiedName, Set Text, [BoundSig], PExpr.PExpr)] ->
  [Diagnostic ResolveError]
detectBoundCycles bounded =
  let graph :: Map.Map QualifiedName [QualifiedName]
      graph =
        Map.fromList
          [ ( qn,
              [ QualifiedName m n
              | b <- bs,
                Qualified m n <- [b.name]
              ]
            )
          | (qn, _, bs, _) <- bounded
          ]
      origins :: Map.Map QualifiedName PExpr.PExpr
      origins = Map.fromList [(qn, origin) | (qn, _, _, origin) <- bounded]
      (_, cycles) = foldl visit (Set.empty, []) (Map.keys graph)
      visit (visited, acc) qn = dfs graph visited [] acc qn
   in map (emitCycleDiag origins) cycles

-- | Iterative DFS from @qn@ that pushes any detected cycle onto the
-- accumulator and returns the updated @(visited, cycles)@ pair. A
-- vertex is added to @visited@ only after its entire subtree has been
-- explored, ensuring each simple cycle is reported exactly once.
dfs ::
  Map.Map QualifiedName [QualifiedName] ->
  Set QualifiedName ->
  [QualifiedName] ->
  [[QualifiedName]] ->
  QualifiedName ->
  (Set QualifiedName, [[QualifiedName]])
dfs graph visited path acc qn
  | qn `elem` path =
      let cycle_ = reverse (qn : takeWhile (/= qn) path) ++ [qn]
       in (visited, cycle_ : acc)
  | qn `Set.member` visited = (visited, acc)
  | otherwise =
      let neighbors = Map.findWithDefault [] qn graph
          (visited', acc') =
            foldl
              (\(v, a) target -> dfs graph v (qn : path) a target)
              (visited, acc)
              neighbors
       in (Set.insert qn visited', acc')

emitCycleDiag ::
  Map.Map QualifiedName PExpr.PExpr ->
  [QualifiedName] ->
  Diagnostic ResolveError
emitCycleDiag origins cycle_ =
  let names = map (flattenName . qualifiedNameToLooseName) cycle_
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
checkRuleHeads :: Set Name -> [P.Module] -> [Diagnostic ResolveError]
checkRuleHeads fNames mods = snd $ foldl go (Set.empty, []) allRules
  where
    allRules = [(r, m) | m <- mods, r <- m.rules]
    go (seen, errs) (r, _m) =
      let cs = headConstraints r.head.node
          new =
            [ ( c.name,
                noDiag (P.AnnP (FunctionInRuleHead c.name) r.head.sourceLoc r.head.parsed)
              )
            | c <- cs,
              c.name `Set.member` fNames,
              c.name `Set.notMember` seen
            ]
       in (foldl (\s (n, _) -> Set.insert n s) seen new, errs ++ map snd new)

-- | Reserved names that cannot be used as constraint or function declarations.
reservedDeclNames :: Set Text
reservedDeclNames = Set.fromList ["term"]

-- | Check that no declaration uses a reserved name.
checkReservedNames :: [P.Module] -> [Diagnostic ResolveError]
checkReservedNames mods =
  [ noDiag (P.AnnP (ReservedName (Qualified m.name d.name)) loc (PExpr.Atom ""))
  | m <- mods,
    P.Ann d loc <- m.decls,
    isDeclNamed d,
    d.name `Set.member` reservedDeclNames
  ]
  where
    isDeclNamed P.ConstraintDecl {} = True
    isDeclNamed P.FunctionDecl {} = True
    isDeclNamed _ = False

headConstraints :: P.Head -> [P.Constraint]
headConstraints (P.Simplification cs) = cs
headConstraints (P.Propagation cs) = cs
headConstraints (P.Simpagation ks rs) = ks ++ rs

toQualId :: Name -> Int -> Maybe QualifiedIdentifier
toQualId (Qualified m n) a = Just (QualifiedIdentifier m n a)
toQualId (Unqualified _) _ = Nothing

-- ---------------------------------------------------------------------------
-- Module flattening
-- ---------------------------------------------------------------------------

resolveRules :: [P.Module] -> ([R.Rule], [Diagnostic ResolveError])
resolveRules mods =
  let raws = [(r, m) | m <- mods, r <- m.rules]
      go (acc, errs) (r, _m) =
        case resolveHead r.head.sourceLoc r.head.parsed r.head.node of
          Right rh ->
            ( acc
                ++ [ R.Rule
                       { name = r.name,
                         head = P.AnnP rh r.head.sourceLoc r.head.parsed,
                         guard = r.guard,
                         body = r.body
                       }
                   ],
              errs
            )
          Left newErrs -> (acc, errs ++ newErrs)
   in foldl go ([], []) raws

resolveHead ::
  P.SourceLoc ->
  PExpr.PExpr ->
  P.Head ->
  Either [Diagnostic ResolveError] R.Head
resolveHead loc origin h = case h of
  P.Simplification cs -> R.Simplification <$> traverse (qualifyConstraint loc origin) cs
  P.Propagation cs -> R.Propagation <$> traverse (qualifyConstraint loc origin) cs
  P.Simpagation ks rs ->
    R.Simpagation
      <$> traverse (qualifyConstraint loc origin) ks
      <*> traverse (qualifyConstraint loc origin) rs

qualifyConstraint ::
  P.SourceLoc ->
  PExpr.PExpr ->
  Constraint ->
  Either [Diagnostic ResolveError] QualifiedConstraint
qualifyConstraint loc origin (Constraint n args) = case n of
  Qualified m b -> Right (QualifiedConstraint (QualifiedName m b) args)
  Unqualified _ ->
    Left [noDiag (P.AnnP (UnqualifiedConstraintName n) loc origin)]

resolveFunctions :: [P.Module] -> [R.FunctionDef]
resolveFunctions mods =
  let -- Collect all function declarations with their module context
      allDecls =
        [ (QualifiedName m.name d.name, d.arity, d, m)
        | m <- mods,
          P.Ann d _ <- m.decls,
          P.FunctionDecl {} <- [d]
        ]
      -- Group by (qualifiedName, arity)
      grouped =
        Map.toList $
          Map.fromListWith
            (++)
            [ ((qn, ar), [(d, m)])
            | (qn, ar, d, m) <- allDecls
            ]
   in [ R.FunctionDef
          { name = qn,
            arity = ar,
            signatures =
              collectSignatures decls
                ++ collectExtensionSignatures mods qn ar,
            isOpen = any (\(d, _) -> d.isOpen) decls,
            requiring = concatMap (\(d, _) -> maybe [] id d.requiring) decls,
            equations = concatMap (\(d, m) -> gatherEquations mods m d) decls
          }
      | ((qn, ar), decls) <- grouped
      ]

-- | Collect type signatures from a group of declarations for the same function.
collectSignatures :: [(P.Declaration, P.Module)] -> [([TypeExpr], TypeExpr)]
collectSignatures decls =
  [ (argTys, retTy)
  | (d, _) <- decls,
    Just argTys <- [d.argTypes],
    Just retTy <- [d.returnType]
  ]

-- | Collect signatures contributed by @:- extend_function_type@
-- directives in any module. Only signatures whose resolved target
-- matches the given qualified name and arity are included.
collectExtensionSignatures ::
  [P.Module] -> QualifiedName -> Int -> [([TypeExpr], TypeExpr)]
collectExtensionSignatures mods qn ar =
  [ (argTys, retTy)
  | m <- mods,
    P.Ann d _ <- m.extensionTypes,
    d.arity == ar,
    Just (Qualified tm tn) <- [d.target],
    QualifiedName tm tn == qn,
    Just argTys <- [d.argTypes],
    Just retTy <- [d.returnType]
  ]

-- | Gather equations for a function declaration, stripping the funName.
-- Free-floating equations only come from the declaring module
-- (orphans are rejected by 'checkOrphanEquations'). Extension equations
-- contributed via @:- extend_function@ are pulled from every module's
-- @extensions@ list.
gatherEquations :: [P.Module] -> P.Module -> P.Declaration -> [P.AnnP R.FunctionEquation]
gatherEquations mods m d =
  let qualName = Qualified m.name d.name
      primaryEqs =
        [ annEq
        | annEq <- m.equations,
          annEq.node.funName == qualName,
          length annEq.node.args == d.arity
        ]
      extensionEqs =
        [ annEq
        | mod_ <- mods,
          annEq <- mod_.extensions,
          annEq.node.funName == qualName,
          length annEq.node.args == d.arity
        ]
   in map stripFunName (primaryEqs ++ extensionEqs)

stripFunName :: P.AnnP P.FunctionEquation -> P.AnnP R.FunctionEquation
stripFunName (P.AnnP eq loc parsed) =
  P.AnnP
    R.FunctionEquation
      { args = eq.args,
        guard = eq.guard,
        rhs = eq.rhs
      }
    loc
    parsed
