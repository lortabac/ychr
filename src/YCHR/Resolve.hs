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
import YCHR.Types (Name (..), QualifiedIdentifier (..), TypeExpr)

data ResolveError
  = -- | A name declared as a constraint has function equations.
    ConstraintHasEquations Name
  | -- | A name declared as a function appears in a rule head.
    FunctionInRuleHead Name
  | -- | A name collides with a reserved built-in.
    ReservedName Name
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
      typeDefs = [td.node | m <- mods, td <- m.typeDecls]
      eqErrors = checkEquations constraintNames mods
      headErrors = checkRuleHeads functionNames mods
      reservedErrors = checkReservedNames mods
      errs = eqErrors ++ headErrors ++ reservedErrors
   in if null errs
        then
          Right
            R.Program
              { rules = resolveRules mods,
                functions = resolveFunctions mods,
                constraintTypes = conTypes,
                functionNames = functionNames,
                typeDefinitions = typeDefs
              }
        else Left errs

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

buildFunctionNames :: [P.Module] -> Set Name
buildFunctionNames mods =
  Set.fromList
    [ Qualified m.name d.name
    | m <- mods,
      P.Ann d _ <- m.decls,
      P.FunctionDecl {} <- [d]
    ]

collectConstraintTypes :: [P.Module] -> Map.Map Name [TypeExpr]
collectConstraintTypes mods =
  Map.fromList
    [ (Qualified m.name d.name, ts)
    | m <- mods,
      P.Ann d _ <- m.decls,
      P.ConstraintDecl {} <- [d],
      Just ts <- [d.argTypes]
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
                  ++ [noDiag (P.AnnP (ConstraintHasEquations annEq.node.funName) annEq.sourceLoc annEq.parsed)]
              )
        _ -> (seen, errs)

-- | Check that no rule head constraint is a function-declared name.
-- Reports only the first rule per name.
checkRuleHeads :: Set Name -> [P.Module] -> [Diagnostic ResolveError]
checkRuleHeads fNames mods = snd $ foldl go (Set.empty, []) allRules
  where
    allRules = [(r, m) | m <- mods, r <- m.rules]
    go (seen, errs) (r, _m) =
      let cs = headConstraints r.head.node
          new =
            [ (c.name, noDiag (P.AnnP (FunctionInRuleHead c.name) r.head.sourceLoc r.head.parsed))
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

resolveRules :: [P.Module] -> [R.Rule]
resolveRules mods =
  [ R.Rule
      { name = r.name,
        head = r.head,
        guard = r.guard,
        body = r.body
      }
  | m <- mods,
    r <- m.rules
  ]

resolveFunctions :: [P.Module] -> [R.FunctionDef]
resolveFunctions mods =
  [ R.FunctionDef
      { name = Qualified m.name d.name,
        arity = d.arity,
        argTypes = d.argTypes,
        returnType = d.returnType,
        isOpen = d.isOpen,
        equations = gatherEquations mods m d
      }
  | m <- mods,
    P.Ann d _ <- m.decls,
    P.FunctionDecl {} <- [d]
  ]

-- | Gather equations for a function declaration, stripping the funName.
-- Open functions collect equations from all modules; closed functions
-- only from the declaring module.
gatherEquations :: [P.Module] -> P.Module -> P.Declaration -> [P.AnnP R.FunctionEquation]
gatherEquations mods m d =
  let qualName = Qualified m.name d.name
      matchingEqs
        | d.isOpen =
            [annEq | mod_ <- mods, annEq <- mod_.equations, annEq.node.funName == qualName, length annEq.node.args == d.arity]
        | otherwise =
            [annEq | annEq <- m.equations, annEq.node.funName == qualName, length annEq.node.args == d.arity]
   in map stripFunName matchingEqs

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
