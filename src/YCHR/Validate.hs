{-# LANGUAGE OverloadedStrings #-}

-- | Post-rename validation.
--
-- Checks that declaration kinds are used consistently: constraint-declared
-- names must not have function equations, and function-declared names must
-- not appear in rule heads. Runs after renaming (names are qualified) and
-- before desugaring.
module YCHR.Validate
  ( ValidationError (..),
    ConstraintDecls (..),
    FunctionDecls (..),
    validateDeclKinds,
  )
where

import Data.Set (Set)
import Data.Set qualified as Set
import YCHR.Diagnostic (Diagnostic, noDiag)
import YCHR.Parsed
import YCHR.Types (QualifiedIdentifier (..))

-- | Set of names declared as constraints.
newtype ConstraintDecls = ConstraintDecls (Set QualifiedIdentifier)

-- | Set of names declared as functions.
newtype FunctionDecls = FunctionDecls (Set QualifiedIdentifier)

data ValidationError
  = -- | A name declared as a constraint has function equations.
    ConstraintHasEquations Name
  | -- | A name declared as a function appears in a rule head.
    FunctionInRuleHead Name
  deriving (Eq, Show)

-- | Validate that declaration kinds match their usage across all modules.
-- Returns one diagnostic per mismatched name (first occurrence only).
validateDeclKinds :: [Module] -> [Diagnostic ValidationError]
validateDeclKinds mods =
  let ConstraintDecls cDecls = buildConstraintDecls mods
      FunctionDecls fDecls = buildFunctionDecls mods
   in checkEquations cDecls mods ++ checkRuleHeads fDecls mods

buildConstraintDecls :: [Module] -> ConstraintDecls
buildConstraintDecls mods =
  ConstraintDecls . Set.fromList $
    [ QualifiedIdentifier m.name d.name d.arity
    | m <- mods,
      Ann d _ <- m.decls,
      ConstraintDecl {} <- [d]
    ]

buildFunctionDecls :: [Module] -> FunctionDecls
buildFunctionDecls mods =
  FunctionDecls . Set.fromList $
    [ QualifiedIdentifier m.name d.name d.arity
    | m <- mods,
      Ann d _ <- m.decls,
      FunctionDecl {} <- [d]
    ]

-- | Check that no equation targets a constraint-declared name.
-- Reports only the first equation per name.
checkEquations :: Set QualifiedIdentifier -> [Module] -> [Diagnostic ValidationError]
checkEquations cDecls mods = snd $ foldl go (Set.empty, []) allEqs
  where
    allEqs = [annEq | m <- mods, annEq <- m.equations]
    go (seen, errs) annEq =
      case toQualId annEq.node.funName (length annEq.node.args) of
        Just qid
          | qid `Set.member` cDecls,
            qid `Set.notMember` seen ->
              (Set.insert qid seen, errs ++ [noDiag (AnnP (ConstraintHasEquations annEq.node.funName) annEq.sourceLoc annEq.parsed)])
        _ -> (seen, errs)

-- | Check that no rule head constraint is a function-declared name.
-- Reports only the first rule per name.
checkRuleHeads :: Set QualifiedIdentifier -> [Module] -> [Diagnostic ValidationError]
checkRuleHeads fDecls mods = snd $ foldl go (Set.empty, []) allRules
  where
    allRules = [(r, m) | m <- mods, r <- m.rules]
    go (seen, errs) (r, _m) =
      let cs = headConstraints r.head.node
          new =
            [ (qid, noDiag (AnnP (FunctionInRuleHead c.name) r.head.sourceLoc r.head.parsed))
            | c <- cs,
              Just qid <- [toQualId c.name (length c.args)],
              qid `Set.member` fDecls,
              qid `Set.notMember` seen
            ]
       in (foldl (\s (qid, _) -> Set.insert qid s) seen new, errs ++ map snd new)

headConstraints :: Head -> [Constraint]
headConstraints (Simplification cs) = cs
headConstraints (Propagation cs) = cs
headConstraints (Simpagation ks rs) = ks ++ rs

toQualId :: Name -> Int -> Maybe QualifiedIdentifier
toQualId (Qualified m n) a = Just (QualifiedIdentifier m n a)
toQualId (Unqualified _) _ = Nothing
