{-# LANGUAGE OverloadedStrings #-}

-- | Exhaustiveness checking for user-defined functions.
--
-- Warns when a function's pattern-matching equations cannot match some
-- value of a declared algebraic type. The check is type-directed and
-- deliberately narrow:
--
--   * Only /functions/ are checked, never rules.
--
--   * Only positions whose declared type is a declared /algebraic/ type
--     (@:- chr_type t ---> c1 ; c2 ; …@) contribute. Positions of
--     @int@\/@float@\/@string@\/opaque\/type-variable\/@any@\/unknown
--     type can't be enumerated, so they are treated as always covered
--     and are never the source of a warning.
--
--   * Only /closed/, /single-signature/ functions are checked. Open
--     functions/classes may gain equations in modules outside the
--     compilation unit (so a local gap might be filled elsewhere), and
--     multi-signature classes have ambiguous column types.
--
--   * An equation carrying a user guard does not count as covering its
--     pattern: the guard may fail at runtime, so the pattern is not
--     guaranteed handled.
--
-- The core is Maranget's matrix/usefulness algorithm
-- (<http://moscova.inria.fr/~maranget/papers/warn/index.html>),
-- restricted so that only algebraic columns have an enumerable
-- constructor signature. It handles multi-argument functions and
-- nested constructor patterns uniformly, and produces a witness — an
-- example unmatched call — for the warning message.
module YCHR.Exhaustiveness
  ( ExhaustivenessWarning (..),
    checkExhaustiveness,
  )
where

import Data.List (find)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Constructors (ConEnv, buildConEnv, canonicalizeCon, lookupCon)
import YCHR.Diagnostic (Diagnostic (..))
import YCHR.Parsed (AnnP (..))
import YCHR.Resolved qualified as R
import YCHR.Types
  ( DataConstructor (..),
    Name,
    Term (..),
    TypeDefinition (..),
    TypeExpr (..),
    TypeKind (..),
    flattenName,
    qualifiedToName,
  )

-- | A non-exhaustive function definition. Carries the function's
-- display name (e.g. @"M:f/2"@) and a witness call (e.g. @f(_, blue)@)
-- that no equation matches.
data ExhaustivenessWarning
  = NonExhaustiveMatch Text Term
  deriving (Eq, Show)

-- | A pattern reduced to what matters for exhaustiveness. Variables,
-- wildcards, and every position of a non-algebraic type collapse to
-- 'PWild'; only constructors of a declared algebraic type survive as
-- 'PCon'.
data Pat
  = PWild
  | PCon Name [Pat]
  deriving (Eq, Show)

-- | The type of a matrix column: an algebraic type with its full
-- constructor set, or anything non-enumerable.
data ColType
  = AlgCol [DataConstructor]
  | OtherCol

-- ---------------------------------------------------------------------------
-- Entry point
-- ---------------------------------------------------------------------------

-- | Check every function in a resolved program for exhaustiveness.
checkExhaustiveness :: R.Program -> [Diagnostic ExhaustivenessWarning]
checkExhaustiveness prog =
  let conEnv = buildConEnv prog.typeDefinitions
      typeMap = Map.fromList [(td.name, td) | td <- prog.typeDefinitions]
   in concatMap (checkFunction conEnv typeMap) prog.functions

-- | Check a single function definition. Returns at most one warning.
-- Skips open functions, untyped or multi-signature functions, and
-- functions with no equations.
checkFunction ::
  ConEnv ->
  Map Name TypeDefinition ->
  R.FunctionDef ->
  [Diagnostic ExhaustivenessWarning]
checkFunction conEnv typeMap fd
  | fd.isOpen = []
  | [sig] <- fd.signatures,
    AnnP _ loc origin : _ <- fd.equations =
      let (argTys, _) = sig
          classify = colTypeOf conEnv typeMap
          colTypes = map classify argTys
          -- Only equations without a user guard count as covering.
          matrix =
            [ zipWith (termToPat conEnv typeMap) colTypes eq.args
            | AnnP eq _ _ <- fd.equations,
              null eq.guard.node
            ]
       in case findMissing classify colTypes matrix of
            -- Only warn when the witness commits to a concrete constructor:
            -- a 'PCon' can only come from an uncovered /algebraic/ column,
            -- so its presence is what makes the gap attributable to a
            -- declared algebraic type. An all-wildcard witness means the
            -- non-exhaustiveness stems entirely from non-enumerable columns
            -- (e.g. an @int@ argument with no catch-all, or a function whose
            -- every equation is guarded), which we deliberately do not flag.
            Just witness
              | any hasCon witness ->
                  let warning = NonExhaustiveMatch displayName (witnessCall fd witness)
                   in [Diagnostic (Just label) (AnnP warning loc origin)]
            _ -> []
  | otherwise = []
  where
    displayName = flattenName (qualifiedToName fd.name) <> "/" <> T.pack (show fd.arity)
    label = "function " <> displayName

-- | Build the witness call term @f(w1, …, wn)@ from a witness pattern
-- vector. The functor is the function's unqualified base name so the
-- rendering reads like a source call.
witnessCall :: R.FunctionDef -> [Pat] -> Term
witnessCall fd witness =
  CompoundTerm (qualifiedToName fd.name) (map patToTerm witness)

patToTerm :: Pat -> Term
patToTerm PWild = Wildcard
patToTerm (PCon name sub) = CompoundTerm name (map patToTerm sub)

-- | Whether a witness pattern contains a constructor anywhere. A 'PCon'
-- only ever originates from an uncovered algebraic column, so this is
-- the test for "this gap is attributable to a declared algebraic type".
hasCon :: Pat -> Bool
hasCon PWild = False
hasCon (PCon _ _) = True

-- ---------------------------------------------------------------------------
-- Type-directed pattern reduction
-- ---------------------------------------------------------------------------

-- | Classify a declared type expression. Only a 'TypeCon' naming a
-- declared algebraic type is enumerable; everything else (type
-- variables, built-in @int@\/@float@\/@string@, opaque types, unknown
-- names) is 'OtherCol'.
colTypeOf :: ConEnv -> Map Name TypeDefinition -> TypeExpr -> ColType
colTypeOf _ typeMap (TypeCon name _) =
  case Map.lookup name typeMap of
    Just td -> case td.kind of
      Algebraic cs -> AlgCol cs
      Opaque -> OtherCol
    Nothing -> OtherCol
colTypeOf _ _ (TypeVar _) = OtherCol

-- | Reduce a pattern term against the declared type of its position.
-- Constructors of the position's algebraic type survive (recursing into
-- their fields with the field types); everything else collapses to
-- 'PWild'. A constructor that does not belong to the expected type
-- (only possible in a type-incorrect program, diagnosed elsewhere) is
-- treated conservatively as 'PWild' so it cannot manufacture a spurious
-- warning.
termToPat :: ConEnv -> Map Name TypeDefinition -> ColType -> Term -> Pat
termToPat _ _ OtherCol _ = PWild
termToPat conEnv typeMap (AlgCol cs) term = case term of
  CompoundTerm name sub ->
    let canonical = canonicalizeCon conEnv name
     in case lookupCon conEnv canonical of
          Just (_, dc)
            -- The constructor must belong to this position's type and be
            -- applied at its declared arity; otherwise the program is
            -- type-incorrect (diagnosed elsewhere) and we stay
            -- conservative with a wildcard.
            | dc.conName `elem` [c.conName | c <- cs],
              length sub == length dc.conArgs ->
                PCon dc.conName (zipWith subPat dc.conArgs sub)
          _ -> PWild
  _ -> PWild
  where
    subPat ty = termToPat conEnv typeMap (colTypeOf conEnv typeMap ty)

-- ---------------------------------------------------------------------------
-- Maranget usefulness / missing-pattern search
-- ---------------------------------------------------------------------------

-- | Search for a witness vector that no row of the matrix matches, given
-- the column types. 'Nothing' means the matrix is exhaustive. The
-- @classify@ argument turns a constructor's field types into column
-- types when specializing, so nested patterns are checked with the same
-- type-directed restriction as the top level.
--
-- This is the usefulness of the all-wildcard vector against the matrix,
-- specialized to return a concrete witness. The three cases follow
-- Maranget: no columns left, an algebraic column with a complete
-- constructor signature, and an incomplete/non-enumerable column.
findMissing :: (TypeExpr -> ColType) -> [ColType] -> [[Pat]] -> Maybe [Pat]
findMissing _ [] matrix
  | null matrix = Just [] -- nothing matches the empty value vector
  | otherwise = Nothing -- some row matches it
findMissing classify (t : ts) matrix =
  let present = Set.fromList [c | (PCon c _ : _) <- matrix]
   in case completeSignature t present of
        Just ctors ->
          -- Complete signature: a witness must commit to one constructor.
          listToMaybe (mapMaybe (specializeWitness classify ts matrix) ctors)
        Nothing ->
          -- Incomplete (or non-enumerable): defaulting suffices, and the
          -- witness fills this column with a missing constructor (or a
          -- wildcard when the type is non-enumerable).
          (missingHead t present :) <$> findMissing classify ts (defaultMatrix matrix)

-- | When the column type is algebraic and every one of its constructors
-- appears at the head of the column, return that constructor set;
-- otherwise 'Nothing' (incomplete, or non-enumerable).
completeSignature :: ColType -> Set Name -> Maybe [DataConstructor]
completeSignature OtherCol _ = Nothing
completeSignature (AlgCol ctors) present
  | all (\dc -> dc.conName `Set.member` present) ctors = Just ctors
  | otherwise = Nothing

-- | Recurse into one constructor of a complete signature, rebuilding the
-- witness head if the specialized matrix is non-exhaustive. The
-- constructor's field types become the new leading columns, classified
-- through @classify@ so nested algebraic fields are themselves checked.
specializeWitness ::
  (TypeExpr -> ColType) -> [ColType] -> [[Pat]] -> DataConstructor -> Maybe [Pat]
specializeWitness classify ts matrix dc =
  let argTypes = map classify dc.conArgs
      n = length dc.conArgs
   in case findMissing classify (argTypes ++ ts) (specialize dc matrix) of
        Nothing -> Nothing
        Just w -> Just (PCon dc.conName (take n w) : drop n w)

-- | The witness pattern for an incomplete column: a constructor not
-- present (applied to wildcards) for an algebraic type, or a wildcard
-- for a non-enumerable type.
missingHead :: ColType -> Set Name -> Pat
missingHead OtherCol _ = PWild
missingHead (AlgCol ctors) present =
  case find (\dc -> not (dc.conName `Set.member` present)) ctors of
    Just dc -> PCon dc.conName (replicate (length dc.conArgs) PWild)
    Nothing -> PWild -- unreachable: incomplete implies a missing ctor

-- | Specialize the matrix on a constructor: rows headed by that
-- constructor expose its sub-patterns; rows headed by a wildcard
-- contribute wildcards for its fields; other constructor rows are
-- dropped.
specialize :: DataConstructor -> [[Pat]] -> [[Pat]]
specialize dc = mapMaybe row
  where
    n = length dc.conArgs
    row (PCon c args : rest)
      | c == dc.conName = Just (args ++ rest)
      | otherwise = Nothing
    row (PWild : rest) = Just (replicate n PWild ++ rest)
    row [] = Nothing

-- | The default matrix: rows headed by a wildcard, with that head
-- dropped. Constructor-headed rows are dropped.
defaultMatrix :: [[Pat]] -> [[Pat]]
defaultMatrix = mapMaybe row
  where
    row (PWild : rest) = Just rest
    row (PCon _ _ : _) = Nothing
    row [] = Nothing
