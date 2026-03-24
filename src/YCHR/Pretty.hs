-- | Pretty-printing utilities for CHR terms and binding maps.
module YCHR.Pretty
  ( prettyTerm,
    prettyBindings,
  )
where

import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import YCHR.Types (Name (..), Term (..))

-- | Render a 'Term' as a Prolog-compatible string.
-- Unbound variables ('VarTerm' and 'Wildcard') are shown as @_@.
prettyTerm :: Term -> String
prettyTerm (IntTerm n) = show n
prettyTerm (AtomTerm s) = s
prettyTerm (VarTerm _) = "_"
prettyTerm Wildcard = "_"
prettyTerm (CompoundTerm (Unqualified f) ts) =
  f ++ "(" ++ intercalate ", " (map prettyTerm ts) ++ ")"
prettyTerm (CompoundTerm (Qualified m f) ts) =
  m ++ ":" ++ f ++ "(" ++ intercalate ", " (map prettyTerm ts) ++ ")"

-- | Serialize a variable binding map to the golden file format.
--
-- Keys are sorted alphabetically for determinism. Each line has the form
-- @K = V@ followed by a newline, matching the output of 'unlines'.
prettyBindings :: Map String Term -> String
prettyBindings m =
  unlines [k ++ " = " ++ prettyTerm v | (k, v) <- Map.toAscList m]
