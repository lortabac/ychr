-- | Pretty-printing utilities for CHR terms and binding maps.
module YCHR.Pretty
  ( prettyTerm,
    prettyBindings,
    prettyQueryResult,
    prettyTermSrc,
    prettyConstraintSrc,
  )
where

import Data.Char (isAlphaNum, isLower)
import Data.List (intercalate, isPrefixOf)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import YCHR.Types (Constraint (..), Name (..), Term (..))

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

-- ---------------------------------------------------------------------------
-- Surface pretty-printer (for roundtrip: parse . prettyTermSrc = id)
-- ---------------------------------------------------------------------------

reservedWordsSrc :: [String]
reservedWordsSrc = ["is", "div", "mod"]

-- | True if the atom string requires single-quote wrapping.
needsQuoting :: String -> Bool
needsQuoting [] = True
needsQuoting (c : cs) =
  not
    ( isLower c
        && all (\x -> isAlphaNum x || x == '_') cs
        && (c : cs) `notElem` reservedWordsSrc
    )

-- | Render an atom, quoting with @\'...\'@ if necessary.
-- Embedded single quotes are doubled per ISO Prolog convention.
renderAtom :: String -> String
renderAtom s
  | needsQuoting s = "'" ++ concatMap esc s ++ "'"
  | otherwise = s
  where
    esc '\'' = "''"
    esc c = [c]

infixOpsSrc :: [String]
infixOpsSrc = ["*", "div", "mod", "+", "-", ":=", "is", "=", "==", "<", ">", "=<", ">="]

-- | Render a 'Term' as valid surface-language source text.
-- Unlike 'prettyTerm', variable names are preserved rather than collapsed to @_@.
prettyTermSrc :: Term -> String
prettyTermSrc (IntTerm n) = show n
prettyTermSrc (AtomTerm s) = renderAtom s
prettyTermSrc (VarTerm v) = v
prettyTermSrc Wildcard = "_"
prettyTermSrc (CompoundTerm (Unqualified op) [l, r])
  | op `elem` infixOpsSrc =
      "(" ++ prettyTermSrc l ++ " " ++ op ++ " " ++ prettyTermSrc r ++ ")"
prettyTermSrc (CompoundTerm (Unqualified f) ts) =
  renderAtom f ++ "(" ++ intercalate ", " (map prettyTermSrc ts) ++ ")"
prettyTermSrc (CompoundTerm (Qualified m f) ts) =
  renderAtom m
    ++ ":"
    ++ renderAtom f
    ++ "("
    ++ intercalate ", " (map prettyTermSrc ts)
    ++ ")"

-- | Render a 'Constraint' as valid surface-language source text.
prettyConstraintSrc :: Constraint -> String
prettyConstraintSrc (Constraint (Unqualified name) []) = renderAtom name
prettyConstraintSrc (Constraint (Unqualified name) args) =
  renderAtom name ++ "(" ++ intercalate ", " (map prettyTermSrc args) ++ ")"
prettyConstraintSrc (Constraint (Qualified m name) args) =
  renderAtom m
    ++ ":"
    ++ renderAtom name
    ++ case args of
      [] -> ""
      _ -> "(" ++ intercalate ", " (map prettyTermSrc args) ++ ")"

-- ---------------------------------------------------------------------------
-- User-facing output (binding map)
-- ---------------------------------------------------------------------------

-- | Serialize a variable binding map to the golden file format.
--
-- Keys are sorted alphabetically for determinism. Each line has the form
-- @K = V@ followed by a newline, matching the output of 'unlines'.
prettyBindings :: Map String Term -> String
prettyBindings m =
  unlines [k ++ " = " ++ prettyTerm v | (k, v) <- Map.toAscList m]

-- | Render a variable binding map as a Prolog-style query result.
--
-- Variables starting with @_@ are filtered out (internal/wildcard).
-- If no user-visible bindings remain, returns @true.@.
-- Otherwise, comma-separated @K = V@ lines terminated with a dot.
prettyQueryResult :: Map String Term -> String
prettyQueryResult m =
  let visible = [(k, v) | (k, v) <- Map.toAscList m, not ("_" `isPrefixOf` k)]
   in case visible of
        [] -> "true.\n"
        _ -> formatBindings visible
  where
    formatBindings [] = ""
    formatBindings [(k, v)] = k ++ " = " ++ prettyTerm v ++ ".\n"
    formatBindings ((k, v) : rest) =
      k ++ " = " ++ prettyTerm v ++ ",\n" ++ formatBindings rest
