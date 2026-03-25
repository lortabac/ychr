{-# LANGUAGE OverloadedStrings #-}

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
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Types (Constraint (..), Name (..), Term (..))

-- | Render a 'Term' as a Prolog-compatible string.
-- Unbound variables ('VarTerm' and 'Wildcard') are shown as @_@.
prettyTerm :: Term -> String
prettyTerm (IntTerm n) = show n
prettyTerm (AtomTerm s) = T.unpack s
prettyTerm (VarTerm _) = "_"
prettyTerm Wildcard = "_"
prettyTerm (CompoundTerm (Unqualified f) ts) =
  T.unpack f ++ "(" ++ intercalate ", " (map prettyTerm ts) ++ ")"
prettyTerm (CompoundTerm (Qualified m f) ts) =
  T.unpack m ++ ":" ++ T.unpack f ++ "(" ++ intercalate ", " (map prettyTerm ts) ++ ")"

-- ---------------------------------------------------------------------------
-- Surface pretty-printer (for roundtrip: parse . prettyTermSrc = id)
-- ---------------------------------------------------------------------------

reservedWordsSrc :: [Text]
reservedWordsSrc = ["is", "div", "mod"]

-- | True if the atom string requires single-quote wrapping.
needsQuoting :: Text -> Bool
needsQuoting t = case T.uncons t of
  Nothing -> True
  Just (c, cs) ->
    not
      ( isLower c
          && T.all (\x -> isAlphaNum x || x == '_') cs
          && t `notElem` reservedWordsSrc
      )

-- | Render an atom, quoting with @\'...\'@ if necessary.
-- Embedded single quotes are doubled per ISO Prolog convention.
renderAtom :: Text -> String
renderAtom s
  | needsQuoting s = "'" ++ concatMap esc (T.unpack s) ++ "'"
  | otherwise = T.unpack s
  where
    esc '\'' = "''"
    esc c = [c]

infixOpsSrc :: [Text]
infixOpsSrc = ["*", "div", "mod", "+", "-", ":=", "is", "=", "==", "<", ">", "=<", ">="]

-- | Render a 'Term' as valid surface-language source text.
-- Unlike 'prettyTerm', variable names are preserved rather than collapsed to @_@.
prettyTermSrc :: Term -> String
prettyTermSrc (IntTerm n) = show n
prettyTermSrc (AtomTerm s) = renderAtom s
prettyTermSrc (VarTerm v) = T.unpack v
prettyTermSrc Wildcard = "_"
prettyTermSrc (CompoundTerm (Unqualified op) [l, r])
  | op `elem` infixOpsSrc =
      "(" ++ prettyTermSrc l ++ " " ++ T.unpack op ++ " " ++ prettyTermSrc r ++ ")"
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
prettyBindings :: Map Text Term -> String
prettyBindings m =
  unlines [T.unpack k ++ " = " ++ prettyTerm v | (k, v) <- Map.toAscList m]

-- | Render a variable binding map as a Prolog-style query result.
--
-- Variables starting with @_@ are filtered out (internal/wildcard).
-- If no user-visible bindings remain, returns @true.@.
-- Otherwise, comma-separated @K = V@ lines terminated with a dot.
prettyQueryResult :: Map Text Term -> String
prettyQueryResult m =
  let visible = [(k, v) | (k, v) <- Map.toAscList m, not ("_" `T.isPrefixOf` k)]
   in case visible of
        [] -> "true.\n"
        _ -> formatBindings visible
  where
    formatBindings [] = ""
    formatBindings [(k, v)] = T.unpack k ++ " = " ++ prettyTerm v ++ ".\n"
    formatBindings ((k, v) : rest) =
      T.unpack k ++ " = " ++ prettyTerm v ++ ",\n" ++ formatBindings rest
