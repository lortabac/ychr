{-# LANGUAGE OverloadedStrings #-}

-- | Rendering of solver-side type values as user-facing text.
--
-- The type checker solves types inside a CHR program and decodes them
-- on the way out ("YCHR.Internal.TypeCheck"). Their representation
-- ('tcon', 'fun', 'rigid', the @ty_@-prefixed base types) is declared
-- in the solver's CHR module, so every functor carries that module's
-- runtime-mangled prefix; 'typeModule' is the one place that knows it.
module YCHR.Internal.TypeCheck.Render
  ( -- * Rendering
    displayQualifiedAtom,
    showType,
    showValue,
    showValueShape,
    typeModule,

    -- * Dereferencing
    deepDerefType,
  )
where

import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Runtime.Monad (Chr)
import YCHR.Internal.Runtime.Registry (fromValueList)
import YCHR.Internal.Runtime.Types (Value (..))
import YCHR.Internal.Runtime.Var (deref)

-- | The CHR module the type representation is declared in, by its
-- source module name (@typechecker\/solver.chr@). Renaming that
-- module means changing this. Exported because the REPL shows
-- built-in types under the same qualifier
-- ("YCHR.Internal.Repl"@.builtinTypeModule@).
typeModule :: Text
typeModule = "$typechecker"

-- | Runtime functor name of a constructor declared in the solver's
-- type module — the flattened @m__n@ form the renamer produces.
typeAtom :: Text -> Text
typeAtom n = typeModule <> "__" <> n

-- | Convert a runtime-flattened qualified atom (@m__n@) back to the
-- source-level display form (@m:n@). No-op when the atom doesn't
-- contain @__@. Used in error messages so users see familiar syntax.
-- Inverse of the runtime name mangling.
displayQualifiedAtom :: Text -> Text
displayQualifiedAtom = T.replace "__" ":"

-- | Like 'displayQualifiedAtom', but additionally undoes the internal
-- spelling of the built-in types: the solver's module qualifier and
-- the @ty_@ constructor prefix both come off, so @$typechecker__ty_int@
-- renders as @int@. User-defined types stay module-qualified. This is
-- the only place a checker-internal atom becomes user-visible text, so
-- it is the only place that has to know about the prefix.
displayTypeAtom :: Text -> Text
displayTypeAtom t =
  let q = displayQualifiedAtom t
   in case T.stripPrefix (typeModule <> ":") q of
        Nothing -> q
        Just base -> fromMaybe base (T.stripPrefix "ty_" base)

-- | Render a solved type value as the source syntax a user would
-- write. Pure, so callers deep-dereference first ('deepDerefType') —
-- otherwise a solved variable prints as @_@ rather than as its type.
showType :: Value -> Text
showType (VAtom a) = displayTypeAtom a
showType (VTerm functor [a, b])
  | functor == typeAtom "tcon" =
      let name = showTypeName a
       in case fromValueList b of
            Just [] -> name
            Just as -> name <> "(" <> T.intercalate ", " (map showType as) <> ")"
            Nothing -> name <> "(?)"
  | functor == typeAtom "fun" =
      case fromValueList a of
        Just as ->
          "fun("
            <> T.intercalate ", " (map showType as)
            <> ") -> "
            <> showType b
        Nothing -> "fun(?) -> " <> showType b
-- Rigid type variable: rendered with its synthetic id so distinct
-- rigids are distinguishable in inconsistency messages. The original
-- source-level tvar name (@T@, @A@, ...) is not preserved because the
-- checker does not currently maintain an id-to-name map; @T#<n>@ is
-- enough to communicate "this is a polymorphic type variable" to the
-- reader. A skolem pinned by guard-derived evidence is rendered as
-- the type it was pinned to — that is the type the reader's guard
-- established. (Callers deep-dereference first, so a bound cell
-- arrives here as a concrete type rather than a variable.)
showType (VTerm functor [cell, VInt n])
  | functor == typeAtom "rigid" = case cell of
      VVar _ -> "T#" <> T.pack (show n)
      pinned -> showType pinned
showType (VVar _) = "_"
showType (VInt n) = T.pack (show n)
showType _ = "?"

showTypeName :: Value -> Text
showTypeName (VAtom a) = displayTypeAtom a
showTypeName _ = "?"

-- | Render a decoded diagnostic detail that is expected to be a plain
-- name atom.
showValue :: Value -> Chr Text
showValue v = do
  v' <- deref v
  case v' of
    VAtom a -> pure (displayQualifiedAtom a)
    _ -> pure "?"

-- | One-line description of a runtime 'Value''s outer shape, used only
-- in 'error' messages for broken-invariant cases while decoding the
-- diagnostic accumulators.
showValueShape :: Value -> String
showValueShape (VTerm f xs) =
  "VTerm " <> T.unpack f <> "/" <> show (length xs)
showValueShape (VAtom a) = "VAtom " <> T.unpack a
showValueShape (VInt _) = "VInt"
showValueShape (VFloat _) = "VFloat"
showValueShape (VText _) = "VText"
showValueShape (VBool _) = "VBool"
showValueShape (VVar _) = "VVar"
showValueShape VWildcard = "VWildcard"

-- | Dereference a type value through every nesting level, so
-- 'showType' (a pure function) sees the solved types rather than
-- bound-variable placeholders. This is what lets a pinned rigid's
-- cell, or a solved type-constructor argument, print as its type
-- instead of @_@.
deepDerefType :: Value -> Chr Value
deepDerefType v = do
  v' <- deref v
  case v' of
    VTerm f args -> VTerm f <$> traverse deepDerefType args
    _ -> pure v'
