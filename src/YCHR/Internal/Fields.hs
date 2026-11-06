{-# LANGUAGE OverloadedStrings #-}

-- | Labelled constructor fields: the accessor functions the compiler
-- writes for them.
--
-- The renamer rewrites @get_field(L, X)@ and @set_field(L, X, V)@ so
-- that @L@ is @m:ctor::lab@. Resolve turns that into a call of one of
-- the functions below, and adds them to the program. So the type
-- checker and the compiler only see ordinary positional code.
module YCHR.Internal.Fields
  ( getterName,
    setterName,
    accessorFunctions,
  )
where

import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Loc (noAnn)
import YCHR.Internal.PExpr qualified as PExpr
import YCHR.Internal.Parsed (AnnP (..))
import YCHR.Internal.Resolved qualified as R
import YCHR.Internal.Types

-- | The getter of label @lab@ of constructor @m:ctor@.
getterName :: Text -> Text -> Text -> QualifiedName
getterName = accessorName "get_field"

-- | The setter of label @lab@ of constructor @m:ctor@.
setterName :: Text -> Text -> Text -> QualifiedName
setterName = accessorName "set_field"

-- | @form(ctor__::lab)@. No atom can hold @__@ (the lexer rejects
-- it), so a user can't write this name, and it splits back into
-- @ctor@ and @lab@ one way only: the first @__::@ is right after
-- @ctor@, even when @ctor@ ends in @_@.
accessorName :: Text -> Text -> Text -> Text -> QualifiedName
accessorName form m c lab = QualifiedName m (form <> "(" <> c <> "__::" <> lab <> ")")

-- | A getter and a setter for every labelled argument of every type.
-- The type definitions must be renamed, so names are qualified.
--
-- For @pair(fst :: K, snd :: V)@ in type @t(K, V)@, label @fst@ gives:
--
-- > 'get_field(pair__::fst)'(t(K, V)) -> K
-- > 'get_field(pair__::fst)'(pair(A1, A2)) -> A1.
-- > 'set_field(pair__::fst)'(t(K, V), K) -> t(K, V)
-- > 'set_field(pair__::fst)'(pair(A1, A2), V) -> pair(V, A2).
--
-- If the type has other constructors, each gets an equation that
-- panics: @other(_, _) -> panic("...")@. That keeps the exhaustiveness
-- check quiet and gives a clear runtime error. There is no @_@
-- catch-all: an unbound argument must match no equation, so a guard
-- waits for it, as with a hand-written accessor.
accessorFunctions :: [TypeDefinition] -> [R.FunctionDef]
accessorFunctions tds =
  concat
    [ accessors td dc m c fs
    | td <- tds,
      dc <- typeConstructors td,
      Qualified m c <- [dc.conName],
      Labelled fs <- [dc.conFields]
    ]

accessors ::
  TypeDefinition ->
  DataConstructor ->
  Text ->
  Text ->
  NonEmpty (Text, TypeExpr) ->
  [R.FunctionDef]
accessors td dc m c fs =
  concat
    [ [getter i lab ty, setter i lab ty]
    | (i, (lab, ty)) <- zip [0 :: Int ..] (NE.toList fs)
    ]
  where
    n = NE.length fs
    vars = ["A" <> T.pack (show k) | k <- [1 .. n]]
    pat = CompoundTerm dc.conName (map VarTerm vars)
    tyT = TypeCon td.name (map TypeVar td.typeVars)
    -- A pattern for each other constructor of the type.
    others =
      [ CompoundTerm o.conName (map (const Wildcard) (conArgs o))
      | o <- typeConstructors td,
        o.conName /= dc.conName
      ]
    shown = T.unpack c <> "/" <> show n
    label lab = T.unpack c <> "::" <> T.unpack lab
    -- Shown in stack traces: @get_field(c::lab, X)@.
    source form lab =
      PExpr.Compound
        form
        ( map
            noAnn
            [ PExpr.Compound "::" [noAnn (PExpr.Atom c), noAnn (PExpr.Atom lab)],
              PExpr.Var "X"
            ]
        )
    eq form lab args rhs =
      let ann x = AnnP x td.loc (source form lab)
       in ann (R.FunctionEquation args (ann []) (ann (rhs :| [])))
    panicWith what lab =
      R.CallExpr
        (QualifiedName "prelude" "panic")
        [R.TextExpr (T.pack (what <> "(" <> label lab <> "): not a " <> shown))]
    fun name sig eqs =
      R.FunctionDef
        { name = name,
          arity = length sig.argTypes,
          signatures = [sig],
          isOpen = False,
          requiring = [],
          refining = Nothing,
          inline = False,
          equations = eqs
        }
    getter i lab ty =
      fun
        (getterName m c lab)
        (FunSignature [tyT] ty)
        ( eq "get_field" lab [pat] (R.VarExpr (vars !! i))
            : [eq "get_field" lab [o] (panicWith "get_field" lab) | o <- others]
        )
    setter i lab ty =
      fun
        (setterName m c lab)
        (FunSignature [tyT, ty] tyT)
        ( eq
            "set_field"
            lab
            [pat, VarTerm "V"]
            ( R.CtorExpr
                dc.conName
                [R.VarExpr (if k == i then "V" else v) | (k, v) <- zip [0 ..] vars]
            )
            : [eq "set_field" lab [o, Wildcard] (panicWith "set_field" lab) | o <- others]
        )
