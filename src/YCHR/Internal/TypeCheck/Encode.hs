{-# LANGUAGE OverloadedStrings #-}

-- | Encoding of the desugared AST as a ground CHR term.
--
-- The all-CHR type-checker (@typechecker\/@) receives the whole
-- program as one value and does every check itself, so this module is
-- the entire Haskell side of the input boundary: no walking, no
-- per-node constraint emission, no live handle table.
--
-- The shape of the encoding is declared, one constructor per Haskell
-- constructor, in @typechecker\/ast.chr@. That file and this one
-- are a matched pair; changing either without the other silently
-- produces terms no rule matches.
--
-- Two things the encoding deliberately does not carry:
--
--   * The 'PExpr' of each 'AnnP'. Diagnostics echo the source snippet
--     it pretty-prints, but no rule ever inspects it, and shipping the
--     parse tree into CHR would double the size of the term for
--     nothing. Instead each annotation gets a small integer id, and
--     'Encoded' returns the id-to-p-expr map so the driver can recover
--     the snippet when a diagnostic comes back naming that id.
--
--   * Fresh type variables. The old driver allocated a solver variable
--     per source type variable while encoding; here 'TypeVar' stays a
--     named source variable and the allocation is a CHR rule's job.
--
-- Names — of constraints, functions, constructors, type constructors —
-- are encoded in the runtime-mangled form ('runtimeName'), which is
-- what compiled CHR rules and the constructor-canonicalizing renamer
-- produce. A name in an encoded AST therefore compares equal to the
-- same name arriving from any other source. Everything else that is
-- spelled as an atom — source variable names, host-function names —
-- goes through 'atomTerm' unmangled, because it is never compared
-- against anything the compiler produced. The two are used
-- consistently per position, so no comparison ever straddles them.
--
-- /Type-parameter/ names are the exception among the source spellings:
-- they are encoded as strings rather than atoms. The checker has to
-- allocate one solver variable per distinct type parameter of a
-- declaration, in the order @Set.toList . Set.fromList@ produces —
-- ascending by name — because a rigid variable's synthetic id is
-- user-visible (@T#0@) and the two checkers must agree on it. Atoms
-- have no ordering CHR-side; strings do.
module YCHR.Internal.TypeCheck.Encode
  ( -- * Encoding
    Encoded (..),
    encodeProgram,
    encodeBodyGoals,
    encodeSourceLoc,

    -- * Handing the result to a session
    encodedToValue,

    -- * Atom naming
    astAtom,
  )
where

import Control.Monad.Trans.State.Strict (State, get, put, runState)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Compile.Names (runtimeName)
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Loc (SourceLoc (..))
import YCHR.Internal.PExpr (PExpr)
import YCHR.Internal.Parsed (AnnP (..))
import YCHR.Internal.Runtime.Types (Value (..))
import YCHR.Internal.Types
  ( BoundSig (..),
    ConstraintKey (..),
    DataConstructor (..),
    HeadArg (..),
    HeadConstraint (..),
    Name (..),
    QualifiedName,
    Term (..),
    TypeDefinition (..),
    TypeExpr (..),
    TypeKind (..),
    flattenName,
    qualifiedToName,
  )

-- | A program encoded for the CHR checker.
data Encoded = Encoded
  { -- | The ground term to hand to @check_program@ \/ @check_goals@.
    term :: Term,
    -- | The p-expr of every annotated node, keyed by the annotation id
    -- the encoded term carries. A pure artifact of the encoding: the
    -- driver reads it back when rendering a diagnostic, and nothing
    -- else ever sees it.
    origins :: IntMap PExpr
  }

-- | Annotation-id counter plus the p-exprs collected so far.
data EncState = EncState
  { nextAnnId :: !Int,
    seenOrigins :: !(IntMap PExpr)
  }

type Enc = State EncState

-- ---------------------------------------------------------------------------
-- Term construction
-- ---------------------------------------------------------------------------

-- | Runtime functor name of a constructor declared in the
-- @'$tc_ast'@ module. Every term this module builds is headed by one
-- of these.
astAtom :: Text -> Text
astAtom n = "$tc_ast__" <> n

-- | An @'$tc_ast'@ compound. Zero arguments yields an atom once
-- converted to a 'Value'.
ast :: Text -> [Term] -> Term
ast n args = CompoundTerm (Unqualified (astAtom n)) args

-- | A bare atom carrying exactly the given text. Used for names that
-- are already in runtime-mangled form and for source-level variable
-- names.
atomTerm :: Text -> Term
atomTerm t = CompoundTerm (Unqualified t) []

nameTerm :: Name -> Term
nameTerm = atomTerm . runtimeName

qnameTerm :: QualifiedName -> Term
qnameTerm = nameTerm . qualifiedToName

-- | A Prolog list in the renamer-canonicalized spelling the runtime
-- uses (@prelude:.@ \/ @prelude:[]@).
listTerm :: [Term] -> Term
listTerm = foldr cons nil
  where
    cons x xs = CompoundTerm (Unqualified "prelude__.") [x, xs]
    nil = CompoundTerm (Unqualified "prelude__[]") []

-- | A @library(maybe)@ optional value.
maybeTerm :: Maybe Term -> Term
maybeTerm Nothing = CompoundTerm (Unqualified "maybe__nothing") []
maybeTerm (Just t) = CompoundTerm (Unqualified "maybe__just") [t]

-- | A @library(pairs)@ association-list entry.
kvTerm :: Term -> Term -> Term
kvTerm k v = CompoundTerm (Unqualified "pairs__kv") [k, v]

intTerm :: Int -> Term
intTerm = IntTerm . fromIntegral

-- ---------------------------------------------------------------------------
-- Entry points
-- ---------------------------------------------------------------------------

-- | Encode a whole desugared program.
encodeProgram :: D.Program -> Encoded
encodeProgram prog =
  let (t, st) = runState (program prog) (EncState 0 IntMap.empty)
   in Encoded {term = t, origins = st.seenOrigins}

-- | Encode a query's body goals. Goals carry no annotations of their
-- own — the caller supplies the one location they are all checked
-- against — so this needs no state and returns a bare term.
encodeBodyGoals :: [D.BodyGoal] -> Term
encodeBodyGoals = listTerm . map bodyGoal

-- | Encode a source position. Exposed because the goal entry point
-- takes the one location its goals are checked against as a separate
-- argument, rather than reading it off an annotation.
encodeSourceLoc :: SourceLoc -> Term
encodeSourceLoc l = ast "loc" [TextTerm (T.pack l.file), intTerm l.line, intTerm l.col]

-- ---------------------------------------------------------------------------
-- Program structure
-- ---------------------------------------------------------------------------

program :: D.Program -> Enc Term
program prog = do
  rs <- traverse rule prog.rules
  fs <- traverse function prog.functions
  pure
    ( ast
        "program"
        [ listTerm rs,
          listTerm fs,
          assocTerm (listTerm . map typeExpr) prog.constraintTypes,
          assocTerm (listTerm . map boundSig) prog.constraintBounds,
          listTerm (map typeDef prog.typeDefinitions)
        ]
    )

-- | A @Map ConstraintKey v@ as an assoc list, in ascending key order.
assocTerm :: (v -> Term) -> Map ConstraintKey v -> Term
assocTerm f m = listTerm [kvTerm (conKey k) (f v) | (k, v) <- Map.toAscList m]

conKey :: ConstraintKey -> Term
conKey k = ast "con_key" [qnameTerm k.name, intTerm k.arity]

-- | Encode an annotated node: allocate an id, remember the node's
-- p-expr under it, and emit @ann(Id, Loc, Node)@.
ann :: (a -> Term) -> AnnP a -> Enc Term
ann f a = do
  st <- get
  let i = st.nextAnnId
  put
    EncState
      { nextAnnId = i + 1,
        seenOrigins = IntMap.insert i a.parsed st.seenOrigins
      }
  pure (ast "ann" [intTerm i, encodeSourceLoc a.sourceLoc, f a.node])

rule :: D.Rule -> Enc Term
rule r = do
  h <- ann ruleHead r.head
  g <- ann (listTerm . map guard) r.guard
  b <- ann (listTerm . map bodyGoal) r.body
  pure (ast "rule" [maybeTerm (TextTerm <$> r.name), h, g, b])

ruleHead :: D.Head -> Term
ruleHead h =
  ast "rule_head" [listTerm (map headCon h.kept), listTerm (map headCon h.removed)]

headCon :: HeadConstraint -> Term
headCon hc = ast "head_con" [qnameTerm hc.name, listTerm (map headArg hc.args)]

headArg :: HeadArg -> Term
headArg (HeadVar v) = ast "head_var" [atomTerm v]
headArg HeadWildcard = ast "head_wild" []

function :: D.Function -> Enc Term
function f = do
  eqs <- ann (listTerm . map equation) f.equations
  pure
    ( ast
        "fun_def"
        [ qnameTerm f.name,
          intTerm f.arity,
          listTerm (map funSig f.signatures),
          listTerm (map boundSig f.requiring),
          eqs
        ]
    )

funSig :: ([TypeExpr], TypeExpr) -> Term
funSig (args, ret) = ast "fun_sig" [listTerm (map typeExpr args), typeExpr ret]

equation :: D.Equation -> Term
equation eq =
  ast
    "fun_eq"
    [ listTerm (map headArg eq.params),
      listTerm (map guard eq.guards),
      listTerm (map funStmt eq.prelude),
      expr eq.rhs
    ]

boundSig :: BoundSig -> Term
boundSig b =
  ast
    "bound_sig"
    [ nameTerm b.name,
      intTerm b.arity,
      listTerm (map typeExpr b.argTypes),
      typeExpr b.returnType,
      encodeSourceLoc b.loc
    ]

-- ---------------------------------------------------------------------------
-- Goals, guards, expressions
-- ---------------------------------------------------------------------------

guard :: D.Guard -> Term
guard (D.GuardEqual a b) = ast "guard_equal" [expr a, expr b]
guard (D.GuardMatch e n i) = ast "guard_match" [expr e, nameTerm n, intTerm i]
guard (D.GuardGetArg v e i) = ast "guard_getarg" [atomTerm v, expr e, intTerm i]
guard (D.GuardExpr e) = ast "guard_expr" [expr e]

bodyGoal :: D.BodyGoal -> Term
bodyGoal D.BodyTrue = ast "body_true" []
bodyGoal (D.BodyTell n args) = ast "body_tell" [qnameTerm n, exprs args]
bodyGoal (D.BodyUnify a b) = ast "body_unify" [expr a, expr b]
bodyGoal (D.BodyHostStmt f args) = ast "body_host" [atomTerm f, exprs args]
bodyGoal (D.BodyIs v e) = ast "body_is" [atomTerm v, expr e]
bodyGoal (D.BodyCall n args) = ast "body_call" [qnameTerm n, exprs args]
bodyGoal (D.BodyApply f args) = ast "body_apply" [expr f, exprs args]

funStmt :: D.FunStmt -> Term
funStmt (D.FunIs v e) = ast "fun_is" [atomTerm v, expr e]
funStmt (D.FunHostStmt f args) = ast "fun_host" [atomTerm f, exprs args]
funStmt (D.FunCall n args) = ast "fun_call" [qnameTerm n, exprs args]
funStmt (D.FunApply f args) = ast "fun_apply" [expr f, exprs args]

exprs :: [D.Expr] -> Term
exprs = listTerm . map expr

expr :: D.Expr -> Term
expr (D.VarExpr v) = ast "var_e" [atomTerm v]
expr (D.IntExpr n) = ast "int_e" [IntTerm n]
expr (D.FloatExpr n) = ast "float_e" [FloatTerm n]
expr (D.TextExpr s) = ast "text_e" [TextTerm s]
expr D.WildcardExpr = ast "wild_e" []
expr (D.CtorExpr n args) = ast "ctor_e" [nameTerm n, exprs args]
expr (D.CallExpr n args) = ast "call_e" [qnameTerm n, exprs args]
expr (D.ApplyExpr f args) = ast "apply_e" [expr f, exprs args]
expr (D.FunRefExpr n arity) = ast "funref_e" [qnameTerm n, intTerm arity]
expr (D.LambdaExpr params body) =
  ast
    "lambda_e"
    [ listTerm (map headArg (NE.toList params)),
      exprs (NE.toList body)
    ]
expr (D.HostExpr f args) = ast "host_e" [atomTerm f, exprs args]

-- ---------------------------------------------------------------------------
-- Type declarations
-- ---------------------------------------------------------------------------

-- | A source type expression. Function types are the one shape that is
-- normalized rather than transcribed: @fun(A, B) -> C@ parses as
-- @TypeCon \"->\" [TypeCon \"fun\" [A, B], C]@, and every consumer has
-- to re-recognize that spelling before doing anything with it.
-- Recognizing it once,
-- here, means the CHR side never has to compare against the bare atoms
-- @'->'@ and @fun@: it matches a constructor instead, which is both
-- clearer and immune to a checker-internal declaration happening to
-- share one of those names.
--
-- Only the exact two-level shape is a function type. Anything else
-- headed by @->@ or @fun@ is an ordinary type reference and stays a
-- 'tconx', exactly as the Haskell consumers treat it.
typeExpr :: TypeExpr -> Term
typeExpr (TypeVar v) = ast "tvar" [TextTerm v]
typeExpr (TypeCon (Unqualified "->") [TypeCon (Unqualified "fun") argTys, retTy]) =
  ast "tfunx" [listTerm (map typeExpr argTys), typeExpr retTy]
typeExpr (TypeCon n args) = ast "tconx" [nameTerm n, listTerm (map typeExpr args)]

typeDef :: TypeDefinition -> Term
typeDef td =
  ast
    "type_def"
    [ nameTerm td.name,
      listTerm (map TextTerm td.typeVars),
      typeKind td.kind,
      encodeSourceLoc td.loc
    ]

typeKind :: TypeKind -> Term
typeKind (Algebraic cs) = ast "algebraic" [listTerm (map dataCon cs)]
typeKind Opaque = ast "opaque" []

dataCon :: DataConstructor -> Term
dataCon dc = ast "data_con" [nameTerm dc.conName, listTerm (map typeExpr dc.conArgs)]

-- ---------------------------------------------------------------------------
-- Handing the result to a session
-- ---------------------------------------------------------------------------

-- | Convert an encoded term to the runtime 'Value' a session sees.
--
-- Deliberately not 'YCHR.Internal.Meta.termToValue': that one is the
-- /host/ bridge, and rewrites a bare @true@ \/ @false@ compound to a
-- native boolean. An encoded AST is data about a program, not values
-- of one — a user constructor spelled @true@ has to survive as the
-- atom the checker's constructor tables are keyed on. There are no
-- variables to allocate either, since the encoding is ground, so this
-- is a plain fold.
encodedToValue :: Term -> Value
encodedToValue (IntTerm n) = VInt n
encodedToValue (FloatTerm d) = VFloat d
encodedToValue (TextTerm t) = VText t
encodedToValue Wildcard = VWildcard
encodedToValue (CompoundTerm n []) = VAtom (flattenName n)
encodedToValue (CompoundTerm n args) = VTerm (flattenName n) (map encodedToValue args)
encodedToValue (VarTerm v) =
  error
    ( "TypeCheck.Encode.encodedToValue: encoded terms are ground, got var "
        <> T.unpack v
    )
