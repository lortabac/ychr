{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Internal.Desugar.Hnf
-- Description : The core of the Head Normal Form transformation.
--
-- HNF replaces a non-variable or repeated argument with a fresh variable
-- and emits the 'D.GuardEqual', 'D.GuardMatch' and 'D.GuardGetArg' guards
-- that recover what the argument said. "YCHR.Internal.Desugar" runs it
-- over rule heads, aggregate goals and equation patterns;
-- "YCHR.Internal.Desugar.AggregateScope" runs it over an aggregate's
-- result pattern.
module YCHR.Internal.Desugar.Hnf
  ( HnfState (..),
    Hnf,
    hnfState,
    normalizeArg,
    headTermToExpr,
  )
where

import Control.Monad (zipWithM_)
import Control.Monad.Trans.State.Strict (State, get, modify', put)
import Data.Sequence (Seq, (|>))
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Types

-- | Prefix for fresh variables introduced by the Head Normal Form
-- transformation.
--
-- The leading @$@ keeps the name out of reach of source code: a source
-- variable is @[A-Z_][A-Za-z0-9_]*@, so it can never spell @$hnf_0@. A
-- bare @_hnf_0@ would be a legal source variable name and would shadow the
-- slot HNF created for a decomposed argument.
hnfPrefix :: Text
hnfPrefix = "$hnf_"

-- | Convert a head-position 'Term' (always a pattern: variable, wildcard,
-- literal, or constructor compound) to its 'D.Expr' equivalent. HNF
-- emits guards whose operands are these patterns, so the conversion is
-- exhaustive over the pattern grammar.
headTermToExpr :: Term -> D.Expr
headTermToExpr (VarTerm v) = D.VarExpr v
headTermToExpr Wildcard = D.WildcardExpr
headTermToExpr (IntTerm n) = D.IntExpr n
headTermToExpr (FloatTerm n) = D.FloatExpr n
headTermToExpr (TextTerm s) = D.TextExpr s
headTermToExpr (CompoundTerm n args) =
  D.CtorExpr n (map headTermToExpr args)

-- | State for HNF: a fresh-variable counter, the set of
-- variable names already seen in the head so far (so that duplicates
-- can be detected), the guards emitted so far, and the prefix of the
-- fresh names.
--
-- The guards are a 'Seq' so that they accumulate in the order they
-- are emitted: a list would have to be prepended to and reversed
-- exactly once at each consumer, which is an invariant no type
-- enforces.
data HnfState = HnfState
  { counter :: !Int,
    seen :: Set.Set Text,
    guards :: Seq D.Guard,
    prefix :: Text
  }

-- | A fresh state: counter 0, nothing seen, no guards, @$hnf_@ names.
hnfState :: HnfState
hnfState = HnfState 0 Set.empty Seq.empty hnfPrefix

-- | An HNF step.
type Hnf = State HnfState

-- | The next fresh name; moves the counter past it.
fresh :: Hnf Text
fresh = do
  st <- get
  put st {counter = st.counter + 1}
  pure (st.prefix <> T.pack (show st.counter))

emit :: D.Guard -> Hnf ()
emit g = modify' (\st -> st {guards = st.guards |> g})

-- | Record a variable as seen. Returns whether it was seen before.
see :: Text -> Hnf Bool
see v = do
  st <- get
  let before = Set.member v st.seen
  put st {seen = Set.insert v st.seen}
  pure before

-- | Normalize one argument of a head constraint. Fresh variables are
-- only introduced for duplicates and non-variables; first-use variables
-- and wildcards pass through.
normalizeArg :: Term -> Hnf HeadArg
normalizeArg (VarTerm v) = do
  dup <- see v
  if dup
    then do
      x <- fresh
      emit (D.GuardEqual (D.VarExpr v) (D.VarExpr x))
      pure (HeadVar x)
    else pure (HeadVar v)
-- Wildcards pass through unchanged: they match anything, are never referenced,
-- and cannot duplicate, so no fresh variable or guard is needed.
normalizeArg Wildcard = pure HeadWildcard
normalizeArg (CompoundTerm cname cargs) = do
  x <- fresh
  decomposeCompound x cname cargs
  pure (HeadVar x)
normalizeArg term = do
  x <- fresh
  emit (D.GuardEqual (D.VarExpr x) (headTermToExpr term))
  pure (HeadVar x)

-- | Decompose a compound term into match and extraction guards. Both
-- 'Qualified' and 'Unqualified' constructor functors are handled
-- uniformly: the renamer canonicalizes data constructors to their
-- 'Qualified' form, and the compiler emits both as a single flat-atom
-- compound (see 'YCHR.Internal.Compile.compileTerm') — so HNF can just emit one
-- 'GuardMatch' per compound regardless of where the name originated.
decomposeCompound :: Text -> Name -> [Term] -> Hnf ()
decomposeCompound parentVar cname cargs = do
  -- 'length' is non-negative, so the conversion to 'Word' is safe.
  emit (D.GuardMatch (D.VarExpr parentVar) cname (fromIntegral (length cargs)))
  zipWithM_ (decomposeArg parentVar) [0 ..] cargs

-- | Decompose a single argument of a compound term.
decomposeArg :: Text -> Word -> Term -> Hnf ()
decomposeArg parentVar i (VarTerm v) = do
  dup <- see v
  if dup
    then do
      -- Duplicate variable: extract and check equality
      x <- fresh
      emit (D.GuardGetArg x (D.VarExpr parentVar) i)
      emit (D.GuardEqual (D.VarExpr v) (D.VarExpr x))
    else
      -- First occurrence: extract and bind
      emit (D.GuardGetArg v (D.VarExpr parentVar) i)
decomposeArg _ _ Wildcard = pure ()
decomposeArg parentVar i (CompoundTerm cname cargs) = do
  -- Nested compound: extract then recursively decompose
  x <- fresh
  emit (D.GuardGetArg x (D.VarExpr parentVar) i)
  decomposeCompound x cname cargs
decomposeArg parentVar i term = do
  -- Ground term (atom, integer, string): extract and check equality
  x <- fresh
  emit (D.GuardGetArg x (D.VarExpr parentVar) i)
  emit (D.GuardEqual (D.VarExpr x) (headTermToExpr term))
