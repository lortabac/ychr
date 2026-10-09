{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Function inlining: substituting a call to an @:- inline@-marked
-- function with its body at eligible call sites.
--
-- 'YCHR.Internal.Resolve.checkInlineDeclarations' has already verified
-- that every @:- inline@-marked function is local and closed, so by
-- the time this pass runs every candidate ('YCHR.Internal.Desugared.Function'
-- with 'YCHR.Internal.Desugared.Function.inline' set) is a real,
-- single-module function. What is checked here is the shape that
-- makes substitution possible at all:
--
--   * exactly one equation (an inline substitution has no way to try
--     equations in order: the desugared AST has no conditional);
--   * that equation has no guards (including HNF-synthesized ones —
--     see 'YCHR.Internal.Desugar.normalizeArg' — so every parameter is
--     a plain variable or wildcard) and an empty prelude (so the body
--     is a single return expression);
--   * no cycle among candidates, direct or transitive. A function that
--     calls itself (even through another candidate) has no finite
--     inlined form.
--
-- Any violation is a hard error: the directive asked for something
-- this function cannot do at all, as opposed to one call site that
-- cannot absorb a particular argument (see 'trySubstitute'), which
-- silently keeps the ordinary call instead.
--
-- Candidates are processed in a topological order over their call
-- graph — callees before callers — so that by the time a candidate's
-- own body is rewritten, every other candidate it calls has already
-- been fully expanded ('finalCandidates'). Sound because the cycle
-- check has already proven the candidate call graph acyclic, so a
-- postorder depth-first walk visits every node exactly once.
module YCHR.Internal.Desugar.Inline (inlineFunctions) where

import Data.List (sort)
-- 'foldl'' is imported qualified because the Prelude only re-exports it
-- from base 4.20 (GHC 9.10); MicroHs's bundled base is older. An
-- unqualified 'import Data.List (foldl'')' would be flagged redundant
-- under GHC, since 'sort' above already covers this module's other
-- "Data.List" need.
import Data.List qualified as List
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
-- Re-exported from "YCHR.Internal.Desugar" so error codes/messages for
-- the new constructors live where every other 'DesugarError' lives.
import YCHR.Internal.Desugar (DesugarError (..))
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Diagnostic (Diagnostic, noDiag)
import YCHR.Internal.Loc (dummyLoc)
import YCHR.Internal.PExpr (PExpr (Atom))
import YCHR.Internal.Parsed (AnnP (..))
import YCHR.Internal.Resolved qualified as R
import YCHR.Internal.Types
  ( HeadArg (..),
    Name (Unqualified),
    QualifiedName (..),
    flattenName,
    qualifiedToName,
  )

-- | A candidate's eligible shape: its parameters and its (possibly
-- already-inlined) return expression.
data Candidate = Candidate
  { params :: [HeadArg],
    rhs :: R.Expr
  }

type Candidates = Map QualifiedName Candidate

-- | Rewrite the program: substitute every eligible call to an
-- @:- inline@-marked function with its body, everywhere an 'R.Expr' or
-- statement-position call can appear (rule guards and bodies, and
-- every function's guards, prelude, and return expression — including
-- another candidate's own, so a chain of inline calls collapses to one
-- level). A program with no @:- inline@-marked function comes back
-- unchanged.
--
-- When a candidate's declared shape is ineligible, or two or more
-- candidates call each other, the diagnostics describe why and the
-- program comes back unchanged (mirrors
-- 'YCHR.Internal.Desugar.liftAllLambdas': the caller treats any
-- non-empty error list as a hard failure and never looks at the
-- program half of the pair).
inlineFunctions :: D.Program -> (D.Program, [Diagnostic DesugarError])
inlineFunctions prog = case buildCandidates prog.functions of
  Left errs -> (prog, errs)
  Right raw
    | Map.null raw -> (prog, [])
    | otherwise ->
        let cands = finalCandidates raw
         in ( prog
                { D.rules = map (rewriteRule cands) prog.rules,
                  D.functions = map (rewriteFunction cands) prog.functions
                },
              []
            )

-- ---------------------------------------------------------------------------
-- Candidate collection and validation
-- ---------------------------------------------------------------------------

-- | Collect every @:- inline@-marked function's single-equation body,
-- after checking it is eligible on its own (one equation, no guards,
-- no prelude) and that no candidate's call graph contains a cycle.
buildCandidates ::
  [D.Function] -> Either [Diagnostic DesugarError] (Map QualifiedName Candidate)
buildCandidates functions =
  let marked = [f | f <- functions, f.inline]
      shapeErrs = concatMap shapeCheck marked
   in if not (null shapeErrs)
        then Left shapeErrs
        else
          let raw =
                Map.fromList
                  [ (f.name, Candidate {params = annEq.node.params, rhs = annEq.node.rhs})
                  | f <- marked,
                    [annEq] <- [f.equations]
                  ]
              candNames = Map.keysSet raw
              graph =
                Map.fromList
                  [ (name, directCallees candNames cand.rhs)
                  | (name, cand) <- Map.toList raw
                  ]
              cyclic = cyclicNodes graph
           in if not (null cyclic)
                then Left [cycleDiagnostic marked cyclic]
                else Right raw

-- | Check that a single @:- inline@-marked function has the shape an
-- inline substitution needs. Every violation is independent, so a
-- program with several ineligible candidates gets one diagnostic per
-- candidate (not per violation: each candidate fails at most one of
-- these, in this order).
shapeCheck :: D.Function -> [Diagnostic DesugarError]
shapeCheck f = case f.equations of
  [annEq]
    | not (null annEq.node.guards) -> [diag (InlineGuardedEquation f.name)]
    | not (null annEq.node.prelude) -> [diag (InlineStatefulEquation f.name)]
    | otherwise -> []
  eqs -> [diag (InlineNotSingleEquation f.name (length eqs))]
  where
    diag err = noDiag (AnnP err loc pexpr)
    (loc, pexpr) = case f.equations of
      (annEq : _) -> (annEq.sourceLoc, annEq.parsed)
      [] -> (dummyLoc, Atom "inline")

-- | Every 'R.CallExpr' target reachable anywhere inside an expression,
-- regardless of nesting. Used both to build the candidate call graph
-- and (via 'rewriteExpr') to perform the actual substitution.
collectCalls :: R.Expr -> [QualifiedName]
collectCalls e = case e of
  R.VarExpr _ -> []
  R.IntExpr _ -> []
  R.FloatExpr _ -> []
  R.TextExpr _ -> []
  R.WildcardExpr -> []
  R.FunRefExpr _ _ -> []
  R.CtorExpr _ args -> concatMap collectCalls args
  R.HostExpr _ args -> concatMap collectCalls args
  R.ApplyExpr f args -> collectCalls f ++ concatMap collectCalls args
  R.CallExpr qn args -> qn : concatMap collectCalls args
  -- Unreachable: lambda lifting runs before this pass, so no
  -- 'R.LambdaExpr' survives into a desugared function's body. Walked
  -- anyway rather than left partial, matching 'compileExpr's own
  -- defensive 'error' on the same shape.
  R.LambdaExpr _ body -> concatMap collectCalls (NE.toList body)

-- | The candidates (by name) that an expression calls directly.
directCallees :: Set QualifiedName -> R.Expr -> Set QualifiedName
directCallees candNames = Set.filter (`Set.member` candNames) . Set.fromList . collectCalls

-- | Every candidate that is on a cycle of the candidate call graph —
-- reachable from one of its own direct callees. A self-call (@f@ calls
-- @f@) is a cycle of length one and is caught the same way, since
-- @f@'s own name is then among its direct callees.
cyclicNodes :: Map QualifiedName (Set QualifiedName) -> [QualifiedName]
cyclicNodes graph =
  [n | n <- Map.keys graph, n `Set.member` reachableFrom (successors n)]
  where
    successors n = Map.findWithDefault Set.empty n graph
    reachableFrom start = go Set.empty (Set.toList start)
    go seen [] = seen
    go seen (x : xs)
      | x `Set.member` seen = go seen xs
      | otherwise = go (Set.insert x seen) (Set.toList (successors x) ++ xs)

cycleDiagnostic :: [D.Function] -> [QualifiedName] -> Diagnostic DesugarError
cycleDiagnostic marked cyclic =
  let names = sort (map (flattenName . qualifiedToName) cyclic)
      cyclicSet = Set.fromList cyclic
      (loc, pexpr) = case [f | f <- marked, Set.member f.name cyclicSet] of
        (f : _) -> case f.equations of
          (annEq : _) -> (annEq.sourceLoc, annEq.parsed)
          [] -> (dummyLoc, Atom "inline")
        [] -> (dummyLoc, Atom "inline")
   in noDiag (AnnP (InlineCycle names) loc pexpr)

-- ---------------------------------------------------------------------------
-- Candidate finalization
-- ---------------------------------------------------------------------------

-- | Rewrite every candidate's body, each one using only the
-- already-finalized bodies of the candidates it calls. Processes
-- candidates in a topological order over their call graph — callees
-- before callers, from 'topoOrder' — which 'buildCandidates' has
-- already proven acyclic, so this never looks up a name it has not
-- filled in yet.
finalCandidates :: Candidates -> Candidates
finalCandidates raw = List.foldl' step Map.empty (topoOrder graph)
  where
    candNames = Map.keysSet raw
    graph = Map.map (\cand -> directCallees candNames cand.rhs) raw
    step acc name = case Map.lookup name raw of
      Nothing -> acc
      Just cand -> Map.insert name (cand {rhs = rewriteExpr acc cand.rhs}) acc

-- | A topological order of a call graph's nodes — callees before
-- callers — as the finish order of a postorder depth-first walk.
-- Sound only when the graph is acyclic, which every caller here has
-- already checked; an unchecked cyclic graph would make this loop.
topoOrder :: Map QualifiedName (Set QualifiedName) -> [QualifiedName]
topoOrder graph = reverse order
  where
    (_, order) = List.foldl' visit (Set.empty, []) (Map.keys graph)
    visit (seen, out) n
      | n `Set.member` seen = (seen, out)
      | otherwise =
          let seen1 = Set.insert n seen
              (seen2, out2) = List.foldl' visit (seen1, out) (Set.toList (successors n))
           in (seen2, n : out2)
    successors n = Map.findWithDefault Set.empty n graph

-- ---------------------------------------------------------------------------
-- Substitution
-- ---------------------------------------------------------------------------

-- | Rewrite every eligible call inside an expression, recursing into
-- every child first so a nested candidate call is substituted before
-- an enclosing one is considered.
rewriteExpr :: Candidates -> R.Expr -> R.Expr
rewriteExpr cands = go
  where
    go e = case e of
      R.VarExpr _ -> e
      R.IntExpr _ -> e
      R.FloatExpr _ -> e
      R.TextExpr _ -> e
      R.WildcardExpr -> e
      R.FunRefExpr _ _ -> e
      R.CtorExpr n args -> R.CtorExpr n (map go args)
      R.HostExpr n args -> R.HostExpr n (map go args)
      R.ApplyExpr f args -> R.ApplyExpr (go f) (map go args)
      -- Unreachable; see 'collectCalls'.
      R.LambdaExpr params body -> R.LambdaExpr params (NE.map go body)
      R.CallExpr qn args ->
        let args' = map go args
         in case Map.lookup qn cands of
              Nothing -> R.CallExpr qn args'
              Just cand -> maybe (R.CallExpr qn args') id (trySubstitute cand args')

-- | Like 'rewriteExpr', but for the RHS of an @is@ binding
-- ('D.BodyIs' / 'D.FunIs'). The compiler dispatches @is@ on the
-- /syntactic/ shape of its RHS: a bare variable compiles to 'EvalIs'
-- (deep-deref, then walk and evaluate the resulting value's compound
-- subterms), anything else to plain 'EvalDeep'. A substitution that
-- turns a call into a bare variable would silently flip that mode, so
-- it is rejected here and the ordinary call is kept — even though the
-- very same substitution is safe (and applied) everywhere else an
-- expression simply denotes a value.
rewriteIsRhs :: Candidates -> R.Expr -> R.Expr
rewriteIsRhs cands e = case e of
  R.CallExpr qn args ->
    let args' = map (rewriteExpr cands) args
        kept = R.CallExpr qn args'
     in case Map.lookup qn cands of
          Nothing -> kept
          Just cand -> case trySubstitute cand args' of
            Just (R.VarExpr _) -> kept
            Just result -> result
            Nothing -> kept
  _ -> rewriteExpr cands e

-- | Try to substitute a candidate's body for a call to it, given the
-- call's (already-rewritten) arguments. 'Nothing' means the call stays
-- as an ordinary call — a non-trivial argument could not be placed
-- safely, so inlining this particular site would change what gets
-- evaluated, when, or how often.
--
-- An argument is /trivial/ (a variable, a literal, or a wildcard — see
-- 'isTrivial') when substituting it changes nothing observable: it has
-- no evaluation effect of its own, so it may be freely duplicated or
-- dropped. Any other argument is /non-trivial/ and may be substituted
-- only when all of the following hold:
--
--   * its parameter is a plain variable (not a wildcard — a wildcard
--     parameter never appears in the body, so a non-trivial argument
--     bound to one would be silently dropped, losing whatever
--     evaluation it would have done as part of an ordinary call);
--   * that variable occurs exactly once in the body;
--   * that occurrence is not nested inside a @quote\/1@ subterm, where
--     the compiler stops evaluating ('YCHR.Internal.Compile.compileExpr's
--     @quote@ case) — substituting an unevaluated expression there
--     would embed it as literal structure instead of the value a real
--     call would have produced;
--   * taken together, in call order, the non-trivial arguments' single
--     occurrences appear in the body in that same left-to-right order,
--     so the body's own evaluation order after substitution still
--     matches call-by-value's "every argument, once, left to right".
trySubstitute :: Candidate -> [R.Expr] -> Maybe R.Expr
trySubstitute cand args
  | length cand.params /= length args = Nothing
  | otherwise = do
      let pairs = zip cand.params args
          rhs = cand.rhs
      if any (\(p, a) -> p == HeadWildcard && not (isTrivial a)) pairs
        then Nothing
        else do
          let nonTrivial = [(v, a) | (HeadVar v, a) <- pairs, not (isTrivial a)]
          if any (\(v, _) -> occurrenceCount v rhs /= 1 || occursUnderQuote v rhs) nonTrivial
            then Nothing
            else
              if not (orderMatches (map fst nonTrivial) rhs)
                then Nothing
                else
                  let subst = Map.fromList [(v, a) | (HeadVar v, a) <- pairs]
                   in Just (substExpr subst rhs)

-- | A value expression whose evaluation has no effect of its own, so it
-- may be duplicated or dropped freely: a variable reference, a
-- literal, the anonymous variable, or a nullary (atom-like)
-- constructor. Everything else — a call, a dynamic dispatch, a host
-- call, or a non-nullary constructor (which may itself contain one of
-- those) — is evaluated exactly once by an ordinary call and must stay
-- that way.
isTrivial :: R.Expr -> Bool
isTrivial e = case e of
  R.VarExpr _ -> True
  R.IntExpr _ -> True
  R.FloatExpr _ -> True
  R.TextExpr _ -> True
  R.WildcardExpr -> True
  R.CtorExpr _ [] -> True
  R.CtorExpr _ (_ : _) -> False
  R.CallExpr {} -> False
  R.ApplyExpr {} -> False
  R.HostExpr {} -> False
  R.FunRefExpr _ _ -> True
  R.LambdaExpr {} -> False

-- | Every free variable name referenced anywhere inside an expression,
-- in left-to-right order, duplicates included.
varOccurrences :: R.Expr -> [Text]
varOccurrences e = case e of
  R.VarExpr v -> [v]
  R.IntExpr _ -> []
  R.FloatExpr _ -> []
  R.TextExpr _ -> []
  R.WildcardExpr -> []
  R.FunRefExpr _ _ -> []
  R.CtorExpr _ args -> concatMap varOccurrences args
  R.HostExpr _ args -> concatMap varOccurrences args
  R.ApplyExpr f args -> varOccurrences f ++ concatMap varOccurrences args
  R.CallExpr _ args -> concatMap varOccurrences args
  R.LambdaExpr _ body -> concatMap varOccurrences (NE.toList body)

occurrenceCount :: Text -> R.Expr -> Int
occurrenceCount v = length . filter (== v) . varOccurrences

-- | Whether the (single, already counted) occurrence of a variable
-- sits inside a @quote\/1@ subterm. Mirrors the exact shape
-- 'YCHR.Internal.Compile.compileExpr' recognizes as the quoting form.
occursUnderQuote :: Text -> R.Expr -> Bool
occursUnderQuote v = goTop
  where
    goTop e = case e of
      R.CtorExpr (Unqualified "quote") [arg] -> v `elem` varOccurrences arg
      R.CtorExpr _ args -> any goTop args
      R.HostExpr _ args -> any goTop args
      R.ApplyExpr f args -> goTop f || any goTop args
      R.CallExpr _ args -> any goTop args
      R.LambdaExpr _ body -> any goTop (NE.toList body)
      R.VarExpr _ -> False
      R.IntExpr _ -> False
      R.FloatExpr _ -> False
      R.TextExpr _ -> False
      R.WildcardExpr -> False
      R.FunRefExpr _ _ -> False

-- | Whether a wanted sequence of (distinct, single-occurrence)
-- variable names appears, in that order, among an expression's
-- variable occurrences.
orderMatches :: [Text] -> R.Expr -> Bool
orderMatches wanted rhs =
  let wantedSet = Set.fromList wanted
   in filter (`Set.member` wantedSet) (varOccurrences rhs) == wanted

-- | Replace every 'R.VarExpr' leaf named in the substitution with the
-- expression it maps to. Sound without capture-avoidance: a
-- candidate's free variables are exactly its parameters (desugaring
-- commits to that upstream), and 'trySubstitute' has already confirmed
-- every replaced occurrence may be duplicated, dropped, or placed
-- exactly once without changing evaluation order.
substExpr :: Map Text R.Expr -> R.Expr -> R.Expr
substExpr subst = go
  where
    go e = case e of
      R.VarExpr v -> Map.findWithDefault e v subst
      R.IntExpr _ -> e
      R.FloatExpr _ -> e
      R.TextExpr _ -> e
      R.WildcardExpr -> e
      R.FunRefExpr _ _ -> e
      R.CtorExpr n args -> R.CtorExpr n (map go args)
      R.HostExpr n args -> R.HostExpr n (map go args)
      R.ApplyExpr f args -> R.ApplyExpr (go f) (map go args)
      R.CallExpr qn args -> R.CallExpr qn (map go args)
      R.LambdaExpr params body -> R.LambdaExpr params (NE.map go body)

-- ---------------------------------------------------------------------------
-- Walking the rest of the program
-- ---------------------------------------------------------------------------

rewriteRule :: Candidates -> D.Rule -> D.Rule
rewriteRule cands r =
  r
    { D.guard = map (rewriteGuard cands) <$> r.guard,
      D.body = map (rewriteBodyGoal cands) <$> r.body
    }

rewriteFunction :: Candidates -> D.Function -> D.Function
rewriteFunction cands f = f {D.equations = map (rewriteEquation cands) f.equations}

rewriteEquation :: Candidates -> AnnP D.Equation -> AnnP D.Equation
rewriteEquation cands = fmap rw
  where
    rw eq =
      eq
        { D.guards = map (rewriteGuard cands) eq.guards,
          D.prelude = map (rewriteFunStmt cands) eq.prelude,
          D.rhs = rewriteExpr cands eq.rhs
        }

rewriteGuard :: Candidates -> D.Guard -> D.Guard
rewriteGuard cands g = case g of
  D.GuardEqual a b -> D.GuardEqual (rewriteExpr cands a) (rewriteExpr cands b)
  D.GuardMatch e n w -> D.GuardMatch (rewriteExpr cands e) n w
  D.GuardGetArg t e w -> D.GuardGetArg t (rewriteExpr cands e) w
  D.GuardExpr e -> D.GuardExpr (rewriteExpr cands e)

rewriteBodyGoal :: Candidates -> D.BodyGoal -> D.BodyGoal
rewriteBodyGoal cands g = case g of
  D.BodyTrue -> D.BodyTrue
  D.BodyTell qn args -> D.BodyTell qn (map (rewriteExpr cands) args)
  D.BodyUnify a b -> D.BodyUnify (rewriteExpr cands a) (rewriteExpr cands b)
  D.BodyHostStmt f args -> D.BodyHostStmt f (map (rewriteExpr cands) args)
  D.BodyIs v e -> D.BodyIs v (rewriteIsRhs cands e)
  D.BodyCall qn args -> case rewriteStmtCall cands qn args of
    KeptCall qn' args' -> D.BodyCall qn' args'
    SubstHost f args' -> D.BodyHostStmt f args'
    SubstCall qn' args' -> D.BodyCall qn' args'
    SubstApply f args' -> D.BodyApply f args'
  D.BodyApply f args -> D.BodyApply (rewriteExpr cands f) (map (rewriteExpr cands) args)
  D.BodyOr branches -> D.BodyOr (NE.map (map (rewriteBodyGoal cands)) branches)

rewriteFunStmt :: Candidates -> D.FunStmt -> D.FunStmt
rewriteFunStmt cands s = case s of
  D.FunIs v e -> D.FunIs v (rewriteIsRhs cands e)
  D.FunHostStmt f args -> D.FunHostStmt f (map (rewriteExpr cands) args)
  D.FunCall qn args -> case rewriteStmtCall cands qn args of
    KeptCall qn' args' -> D.FunCall qn' args'
    SubstHost f args' -> D.FunHostStmt f args'
    SubstCall qn' args' -> D.FunCall qn' args'
    SubstApply f args' -> D.FunApply f args'
  D.FunApply f args -> D.FunApply (rewriteExpr cands f) (map (rewriteExpr cands) args)

-- | The outcome of trying to inline a statement-position call
-- (@D.BodyCall@ \/ @D.FunCall@: a call whose result is discarded). A
-- statement is one of exactly three shapes
-- ('YCHR.Internal.Desugared.BodyGoal' \/ 'YCHR.Internal.Desugared.FunStmt'
-- have no "evaluate this expression and discard it" case), so
-- substitution only applies here when the candidate's body, after
-- substitution, is itself one of the matching three 'R.Expr' shapes.
-- Any other shape — a bare constructor or variable, say — has no
-- statement-position counterpart to become, so the call is kept.
data StmtCallResult
  = KeptCall QualifiedName [R.Expr]
  | SubstHost Text [R.Expr]
  | SubstCall QualifiedName [R.Expr]
  | SubstApply R.Expr [R.Expr]

rewriteStmtCall :: Candidates -> QualifiedName -> [R.Expr] -> StmtCallResult
rewriteStmtCall cands qn args =
  let args' = map (rewriteExpr cands) args
   in case Map.lookup qn cands of
        Nothing -> KeptCall qn args'
        Just cand -> case trySubstitute cand args' of
          Just (R.HostExpr f innerArgs) -> SubstHost f innerArgs
          Just (R.CallExpr qn' innerArgs) -> SubstCall qn' innerArgs
          Just (R.ApplyExpr f innerArgs) -> SubstApply f innerArgs
          _ -> KeptCall qn args'
