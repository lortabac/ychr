{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Internal.Rename.Macro
-- Description : Pure mechanics for macro expansion (@:- macro@).
--
-- The parts of macro expansion that need neither the renamer's monad
-- nor its visibility environments: match a use's arguments against a
-- clause's head patterns, instantiate the selected clause's body
-- (substituting, freshening and evaluating the construction primitives
-- in one pass), compare two uses up to variable renaming for the
-- repeat check, split a term on top-level @,@, and decide whether a
-- term in head position is a constraint conjunct. Deciding /whether/ a
-- name is a macro needs the per-module visibility environments, so it
-- lives in "YCHR.Internal.Rename".
--
-- See [the macro reference](../../../../docs/reference/macros.md) for
-- the user-facing specification this module implements.
module YCHR.Internal.Rename.Macro
  ( -- * Clause selection
    matchClause,
    ClauseMatch (..),
    selectClause,

    -- * Instantiation
    instantiateClause,
    instantiateBody,
    PrimitiveError (..),
    PrimitiveOperand (..),
    primitiveOfOperand,
    isPrimitiveName,
    primitivesIn,

    -- * Termination
    macroDepthLimit,
    macroExpansionBudget,
    isVariant,
    termsSize,

    -- * Expansion steps
    MacroUse (..),
    newMacroUse,
    stepKey,
    MacroState (..),
    initialMacroState,
    freshBudget,
    UseFailure (..),
    UseResult (..),
    expandStep,

    -- * Conjunctions
    flattenConj,
    goalsToChain,

    -- * Head-position validity
    HeadConjunctResult (..),
    headConjunct,

    -- * Definition-time checks
    qualifiedRefsIn,
    varCounts,

    -- * Diagnostics
    renderExpansionChain,
  )
where

import Control.Monad (foldM, unless)
import Control.Monad.Trans.State.Strict (State, StateT, evalState, get, modify', put)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Text (Text)
import Data.Text qualified as Text
import YCHR.Internal.Parsed
  ( AnnP (..),
    ExpansionStep (..),
    MacroClause (..),
    MacroDef (..),
    SourceLoc (..),
  )
import YCHR.Internal.Types
  ( Constraint (..),
    Identifier (..),
    Name (..),
    QualifiedIdentifier (..),
    QualifiedName (..),
    Term (..),
    UnqualifiedIdentifier (..),
  )

-- ---------------------------------------------------------------------------
-- Clause selection
-- ---------------------------------------------------------------------------

-- | Match the arguments of a use against a clause's head patterns.
-- Matching is syntactic and one-way: it compares each pattern with the
-- argument /as written/, never expanding, evaluating or resolving it.
--
-- * @_@ ('Wildcard') matches anything and binds nothing.
-- * A variable binds to the argument on its first occurrence; a
--   repeated variable matches only an /identical/ term ('identical').
-- * A use-site variable or @_@ matches only a variable pattern or @_@:
--   matching never binds a use-site variable.
-- * Constants match the same constant; compounds match the same name
--   ('Unqualified' and 'Qualified' names differ, so names are compared
--   as written) and arity, argument by argument.
--
-- Returns the bindings of the head variables, or 'Nothing'.
matchClause :: [Term] -> [Term] -> Maybe (Map Text Term)
matchClause pats args
  | length pats /= length args = Nothing
  | otherwise = foldM matchOne Map.empty (zip pats args)

matchOne :: Map Text Term -> (Term, Term) -> Maybe (Map Text Term)
matchOne env (pat, arg) = case pat of
  Wildcard -> Just env
  VarTerm v -> case Map.lookup v env of
    Nothing -> Just (Map.insert v arg env)
    Just bound
      | identical bound arg -> Just env
      | otherwise -> Nothing
  -- A qualified pattern whose module or name is a variable (@lib:F@,
  -- @M:f@) is the parser's unqualified @:@ compound, while a qualified
  -- argument written literally (@lib:x@) is a 'Qualified' name: match
  -- the two part by part.
  CompoundTerm (Unqualified ":") [pm, pf]
    | CompoundTerm (Qualified m n) as <- arg ->
        foldM
          matchOne
          env
          [ (pm, CompoundTerm (Unqualified m) []),
            (pf, CompoundTerm (Unqualified n) as)
          ]
  CompoundTerm pn pargs -> case arg of
    CompoundTerm an aargs
      | pn == an && length pargs == length aargs ->
          foldM matchOne env (zip pargs aargs)
    _ -> Nothing
  _ -> if pat == arg then Just env else Nothing

-- | Two argument terms are identical: the same structure, atoms and
-- variables. A term containing @_@ is never identical to anything,
-- since each @_@ is a distinct anonymous variable.
identical :: Term -> Term -> Bool
identical a b = a == b && not (hasWildcard a)
  where
    hasWildcard Wildcard = True
    hasWildcard (CompoundTerm _ ts) = any hasWildcard ts
    hasWildcard _ = False

-- | A clause whose head matched a use, with the bindings of its head
-- variables.
data ClauseMatch = ClauseMatch
  { bindings :: Map Text Term,
    clause :: MacroClause
  }

-- | The first clause, top to bottom, whose head matches the arguments.
selectClause :: [AnnP MacroClause] -> [Term] -> Maybe ClauseMatch
selectClause clauses args =
  case [ ClauseMatch b c.node
       | c <- clauses,
         Just b <- [matchClause c.node.params args]
       ] of
    (hit : _) -> Just hit
    [] -> Nothing

-- ---------------------------------------------------------------------------
-- Instantiation
-- ---------------------------------------------------------------------------

-- | An operand of a construction primitive that breaks its rules.
data PrimitiveError = PrimitiveError
  { operand :: PrimitiveOperand,
    -- | The term the operand received.
    received :: Term
  }
  deriving (Eq, Show)

-- | The operand of a construction primitive that an error is about.
data PrimitiveOperand
  = -- | @F@ in @'$compound'(F, L)@: not an atom or a qualified name.
    CompoundFunctor
  | -- | @L@ in @'$compound'(F, L)@: not a proper list.
    CompoundArgs
  | -- | The operand of @'$atom'@: not a proper, non-empty list.
    AtomParts
  | -- | One part of @'$atom'@: not an unqualified atom or an integer.
    AtomPart
  | -- | The concatenation built by @'$atom'@: empty, or containing a
    -- reserved infix (@__@ or @%%u@).
    AtomResult
  deriving (Eq, Show)

-- | The name of the primitive an operand belongs to.
primitiveOfOperand :: PrimitiveOperand -> Text
primitiveOfOperand op = case op of
  CompoundFunctor -> "$compound"
  CompoundArgs -> "$compound"
  _ -> "$atom"

-- | Whether a name and arity denote a construction primitive:
-- unqualified @'$compound'\/2@ or @'$atom'\/1@.
isPrimitiveName :: Name -> Int -> Bool
isPrimitiveName (Unqualified "$compound") 2 = True
isPrimitiveName (Unqualified "$atom") 1 = True
isPrimitiveName _ _ = False

-- | Every construction primitive occurring in a term, at any depth, as
-- name and arity. Used to reject primitives in macro head patterns.
primitivesIn :: Term -> [Identifier]
primitivesIn (CompoundTerm n args) =
  [Identifier n (length args) | isPrimitiveName n (length args)]
    ++ concatMap primitivesIn args
primitivesIn _ = []

-- | Instantiate a clause's body at one use, in one pass over the body as
-- written (the template):
--
-- * a head variable is replaced with the argument term it was bound to,
--   and the pass never descends into that term, so a primitive that
--   arrives through an argument is never evaluated;
-- * every other variable is renamed to a fresh one, so it cannot clash
--   with any variable of the use site; @_@ stays a distinct anonymous
--   variable;
-- * a compound of the template is rebuilt once its arguments are done,
--   and a construction primitive is evaluated then, so primitives are
--   evaluated innermost first. The pass goes everywhere, @quote\/1@
--   included, because the template is not code.
--
-- Each resulting element is then flattened on @,@, so an element that
-- is itself a conjunction is spliced goal by goal.
--
-- Fresh names come from 'seed', distinct for every call within one
-- renaming run ('MacroState.nextSeed'), not from the use site's
-- 'SourceLoc': all goals of one rule section share one 'SourceLoc'
-- (see 'YCHR.Internal.Parsed.Rule'), so two uses there would alias
-- their fresh variables.
instantiateClause :: Int -> ClauseMatch -> Either PrimitiveError [Term]
instantiateClause seed m =
  concatMap flattenConj <$> instantiateBody "_macro_" seed m

-- | 'instantiateClause' without splitting on @,@ (a clause with a
-- conjunction is still one clause). Fresh variables are
-- @\<prefix\>\<seed\>_\<name\>@. Each macro kind has its own prefix
-- and seed counter, so they can't clash.
instantiateBody :: Text -> Int -> ClauseMatch -> Either PrimitiveError [Term]
instantiateBody prefix seed m = traverse go m.clause.body
  where
    binds = m.bindings
    seedKey = Text.pack (show seed)
    freshen v = prefix <> seedKey <> "_" <> v
    go t = case t of
      VarTerm v -> Right (fromMaybe (VarTerm (freshen v)) (Map.lookup v binds))
      CompoundTerm f as -> do
        as' <- traverse go as
        evalTemplateCompound f as'
      _ -> Right t

-- | Rebuild one compound of a template after its arguments have been
-- instantiated: evaluate a construction primitive, and normalize a
-- @M:f(...)@ whose module or name was a head variable into the
-- qualified form the parser gives a qualified name written literally.
evalTemplateCompound :: Name -> [Term] -> Either PrimitiveError Term
evalTemplateCompound f args = case (f, args) of
  (Unqualified "$compound", [fn, l]) -> do
    name <- case fn of
      CompoundTerm n [] -> Right n
      _ -> case qualifiedAtom fn of
        Just n -> Right n
        Nothing -> Left (PrimitiveError CompoundFunctor fn)
    xs <- maybe (Left (PrimitiveError CompoundArgs l)) Right (properList l)
    Right (CompoundTerm name xs)
  (Unqualified "$atom", [l]) -> case properList l of
    Just parts@(_ : _) -> do
      texts <- traverse atomPart parts
      let t = mconcat texts
      if Text.null t || "__" `Text.isInfixOf` t || "%%u" `Text.isInfixOf` t
        then Left (PrimitiveError AtomResult l)
        else Right (CompoundTerm (Unqualified t) [])
    _ -> Left (PrimitiveError AtomParts l)
  (Unqualified ":", [CompoundTerm (Unqualified m) [], CompoundTerm (Unqualified n) as]) ->
    Right (CompoundTerm (Qualified m n) as)
  _ -> Right (CompoundTerm f args)
  where
    atomPart (CompoundTerm (Unqualified a) []) = Right a
    atomPart (IntTerm n) = Right (Text.pack (show n))
    atomPart p = Left (PrimitiveError AtomPart p)
    qualifiedAtom
      ( CompoundTerm
          (Unqualified ":")
          [CompoundTerm (Unqualified m) [], CompoundTerm (Unqualified n) []]
        ) =
        Just (Qualified m n)
    qualifiedAtom _ = Nothing

-- | The elements of a proper list term (@'.'\/2@ cells ending in @[]@).
properList :: Term -> Maybe [Term]
properList (CompoundTerm (Unqualified "[]") []) = Just []
properList (CompoundTerm (Unqualified ".") [h, t]) = (h :) <$> properList t
properList _ = Nothing

-- ---------------------------------------------------------------------------
-- Termination
-- ---------------------------------------------------------------------------

-- | The maximum depth of a chain of nested macro expansions. A deeper
-- chain is 'YCHR.Internal.Rename.MacroExpansionTooDeep'.
macroDepthLimit :: Int
macroDepthLimit = 1000

-- | The maximum number of expansions that one top-level use (a use
-- written in a rule head, a rule body or a query, not produced by
-- another expansion) may cause, nested ones included. A larger
-- expansion is 'YCHR.Internal.Rename.MacroExpansionTooLarge'. The depth
-- limit alone bounds how deep expansion goes but not how wide: a macro
-- with two recursive uses per clause would otherwise do @2^1000@ steps.
macroExpansionBudget :: Int
macroExpansionBudget = 100000

-- | Whether two argument lists are identical up to a renaming of
-- variables (a bijection between their variables). Each @_@ counts as a
-- distinct variable of its own. Used by the repeat check: a use reached
-- again, while it is still being expanded, with the same macro and
-- variant arguments can never finish expanding.
isVariant :: [Term] -> [Term] -> Bool
isVariant xs ys =
  length xs == length ys
    && isJust (foldM step (Map.empty, Map.empty) pairs)
  where
    pairs = zip (numberWildcards xs) (numberWildcards ys)
    step maps (a, b) = case (a, b) of
      (VarTerm u, VarTerm v) -> bind maps u v
      (CompoundTerm m as, CompoundTerm n bs)
        | m == n && length as == length bs -> foldM step maps (zip as bs)
      (VarTerm _, _) -> Nothing
      (_, VarTerm _) -> Nothing
      _ -> if a == b then Just maps else Nothing
    bind (fwd, bwd) u v = case (Map.lookup u fwd, Map.lookup v bwd) of
      (Nothing, Nothing) -> Just (Map.insert u v fwd, Map.insert v u bwd)
      (Just v', Just u') | v' == v && u' == u -> Just (fwd, bwd)
      _ -> Nothing

-- | Replace each @_@ with a distinct variable whose name no source
-- variable can have.
numberWildcards :: [Term] -> [Term]
numberWildcards ts = evalState (traverse go ts) (0 :: Int)
  where
    go :: Term -> State Int Term
    go t = case t of
      Wildcard -> do
        n <- get
        put (n + 1)
        pure (VarTerm ("$wildcard" <> Text.pack (show n)))
      CompoundTerm f as -> CompoundTerm f <$> traverse go as
      _ -> pure t

-- | The number of nodes in a list of terms. Variant argument lists have
-- the same size, so the repeat check compares sizes first and runs
-- 'isVariant' only on candidates of equal size.
termsSize :: [Term] -> Int
termsSize = sum . map size
  where
    size (CompoundTerm _ as) = 1 + termsSize as
    size _ = 1

-- ---------------------------------------------------------------------------
-- Expansion steps
-- ---------------------------------------------------------------------------

-- | One use in the chain of macro expansions in progress. Both macro
-- kinds keep their chain as a list of these, innermost first.
data MacroUse = MacroUse
  { -- | The macro and where it is used (for a nested use, the
    -- outermost use site).
    step :: ExpansionStep,
    -- | The use's arguments, as written, for the repeat check.
    arguments :: [Term],
    -- | 'termsSize' of 'arguments', compared before 'isVariant'.
    argumentsSize :: Int,
    -- | The number of uses in the chain, this one included.
    depth :: Int
  }

-- | A use of macro @qn@ with these arguments, used at @site@, inside
-- @chain@.
newMacroUse :: QualifiedName -> [Term] -> SourceLoc -> [MacroUse] -> MacroUse
newMacroUse qn args site chain =
  MacroUse
    { step =
        ExpansionStep
          { macroModule = qn.moduleName,
            macroName = qn.baseName,
            macroArity = length args,
            site = site
          },
      arguments = args,
      argumentsSize = termsSize args,
      depth = case chain of
        (u : _) -> u.depth + 1
        [] -> 1
    }

-- | The module, name and arity of a chain entry.
stepKey :: ExpansionStep -> QualifiedIdentifier
stepKey s = QualifiedIdentifier s.macroModule s.macroName s.macroArity

-- | The state macro expansion threads through one run.
data MacroState = MacroState
  { -- | The seed the next instantiation freshens its variables with.
    nextSeed :: Int,
    -- | Expansions the current top-level use may still cause (see
    -- 'macroExpansionBudget').
    remaining :: Int,
    -- | Set once the current top-level use hit a limit, or failed in a
    -- nested use: the rest of its expansion is skipped without further
    -- diagnostics, so a macro that branches as it recurses reports the
    -- problem once.
    abandoned :: Bool
  }

-- | The state a run starts with.
initialMacroState :: MacroState
initialMacroState =
  MacroState {nextSeed = 0, remaining = macroExpansionBudget, abandoned = False}

-- | Start a top-level use: a full budget, nothing abandoned.
freshBudget :: MacroState -> MacroState
freshBudget st = st {remaining = macroExpansionBudget, abandoned = False}

-- | Why a macro use did not expand.
data UseFailure
  = -- | The chain is already 'macroDepthLimit' uses deep.
    UseTooDeep
  | -- | The top-level use has already caused 'macroExpansionBudget'
    -- expansions.
    UseTooLarge
  | -- | The same macro is being expanded higher up the chain with
    -- variant arguments ('isVariant').
    UseCycle
  | -- | No clause's head matches the arguments.
    UseNoClause
  | -- | A construction primitive in the selected clause got a bad
    -- operand.
    UseBadPrimitive PrimitiveError

-- | The outcome of 'expandStep'.
data UseResult a
  = -- | The top-level use was abandoned earlier: report nothing.
    UseSkipped
  | -- | Report the failure, with this chain.
    UseFailed [MacroUse] UseFailure
  | -- | The instantiated clause body.
    UseExpanded a

-- | One expansion step, the same for both macro kinds: check the limits
-- and the repeat check, select a clause and instantiate it with a fresh
-- seed. @chain@ is the chain the use is in, without the use itself. A
-- bad primitive is reported with the use on the chain, every other
-- failure without it.
--
-- A limit abandons the rest of the top-level use, and so does any
-- failure in a nested use: a macro that branches as it recurses would
-- otherwise report the same error once per branch.
expandStep ::
  (Monad m) =>
  (Int -> ClauseMatch -> Either PrimitiveError a) ->
  [MacroUse] ->
  MacroUse ->
  MacroDef ->
  StateT MacroState m (UseResult a)
expandStep instantiate chain use def = get >>= go
  where
    go st
      | st.abandoned = pure UseSkipped
      | use.depth > macroDepthLimit = abandon UseTooDeep
      | st.remaining <= 0 = abandon UseTooLarge
      | any repeats chain = failNested chain UseCycle
      | otherwise = case selectClause def.clauses use.arguments of
          Nothing -> failNested chain UseNoClause
          Just m -> do
            put st {nextSeed = st.nextSeed + 1, remaining = st.remaining - 1}
            case instantiate st.nextSeed m of
              Left pe -> failNested (use : chain) (UseBadPrimitive pe)
              Right x -> pure (UseExpanded x)
    abandon f = do
      modify' (\st -> st {abandoned = True})
      pure (UseFailed chain f)
    failNested c f = do
      unless (null chain) $ modify' (\st -> st {abandoned = True})
      pure (UseFailed c f)
    repeats u =
      stepKey u.step == stepKey use.step
        && u.argumentsSize == use.argumentsSize
        && isVariant u.arguments use.arguments

-- ---------------------------------------------------------------------------
-- Conjunctions
-- ---------------------------------------------------------------------------

-- | Split a term on the top-level @,@ operator, the same conjunction
-- 'YCHR.Internal.Parser.flattenComma' splits at the surface level,
-- but operating on the already-converted 'Term' representation a
-- macro body (and its instantiation) is held in.
flattenConj :: Term -> [Term]
flattenConj (CompoundTerm (Unqualified ",") [l, r]) = flattenConj l ++ flattenConj r
flattenConj t = [t]

-- | The inverse of 'flattenConj': rebuild a right-associated @,@ chain
-- from a list of goals, so a macro expansion that produced several
-- goals can be spliced back in wherever a single 'Term' is expected
-- (a disjunction branch). An empty list — a branch whose goals all
-- expanded to nothing — is @true@.
goalsToChain :: [Term] -> Term
goalsToChain [] = CompoundTerm (Unqualified "true") []
goalsToChain [t] = t
goalsToChain (t : ts) = CompoundTerm (Unqualified ",") [t, goalsToChain ts]

-- ---------------------------------------------------------------------------
-- Head-position validity
-- ---------------------------------------------------------------------------

-- | The outcome of classifying one goal produced by a head expansion:
-- either a constraint conjunct to splice into the head (kept or
-- removed, per the use site), or a term that cannot appear in a head
-- at all (a bare variable or literal, or one of the structural
-- operators @,@\/@;@\/@\\@\/@|@\/@->@\/@=@\/@is@ — a head is a
-- conjunction of constraints, not an arbitrary goal).
data HeadConjunctResult = HeadConjunctOk Constraint | HeadConjunctInvalid Term

-- | Classify one goal of a (flattened) head expansion. See
-- 'HeadConjunctResult'.
headConjunct :: Term -> HeadConjunctResult
headConjunct (CompoundTerm name args)
  | not (isStructuralName name) = HeadConjunctOk (Constraint name args)
  where
    isStructuralName (Unqualified n) = n `elem` structuralNames
    isStructuralName (Qualified _ _) = False
    structuralNames = [",", ";", "\\", "|", "->", "=", "is"]
headConjunct t = HeadConjunctInvalid t

-- ---------------------------------------------------------------------------
-- Definition-time checks
-- ---------------------------------------------------------------------------

-- | Every @(name, arity)@ pair referenced in the term as a compound
-- qualified with exactly the given module name, at any depth. Used by
-- the 'YCHR.Internal.Rename.MacroBodyNotExported' check: a macro
-- body's self-qualified references (@M:x@, where @M@ is the macro's
-- own declaring module) must each name something @M@ declares and
-- exports. A @'$compound'(M:f, [A1, ..., An])@ refers to @f\/n@, the
-- compound it builds, not to @f\/0@; with an argument list that is not
-- a proper list as written, the arity is unknown and @f@ is not
-- checked.
qualifiedRefsIn :: Text -> Term -> [UnqualifiedIdentifier]
qualifiedRefsIn self = go
  where
    go (CompoundTerm (Unqualified "$compound") [CompoundTerm (Qualified m n) [], l])
      | m == self = case properList l of
          Just xs -> UnqualifiedIdentifier n (length xs) : concatMap go xs
          -- The arity is not known until the macro is used.
          Nothing -> go l
    go (CompoundTerm (Qualified m n) args)
      | m == self = UnqualifiedIdentifier n (length args) : concatMap go args
      | otherwise = concatMap go args
    go (CompoundTerm _ args) = concatMap go args
    go _ = []

-- | How many times each variable occurs in a term, for the
-- 'YCHR.Internal.Rename.UnusedMacroParameter' warning.
varCounts :: Term -> Map Text Int
varCounts (VarTerm v) = Map.singleton v 1
varCounts (CompoundTerm _ args) = Map.unionsWith (+) (map varCounts args)
varCounts _ = Map.empty

-- ---------------------------------------------------------------------------
-- Diagnostics
-- ---------------------------------------------------------------------------

-- | Show a macro chain, innermost first, e.g. @"in the expansion of
-- aggregates:count\/2, used at graph.chr:4:3"@. Repeats of the same
-- macro become one line with a count. At most 'maxChainLines' lines,
-- plus one line counting the rest. Used by both macro kinds.
renderExpansionChain :: [ExpansionStep] -> [Text]
renderExpansionChain chain =
  let groups = runs chain
      shown = map renderGroup (take maxChainLines groups)
      hidden = sum (map (.count) (drop maxChainLines groups))
   in shown
        ++ [ "... and " <> tshow hidden <> " more enclosing expansions"
           | hidden > 0
           ]
  where
    runs [] = []
    runs (u : us) =
      let (same, rest) = span (\v -> stepKey v == stepKey u) us
       in ChainRun u (1 + length same) : runs rest
    renderGroup g
      | g.count == 1 =
          "in the expansion of " <> qn u <> ", used at " <> locText u.site
      | otherwise =
          "in "
            <> tshow g.count
            <> " nested expansions of "
            <> qn u
            <> ", innermost used at "
            <> locText u.site
      where
        u = g.innermost
    qn u = u.macroModule <> ":" <> u.macroName <> "/" <> tshow u.macroArity
    locText loc =
      Text.pack loc.file <> ":" <> tshow loc.line <> ":" <> tshow loc.col
    tshow :: (Show a) => a -> Text
    tshow = Text.pack . show

-- | Consecutive uses of the same macro in a chain: the innermost one
-- and how many there are.
data ChainRun = ChainRun
  { innermost :: ExpansionStep,
    count :: Int
  }

-- | Max lines 'renderExpansionChain' shows.
maxChainLines :: Int
maxChainLines = 10
