{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Meta-level host call registry.
--
-- Provides host functions that require access to modules outside the
-- interpreter, such as the pretty-printer and @read_term_from_string@.
module YCHR.Meta
  ( metaHostCallRegistry,
    valueToTerm,
  )
where

import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, gets, modify')
import Data.Foldable (toList)
import Data.Map.Strict qualified as Map
import Data.Text (Text, pack)
import Data.Text qualified as T
import YCHR.Parser (builtinOps, parseTermWith)
import YCHR.Pretty (prettyTerm)
import YCHR.Runtime.Monad (Chr)
import YCHR.Runtime.Registry (HostCallFn (..), HostCallRegistry, unit, valueList)
import YCHR.Runtime.Store (Suspension (..), getAllStoredConstraints, isSuspAlive)
import YCHR.Runtime.Types (Value (..), VarId)
import YCHR.Runtime.Var (deref, getVarId, newVar)
import YCHR.Types (Term (..), flattenName)
import YCHR.Types qualified as Types
import YCHR.VM (Name (..))

-- | Convert a runtime 'Value' to a surface 'Term', dereferencing logical
-- variables. An unbound variable is rendered as 'VarTerm' carrying the
-- alias name from the supplied map (looked up by 'VarId'), or as
-- 'Wildcard' when the variable has no alias.
valueToTerm :: Map.Map VarId Text -> Value -> Chr Term
valueToTerm aliases v = do
  v' <- deref v
  case v' of
    VInt n -> pure (IntTerm n)
    VFloat n -> pure (FloatTerm n)
    VText s -> pure (TextTerm s)
    VBool True -> pure (CompoundTerm (Types.Unqualified "true") [])
    VBool False -> pure (CompoundTerm (Types.Unqualified "false") [])
    VWildcard -> pure Wildcard
    -- 'VAtom' is the runtime form of every 0-arity value (atoms and
    -- declared 0-arity ctors collapse to it; see 'Compile.compileTerm').
    -- Recover the surface qualification from the @m__n@ mangled functor
    -- so the pretty-printer renders qualified atoms as @m:n@. Two
    -- guards: (a) the prefix must be non-empty (rejects symbols that
    -- begin with @__@), (b) the suffix must not contain @__@ itself
    -- (rejects user-quoted atoms with unicode escapes @__uXXXX__@,
    -- whose internal @__@ would otherwise be mistaken for a module
    -- separator — the renamer guarantees both module and base names
    -- are @__@-free /for ASCII identifiers/).
    --
    -- Known limitation: a qualified ctor whose base name contains
    -- non-ASCII (e.g. @:- chr_type t ---> 'naïve'@ in module @m@) is
    -- mangled to @"m__na__uef__ve"@ and the suffix-@__@-check refuses
    -- the split, so the qualifier is lost in display. This case has no
    -- test coverage and was bug-for-bug broken pre-refactor (the
    -- qualified form was preserved but the unicode escape was never
    -- decoded). A proper fix needs a richer separator in 'vmName'.
    VAtom s
      | (m, rest) <- T.breakOn "__" s,
        not (T.null m),
        not (T.null rest),
        let n = T.drop 2 rest,
        not (T.isInfixOf "__" n) ->
          pure (CompoundTerm (Types.Qualified m n) [])
      | otherwise -> pure (CompoundTerm (Types.Unqualified s) [])
    VTerm "prelude__." ts ->
      CompoundTerm (Types.Unqualified ".") <$> traverse (valueToTerm aliases) ts
    -- A term whose functor contains @__@ is the runtime form of a
    -- qualified compound (the mangled form @m__n@). See the matching
    -- guard on 'VAtom' above for why the suffix must be @__@-free.
    VTerm f ts
      | (m, rest) <- T.breakOn "__" f,
        not (T.null m),
        not (T.null rest),
        let n = T.drop 2 rest,
        not (T.isInfixOf "__" n) ->
          CompoundTerm (Types.Qualified m n)
            <$> traverse (valueToTerm aliases) ts
    VTerm f ts -> CompoundTerm (Types.Unqualified f) <$> traverse (valueToTerm aliases) ts
    VVar _ -> do
      mvid <- getVarId v'
      case mvid >>= (`Map.lookup` aliases) of
        Just name -> pure (VarTerm name)
        Nothing -> pure Wildcard

-- | Pretty-print a 'Value' using the surface pretty-printer.
-- Dereferences logical variables before rendering. Runs inside 'Chr'
-- because dereferencing reads variable state from the session.
prettyValue :: Value -> Chr String
prettyValue v = prettyTerm <$> valueToTerm Map.empty v

-- | Convert a parsed 'Term' to a runtime 'Value', creating fresh logical
-- variables. The same variable name within a term maps to the same fresh
-- variable (tracked via 'StateT').
termToValue :: Term -> StateT (Map.Map Text Value) Chr Value
termToValue (VarTerm name) = do
  existing <- gets (Map.lookup name)
  case existing of
    Just v -> pure v
    Nothing -> do
      v <- lift newVar
      modify' (Map.insert name v)
      pure v
termToValue (IntTerm n) = pure (VInt n)
termToValue (FloatTerm n) = pure (VFloat n)
termToValue (TextTerm s) = pure (VText s)
termToValue Wildcard = pure VWildcard
termToValue (CompoundTerm name []) = pure (VAtom (flattenName name))
termToValue (CompoundTerm name args) = do
  args' <- traverse termToValue args
  pure (VTerm (flattenName name) args')

-- | Host call registry providing meta-level operations that depend on
-- modules outside the interpreter (e.g. the pretty-printer).
metaHostCallRegistry :: HostCallRegistry
metaHostCallRegistry =
  Map.fromList
    [ ( Name "print",
        HostCallFn $ \args -> do
          strs <- mapM prettyValue args
          liftIO (mapM_ putStrLn strs)
          pure unit
      ),
      ( Name "write_term_to_string",
        HostCallFn $ \case
          [arg] -> do
            s <- prettyValue arg
            pure (VText (pack s))
          _ -> error "write_term_to_string: expected 1 argument"
      ),
      ( Name "read_term_from_string",
        HostCallFn $ \case
          [VText s] ->
            case parseTermWith builtinOps "<read_term_from_string>" s of
              Left err -> error $ "read_term_from_string: " ++ show err
              Right term -> evalStateT (termToValue term) Map.empty
          _ -> error "read_term_from_string: expected 1 Text argument"
      ),
      ( Name "print_store",
        HostCallFn $ \_ -> do
          groups <- getAllStoredConstraints
          lines_ <- concat <$> traverse renderGroup groups
          liftIO (mapM_ putStrLn lines_)
          pure unit
      ),
      ( Name "write_store_to_list",
        HostCallFn $ \_ -> do
          groups <- getAllStoredConstraints
          susps <- concat <$> traverse suspsOfGroup groups
          pure (valueList susps)
      )
    ]
  where
    renderGroup (tyName, susps) =
      fmap concat . traverse (renderSusp tyName) . toList $ susps
    renderSusp tyName susp@Suspension {args = sargs} = do
      alive <- isSuspAlive susp
      if not alive
        then pure []
        else do
          argTerms <- traverse (valueToTerm Map.empty) sargs
          pure [prettyTerm (CompoundTerm tyName argTerms)]
    suspsOfGroup (tyName, susps) =
      fmap concat . traverse (suspAsValue tyName) . toList $ susps
    suspAsValue tyName susp@Suspension {args = sargs} = do
      alive <- isSuspAlive susp
      if not alive
        then pure []
        else do
          args' <- traverse deepDeref sargs
          pure [constraintAsValue tyName args']
    constraintAsValue (Types.Unqualified t) args' = VTerm t args'
    constraintAsValue (Types.Qualified m f) args' =
      VTerm ":" [VAtom m, VTerm f args']
    deepDeref v = do
      v' <- deref v
      case v' of
        VTerm f xs -> VTerm f <$> traverse deepDeref xs
        _ -> pure v'
