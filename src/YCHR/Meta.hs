{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

-- | Meta-level host call registry.
--
-- Provides host functions that require access to modules outside the
-- interpreter, such as the pretty-printer and @read_term_from_string@.
module YCHR.Meta
  ( metaHostCallRegistry,
    valueToTerm,
  )
where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, gets, modify')
import Data.Foldable (toList)
import Data.Map.Strict qualified as Map
import Data.Text (Text, pack)
import Effectful (Eff, liftIO, runEff, type (:>))
import YCHR.Parser (builtinOps, parseTermWith)
import YCHR.Pretty (prettyTerm)
import YCHR.Runtime.Registry (HostCallFn (..), HostCallRegistry, unit)
import YCHR.Runtime.Store (Suspension (..), getAllStoredConstraints, isSuspAlive)
import YCHR.Runtime.Types (RuntimeVal (..), SuspensionId (..), Value (..))
import YCHR.Runtime.Var (Unify, deref, newVar, runUnify)
import YCHR.Types (Term (..), flattenName)
import YCHR.Types qualified as Types
import YCHR.VM (Name (..))

-- | Convert a runtime 'Value' to a surface 'Term', dereferencing logical
-- variables. Unbound variables are rendered as 'VarTerm varName'.
valueToTerm :: (Unify :> es) => Text -> Value -> Eff es Term
valueToTerm varName v = do
  v' <- deref v
  case v' of
    VInt n -> pure (IntTerm n)
    VFloat n -> pure (FloatTerm n)
    VAtom s -> pure (AtomTerm s)
    VText s -> pure (TextTerm s)
    VBool True -> pure (AtomTerm "true")
    VBool False -> pure (AtomTerm "false")
    VWildcard -> pure Wildcard
    VTerm f ts -> CompoundTerm (Types.Unqualified f) <$> traverse (valueToTerm "_") ts
    VVar _ -> pure (VarTerm varName)

-- | Pretty-print a 'RuntimeVal' using the surface pretty-printer.
-- Dereferences logical variables before rendering.
prettyRuntimeVal :: RuntimeVal -> IO String
prettyRuntimeVal (RVal v) = runEff . runUnify $ prettyTerm <$> valueToTerm "_" v
prettyRuntimeVal (RConstraint (SuspensionId n)) = pure ("<constraint:" ++ show n ++ ">")

-- | Convert a parsed 'Term' to a runtime 'Value', creating fresh logical
-- variables. The same variable name within a term maps to the same fresh
-- variable (tracked via 'StateT').
termToValue :: (Unify :> es) => Term -> StateT (Map.Map Text Value) (Eff es) Value
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
termToValue (AtomTerm s) = pure (VAtom s)
termToValue (TextTerm s) = pure (VText s)
termToValue Wildcard = pure VWildcard
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
          strs <- liftIO (mapM prettyRuntimeVal args)
          liftIO (mapM_ putStrLn strs)
          pure unit
      ),
      ( Name "write_term_to_string",
        HostCallFn $ \case
          [arg] -> do
            s <- liftIO (prettyRuntimeVal arg)
            pure (RVal (VText (pack s)))
          _ -> error "write_term_to_string: expected 1 argument"
      ),
      ( Name "read_term_from_string",
        HostCallFn $ \case
          [RVal (VText s)] ->
            case parseTermWith builtinOps "<read_term_from_string>" s of
              Left err -> error $ "read_term_from_string: " ++ show err
              Right term -> RVal <$> evalStateT (termToValue term) Map.empty
          _ -> error "read_term_from_string: expected 1 Text argument"
      ),
      ( Name "print_store",
        HostCallFn $ \_ -> do
          groups <- getAllStoredConstraints
          lines_ <- concat <$> traverse renderGroup groups
          liftIO (mapM_ putStrLn lines_)
          pure unit
      )
    ]
  where
    renderGroup (tyName, susps) =
      fmap concat . traverse (renderSusp tyName) . toList $ susps
    renderSusp tyName susp = do
      alive <- isSuspAlive susp
      if not alive
        then pure []
        else do
          argTerms <- traverse (valueToTerm "_") susp.args
          pure [prettyTerm (CompoundTerm (Types.Unqualified tyName) argTerms)]
