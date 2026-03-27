{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

-- | Meta-level host call registry.
--
-- Provides host functions that require access to modules outside the
-- interpreter, such as the pretty-printer. In the future this module
-- will contain meta-programming primitives like @read_term@,
-- @write_term@, and @call@.
module YCHR.Meta
  ( metaHostCallRegistry,
    valueToTerm,
  )
where

import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Effectful (Eff, runEff, type (:>))
import YCHR.Pretty (prettyTerm)
import YCHR.Runtime.Interpreter (HostCallRegistry)
import YCHR.Runtime.Types (RuntimeVal (..), SuspensionId (..), Value (..))
import YCHR.Runtime.Var (Unify, deref, runUnify)
import YCHR.Types (Term (..))
import YCHR.Types qualified as Types
import YCHR.VM (Name (..))

-- | Convert a runtime 'Value' to a surface 'Term', dereferencing logical
-- variables. Unbound variables are rendered as 'VarTerm varName'.
valueToTerm :: (Unify :> es) => Text -> Value -> Eff es Term
valueToTerm varName v = do
  v' <- deref v
  case v' of
    VInt n -> pure (IntTerm n)
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

-- | Host call registry providing meta-level operations that depend on
-- modules outside the interpreter (e.g. the pretty-printer).
metaHostCallRegistry :: HostCallRegistry
metaHostCallRegistry =
  Map.fromList
    [ ( Name "print",
        \args -> do
          strs <- mapM prettyRuntimeVal args
          mapM_ putStrLn strs
          pure (RVal (VBool True))
      )
    ]
