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
import Data.Char (chr)
import Data.Foldable (toList)
import Data.Map.Strict qualified as Map
import Data.Text (Text, pack)
import Data.Text qualified as T
import Numeric (readHex)
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
    -- Recover the surface name from the mangled functor produced by
    -- 'Compile.Names.vmName': @encodeText m <> "__" <> encodeText n@
    -- for qualified names, @encodeText n@ for unqualified.
    VAtom s -> pure (decodeName s [])
    VTerm "prelude__." ts ->
      CompoundTerm (Types.Unqualified ".") <$> traverse (valueToTerm aliases) ts
    VTerm f ts -> do
      ts' <- traverse (valueToTerm aliases) ts
      pure (decodeName f ts')
    VVar _ -> do
      mvid <- getVarId v'
      case mvid >>= (`Map.lookup` aliases) of
        Just name -> pure (VarTerm name)
        Nothing -> pure Wildcard

-- | Build a 'CompoundTerm' from a mangled functor text and already-decoded
-- argument terms. Splits @s@ into module/base parts (when present) using
-- 'decodeMangled' and turns each @%%u\<6 hex digits\>@ unicode escape
-- back into its source character.
decodeName :: Text -> [Term] -> Term
decodeName s args = case decodeMangled s of
  Just (m, n) ->
    CompoundTerm (Types.Qualified (decodeEscapes m) (decodeEscapes n)) args
  Nothing -> CompoundTerm (Types.Unqualified (decodeEscapes s)) args

-- | Inverse of 'Compile.Names.vmName'. Returns @Just (mod, base)@ when
-- the input is a qualified mangled name, @Nothing@ when it is
-- unqualified.
--
-- The encoding @encodeText m \<\> "__" \<\> encodeText n@ is injective
-- because 'encodeText' never emits @__@ in its output (non-ASCII chars
-- use the @%%u\<6 hex\>@ marker instead) and the lexer rejects @__@
-- in source. So the only @__@ in the mangled form is the module/base
-- separator — finding it is a single 'T.breakOn' away.
--
-- A leading @__@ (e.g. compiler-internal @__lambda_3@) yields an empty
-- module prefix, which the caller treats as unqualified.
decodeMangled :: Text -> Maybe (Text, Text)
decodeMangled s = case T.breakOn "__" s of
  (_, rest) | T.null rest -> Nothing
  (m, _) | T.null m -> Nothing
  (m, rest) -> Just (m, T.drop 2 rest)

-- | Replace every @%%u\<6 hex digits\>@ escape in @s@ with the
-- corresponding character (inverse of 'Compile.Names.encodeText''s
-- non-ASCII case). 'encodeText' emits exactly six lowercase hex
-- digits per escape and never any closing delimiter; the decoder
-- mirrors that.
decodeEscapes :: Text -> Text
decodeEscapes = T.pack . go . T.unpack
  where
    go [] = []
    go ('%' : '%' : 'u' : a : b : c : d : e : f : rest)
      | all isLowerHexDigit hex,
        [(code, "")] <- readHex hex,
        isValidCodePoint code =
          chr code : go rest
      where
        hex = [a, b, c, d, e, f]
    go (c : cs) = c : go cs

    -- A valid Unicode scalar value is in [0, 0x10FFFF] and not in the
    -- surrogate range [0xD800, 0xDFFF]. 'encodeText' only emits scalar
    -- values, so a malformed input outside this range falls through
    -- as a literal char sequence instead of crashing 'chr'.
    isValidCodePoint code =
      code <= 0x10FFFF && not (code >= 0xD800 && code <= 0xDFFF)

isLowerHexDigit :: Char -> Bool
isLowerHexDigit c = (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')

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
