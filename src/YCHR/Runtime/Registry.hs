{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Host call registry for the CHR runtime.
--
-- Provides a base registry of host language functions (arithmetic,
-- comparisons, string operations, type predicates) and generic helpers
-- for building custom host calls.
module YCHR.Runtime.Registry
  ( -- * Types (re-exported from "YCHR.Runtime.Monad")
    HostCallFn (..),
    HostCallRegistry,

    -- * Registry
    baseHostCallRegistry,

    -- * Utilities
    unit,

    -- * Value predicates
    isInteger,
    isFloat,
    isAtom,
    isBoolean,
    isString,
    isVar,
    isNonvar,

    -- * Generic helpers
    allM,
    collectVars,
    copyTerm,
    fromValueList,
    valueList,
  )
where

import Control.Monad.IO.Class (liftIO)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as T
import YCHR.Runtime.Error (runtimeErrorS)
import YCHR.Runtime.Monad (Chr, HostCallFn (..), HostCallRegistry)
import YCHR.Runtime.Types (Value (..), VarId)
import YCHR.Runtime.Var (deref, equal, getVarId, newVar, unifiable)
import YCHR.VM (Name (..))

-- ---------------------------------------------------------------------------
-- Registry
-- ---------------------------------------------------------------------------

-- | A base host call registry providing arithmetic, comparison, string,
-- and type predicate operations.
baseHostCallRegistry :: HostCallRegistry
baseHostCallRegistry =
  Map.fromList
    [ (Name "+", numArith2 (+) (+)),
      (Name "-", numArith2 (-) (-)),
      (Name "*", numArith2 (*) (*)),
      (Name "div", intArith2 div),
      (Name "mod", intArith2 mod),
      (Name "rem", intArith2 rem),
      (Name "/", floatArith2 (/)),
      (Name "<", numCmp (<) (<)),
      (Name ">", numCmp (>) (>)),
      (Name "=<", numCmp (<=) (<=)),
      (Name ">=", numCmp (>=) (>=)),
      (Name "==", valEq),
      (Name "float", typePred isFloat),
      (Name "int_to_float", toFloatFn),
      (Name "float_to_int", toIntFn),
      (Name "unifiable", unifiableHost),
      (Name "string_concat", stringConcat),
      (Name "string_length", stringLength),
      (Name "string_upper", stringUpper),
      (Name "string_lower", stringLower),
      (Name "__chr_error", chrError),
      (Name "write", writeStr),
      (Name "writeln", writeStrLn),
      (Name "integer", typePred isInteger),
      (Name "atom", typePred isAtom),
      (Name "boolean", typePred isBoolean),
      (Name "string", typePred isString),
      (Name "var", typePred isVar),
      (Name "nonvar", typePred isNonvar),
      (Name "ground", groundPred),
      (Name "term_variables", termVariablesPred),
      (Name "compound_to_list", compoundToList),
      (Name "list_to_compound", listToCompound),
      (Name "copy_term", copyTermHost)
    ]
  where
    numArith2 intOp floatOp = HostCallFn $ \case
      [VInt a, VInt b] -> pure (VInt (intOp a b))
      [VFloat a, VFloat b] -> pure (VFloat (floatOp a b))
      args ->
        runtimeErrorS $
          "arithmetic host call: expected 2 numeric arguments of same type, got "
            ++ show (length args)
    intArith2 op = HostCallFn $ \case
      [VInt a, VInt b] -> pure (VInt (op a b))
      args ->
        runtimeErrorS $
          "integer arithmetic host call: expected 2 Int arguments, got "
            ++ show (length args)
    floatArith2 op = HostCallFn $ \case
      [VFloat a, VFloat b] -> pure (VFloat (op a b))
      args ->
        runtimeErrorS $
          "float arithmetic host call: expected 2 Float arguments, got "
            ++ show (length args)
    numCmp intOp floatOp = HostCallFn $ \case
      [VInt a, VInt b] -> pure (VBool (intOp a b))
      [VFloat a, VFloat b] -> pure (VBool (floatOp a b))
      args ->
        runtimeErrorS $
          "comparison host call: expected 2 numeric arguments of same type, got "
            ++ show (length args)
    toFloatFn = HostCallFn $ \case
      [VInt n] -> pure (VFloat (fromIntegral n))
      [VFloat n] -> pure (VFloat n)
      _ -> runtimeErrorS "int_to_float: expected 1 numeric argument"
    toIntFn = HostCallFn $ \case
      [VFloat n] -> pure (VInt (truncate n))
      [VInt n] -> pure (VInt n)
      _ -> runtimeErrorS "float_to_int: expected 1 numeric argument"
    unifiableHost = HostCallFn $ \case
      [a, b] -> VBool <$> unifiable a b
      args ->
        runtimeErrorS $
          "unifiable host call: expected 2 arguments, got " ++ show (length args)
    valEq = HostCallFn $ \case
      [a, b] -> VBool <$> equal a b
      args ->
        runtimeErrorS $
          "== host call: expected 2 arguments, got " ++ show (length args)
    stringConcat = HostCallFn $ \case
      [VText a, VText b] -> pure (VText (a <> b))
      _ -> runtimeErrorS "string_concat: expected 2 Text arguments"
    stringLength = HostCallFn $ \case
      [VText s] -> pure (VInt (T.length s))
      _ -> runtimeErrorS "string_length: expected 1 Text argument"
    stringUpper = HostCallFn $ \case
      [VText s] -> pure (VText (T.toUpper s))
      _ -> runtimeErrorS "string_upper: expected 1 Text argument"
    stringLower = HostCallFn $ \case
      [VText s] -> pure (VText (T.toLower s))
      _ -> runtimeErrorS "string_lower: expected 1 Text argument"
    chrError = HostCallFn $ \_ -> runtimeErrorS "CHR runtime error: no matching equation"
    writeStr = HostCallFn $ \case
      [VText s] -> unit <$ liftIO (putStr (T.unpack s))
      _ -> runtimeErrorS "write: expected 1 Text argument"
    writeStrLn = HostCallFn $ \case
      [VText s] -> unit <$ liftIO (putStrLn (T.unpack s))
      _ -> runtimeErrorS "writeln: expected 1 Text argument"
    typePred p = HostCallFn $ \case
      [v] -> do
        v' <- deref v
        pure (VBool (p v'))
      _ -> runtimeErrorS "type predicate: expected 1 argument"
    groundPred = HostCallFn $ \case
      [v] -> VBool <$> isGround v
      _ -> runtimeErrorS "ground: expected 1 argument"
    isGround v = do
      v' <- deref v
      case v' of
        VVar _ -> pure False
        VWildcard -> pure False
        VTerm _ args -> allM isGround args
        _ -> pure True
    termVariablesPred = HostCallFn $ \case
      [v] -> do
        (vars, _) <- collectVars Set.empty v
        pure (valueList vars)
      _ -> runtimeErrorS "term_variables: expected 1 argument"
    compoundToList = HostCallFn $ \case
      [VTerm f args] -> pure (valueList (VAtom f : args))
      _ -> runtimeErrorS "compound_to_list: expected 1 compound term argument"
    listToCompound = HostCallFn $ \case
      [list] -> case fromValueList list of
        Just (VAtom f : args) -> pure (VTerm f args)
        _ -> runtimeErrorS "list_to_compound: expected a non-empty list with an atom head"
      _ -> runtimeErrorS "list_to_compound: expected 1 list argument"
    copyTermHost = HostCallFn $ \case
      [v] -> copyTerm v
      _ -> runtimeErrorS "copy_term: expected 1 argument"

-- ---------------------------------------------------------------------------
-- Utilities
-- ---------------------------------------------------------------------------

-- | The unit return value for host calls that are only used for side effects.
unit :: Value
unit = VAtom "()"

-- ---------------------------------------------------------------------------
-- Value predicates
-- ---------------------------------------------------------------------------

isInteger :: Value -> Bool
isInteger (VInt _) = True
isInteger _ = False

isFloat :: Value -> Bool
isFloat (VFloat _) = True
isFloat _ = False

isAtom :: Value -> Bool
isAtom (VAtom _) = True
isAtom _ = False

isBoolean :: Value -> Bool
isBoolean (VBool _) = True
isBoolean _ = False

isString :: Value -> Bool
isString (VText _) = True
isString _ = False

isVar :: Value -> Bool
isVar (VVar _) = True
isVar VWildcard = True
isVar _ = False

isNonvar :: Value -> Bool
isNonvar = not . isVar

-- ---------------------------------------------------------------------------
-- Generic helpers
-- ---------------------------------------------------------------------------

-- | Deep-copy a term, replacing all unbound variables with fresh ones.
-- Preserves sharing: the same original variable always maps to the same
-- fresh variable across the entire copied term.
copyTerm :: Value -> Chr Value
copyTerm val = fst <$> go Map.empty val
  where
    go cache v = do
      v' <- deref v
      case v' of
        VVar _ -> do
          mid <- getVarId v'
          case mid of
            Just vid -> case Map.lookup vid cache of
              Just fresh -> pure (fresh, cache)
              Nothing -> do
                fresh <- newVar
                pure (fresh, Map.insert vid fresh cache)
            Nothing -> pure (v', cache)
        VWildcard -> do
          fresh <- newVar
          pure (fresh, cache)
        VTerm f args -> do
          (args', cache') <- goMany cache args
          pure (VTerm f args', cache')
        other -> pure (other, cache)

    goMany cache [] = pure ([], cache)
    goMany cache (x : xs) = do
      (x', cache') <- go cache x
      (xs', cache'') <- goMany cache' xs
      pure (x' : xs', cache'')

-- | Collect all unique unbound variables in a term, traversing into
-- compound term arguments. Wildcards are replaced with fresh variables.
-- Returns the collected variables and the updated set of seen 'VarId's.
collectVars ::
  Set.Set VarId ->
  Value ->
  Chr ([Value], Set.Set VarId)
collectVars seen v = do
  v' <- deref v
  case v' of
    VVar _ -> do
      mid <- getVarId v'
      case mid of
        Just vid
          | Set.member vid seen -> pure ([], seen)
          | otherwise -> pure ([v'], Set.insert vid seen)
        Nothing -> pure ([], seen)
    VWildcard -> do
      fresh <- newVar
      pure ([fresh], seen)
    VTerm _ args -> collectVarsMany seen args
    _ -> pure ([], seen)
  where
    collectVarsMany s [] = pure ([], s)
    collectVarsMany s (x : xs) = do
      (vars, s') <- collectVars s x
      (rest, s'') <- collectVarsMany s' xs
      pure (vars ++ rest, s'')

-- | Monadic version of 'all'. Short-circuits on the first 'False'.
allM :: (Monad m) => (a -> m Bool) -> [a] -> m Bool
allM _ [] = pure True
allM p (x : xs) = do
  b <- p x
  if b then allM p xs else pure False

-- | Build a Prolog-style list (@[H|T]@) from a Haskell list of values.
--
-- The empty list is represented as the atom @[]@, and cons cells as
-- @.(H, T)@ compound terms.
valueList :: [Value] -> Value
valueList [] = VTerm "prelude__[]" []
valueList (x : xs) = VTerm "prelude__." [x, valueList xs]

-- | Decompose a Prolog-style list back into a Haskell list. Recognizes
-- both the canonicalized cons form (@prelude__.@/@prelude__[]@,
-- emitted by the renamer-driven pipeline) and the legacy bare form
-- (@.@/@[]@, used by Haskell-side code that constructs values without
-- going through the renamer — e.g. test fixtures, the DSL).
-- Returns 'Nothing' if the value is not a well-formed list.
fromValueList :: Value -> Maybe [Value]
fromValueList (VTerm "prelude__[]" []) = Just []
fromValueList (VAtom "prelude__[]") = Just []
fromValueList (VAtom "[]") = Just []
fromValueList (VTerm "prelude__." [x, rest]) = (x :) <$> fromValueList rest
fromValueList (VTerm "." [x, rest]) = (x :) <$> fromValueList rest
fromValueList _ = Nothing
