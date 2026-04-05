{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

-- | Host call registry for the CHR runtime.
--
-- Provides a base registry of host language functions (arithmetic,
-- comparisons, string operations, type predicates) and generic helpers
-- for building custom host calls.
module YCHR.Runtime.Registry
  ( -- * Types
    HostCallFn (..),
    HostCallRegistry,

    -- * Registry
    baseHostCallRegistry,

    -- * Utilities
    unit,
    toValue,

    -- * Value predicates
    isInteger,
    isAtom,
    isBoolean,
    isString,
    isVar,
    isNonvar,

    -- * Generic helpers
    allM,
    collectVars,
    fromValueList,
    valueList,
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as T
import Effectful
import YCHR.Runtime.Store (CHRStore)
import YCHR.Runtime.Types (RuntimeVal (..), Value (..), VarId)
import YCHR.Runtime.Var (Unify, deref, getVarId, newVar)
import YCHR.VM (Name (..))

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

-- | A host call function that can use logical variables, the constraint
-- store, and IO.
newtype HostCallFn = HostCallFn
  {runHostCall :: forall es. (Unify :> es, CHRStore :> es, IOE :> es) => [RuntimeVal] -> Eff es RuntimeVal}

-- | Registry of host language functions.
type HostCallRegistry = Map Name HostCallFn

-- ---------------------------------------------------------------------------
-- Registry
-- ---------------------------------------------------------------------------

-- | A base host call registry providing arithmetic, comparison, string,
-- and type predicate operations.
baseHostCallRegistry :: HostCallRegistry
baseHostCallRegistry =
  Map.fromList
    [ (Name "+", arith2 (+)),
      (Name "-", arith2 (-)),
      (Name "*", arith2 (*)),
      (Name "div", arith2 div),
      (Name "mod", arith2 mod),
      (Name "<", cmp (<)),
      (Name ">", cmp (>)),
      (Name "=<", cmp (<=)),
      (Name ">=", cmp (>=)),
      (Name "==", valEq),
      (Name "string_concat", stringConcat),
      (Name "string_length", stringLength),
      (Name "string_upper", stringUpper),
      (Name "string_lower", stringLower),
      (Name "__chr_error", chrError),
      (Name "write", writeStr),
      (Name "integer", typePred isInteger),
      (Name "atom", typePred isAtom),
      (Name "boolean", typePred isBoolean),
      (Name "string", typePred isString),
      (Name "var", typePred isVar),
      (Name "nonvar", typePred isNonvar),
      (Name "ground", groundPred),
      (Name "term_variables", termVariablesPred),
      (Name "compound_to_list", compoundToList),
      (Name "list_to_compound", listToCompound)
    ]
  where
    arith2 op = HostCallFn $ \case
      [RVal (VInt a), RVal (VInt b)] -> pure (RVal (VInt (op a b)))
      args -> error $ "arithmetic host call: expected 2 Int arguments, got " ++ show (length args)
    cmp op = HostCallFn $ \case
      [RVal (VInt a), RVal (VInt b)] -> pure (RVal (VBool (op a b)))
      args -> error $ "comparison host call: expected 2 Int arguments, got " ++ show (length args)
    valEq = HostCallFn $ \case
      [RVal (VInt a), RVal (VInt b)] -> pure (RVal (VBool (a == b)))
      [RVal (VAtom a), RVal (VAtom b)] -> pure (RVal (VBool (a == b)))
      [RVal (VText a), RVal (VText b)] -> pure (RVal (VBool (a == b)))
      [RVal (VBool a), RVal (VBool b)] -> pure (RVal (VBool (a == b)))
      [_, _] -> pure (RVal (VBool False))
      args -> error $ "== host call: expected 2 arguments, got " ++ show (length args)
    stringConcat = HostCallFn $ \case
      [RVal (VText a), RVal (VText b)] -> pure (RVal (VText (a <> b)))
      _ -> error "string_concat: expected 2 Text arguments"
    stringLength = HostCallFn $ \case
      [RVal (VText s)] -> pure (RVal (VInt (T.length s)))
      _ -> error "string_length: expected 1 Text argument"
    stringUpper = HostCallFn $ \case
      [RVal (VText s)] -> pure (RVal (VText (T.toUpper s)))
      _ -> error "string_upper: expected 1 Text argument"
    stringLower = HostCallFn $ \case
      [RVal (VText s)] -> pure (RVal (VText (T.toLower s)))
      _ -> error "string_lower: expected 1 Text argument"
    chrError = HostCallFn $ \_ -> error "CHR runtime error: no matching equation"
    writeStr = HostCallFn $ \case
      [RVal (VText s)] -> unit <$ liftIO (putStr (T.unpack s))
      _ -> error "write: expected 1 Text argument"
    typePred p = HostCallFn $ \case
      [RVal v] -> do
        v' <- deref v
        pure (RVal (VBool (p v')))
      _ -> error "type predicate: expected 1 argument"
    groundPred = HostCallFn $ \case
      [RVal v] -> RVal . VBool <$> isGround v
      _ -> error "ground: expected 1 argument"
    isGround v = do
      v' <- deref v
      case v' of
        VVar _ -> pure False
        VWildcard -> pure False
        VTerm _ args -> allM isGround args
        _ -> pure True
    termVariablesPred = HostCallFn $ \case
      [RVal v] -> do
        (vars, _) <- collectVars Set.empty v
        pure (RVal (valueList vars))
      _ -> error "term_variables: expected 1 argument"
    compoundToList = HostCallFn $ \case
      [RVal (VTerm f args)] -> pure (RVal (valueList (VAtom f : args)))
      _ -> error "compound_to_list: expected 1 compound term argument"
    listToCompound = HostCallFn $ \case
      [RVal list] -> case fromValueList list of
        Just (VAtom f : args) -> pure (RVal (VTerm f args))
        _ -> error "list_to_compound: expected a non-empty list with an atom head"
      _ -> error "list_to_compound: expected 1 list argument"

-- ---------------------------------------------------------------------------
-- Utilities
-- ---------------------------------------------------------------------------

-- | The unit return value for host calls that are only used for side effects.
unit :: RuntimeVal
unit = RVal (VAtom "()")

-- | Extract a 'Value' from a 'RuntimeVal'. Raises an error on constraint IDs.
toValue :: RuntimeVal -> Value
toValue (RVal v) = v
toValue (RConstraint _) = error "toValue: cannot convert constraint ID to Value"

-- ---------------------------------------------------------------------------
-- Value predicates
-- ---------------------------------------------------------------------------

-- | Check whether a 'Value' is an integer.
isInteger :: Value -> Bool
isInteger (VInt _) = True
isInteger _ = False

-- | Check whether a 'Value' is an atom.
isAtom :: Value -> Bool
isAtom (VAtom _) = True
isAtom _ = False

-- | Check whether a 'Value' is a boolean.
isBoolean :: Value -> Bool
isBoolean (VBool _) = True
isBoolean _ = False

-- | Check whether a 'Value' is a text string.
isString :: Value -> Bool
isString (VText _) = True
isString _ = False

-- | Check whether a 'Value' is an unbound variable or wildcard.
isVar :: Value -> Bool
isVar (VVar _) = True
isVar VWildcard = True
isVar _ = False

-- | Check whether a 'Value' is not a variable.
isNonvar :: Value -> Bool
isNonvar = not . isVar

-- ---------------------------------------------------------------------------
-- Generic helpers
-- ---------------------------------------------------------------------------

-- | Collect all unique unbound variables in a term, traversing into
-- compound term arguments. Wildcards are replaced with fresh variables.
-- Returns the collected variables and the updated set of seen 'VarId's.
collectVars :: (Unify :> es, IOE :> es) => Set.Set VarId -> Value -> Eff es ([Value], Set.Set VarId)
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
valueList [] = VAtom "[]"
valueList (x : xs) = VTerm "." [x, valueList xs]

-- | Decompose a Prolog-style list back into a Haskell list.
-- Returns 'Nothing' if the value is not a well-formed list.
fromValueList :: Value -> Maybe [Value]
fromValueList (VAtom "[]") = Just []
fromValueList (VTerm "." [x, rest]) = (x :) <$> fromValueList rest
fromValueList _ = Nothing
