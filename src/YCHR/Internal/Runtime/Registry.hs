{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Host call registry for the CHR runtime.
--
-- Provides a base registry of host language functions (arithmetic,
-- comparisons, string operations, type predicates) and generic helpers
-- for building custom host calls.
--
-- The value predicates below do not dereference: they inspect the
-- 'Value' they are given, so callers pass an already-dereferenced
-- value (the registry's own @typePred@ does).
module YCHR.Internal.Runtime.Registry
  ( -- * Types (re-exported from "YCHR.Internal.Runtime.Monad")
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
import YCHR.Internal.Runtime.Error (instantiationErrorS, runtimeErrorS)
import YCHR.Internal.Runtime.Monad (Chr, HostCallFn (..), HostCallRegistry)
import YCHR.Internal.Runtime.Types (Value (..), VarId)
import YCHR.Internal.Runtime.Var (deref, equal, getVarId, newVar, unifiable)
import YCHR.Internal.VM (Name (..))

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
      (Name "div", intDivOp2 "div" div),
      (Name "mod", intDivOp2 "mod" mod),
      (Name "rem", intDivOp2 "rem" rem),
      (Name "/", floatArith2 (/)),
      (Name "<", ordCmp (<) (<) (<)),
      (Name ">", ordCmp (>) (>) (>)),
      (Name "=<", ordCmp (<=) (<=) (<=)),
      (Name ">=", ordCmp (>=) (>=) (>=)),
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
      (Name "__chr_is_unbound", typePred isVar),
      (Name "__chr_inst_error", chrInstError),
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
        argError "arithmetic host call" args $
          "arithmetic host call: expected 2 numeric arguments of same type, got "
            ++ show (length args)
    intDivOp2 opName op = HostCallFn $ \case
      [VInt _, VInt 0] ->
        runtimeErrorS $ "integer " ++ opName ++ ": division by zero"
      [VInt a, VInt b] -> pure (VInt (op a b))
      args ->
        argError "integer arithmetic host call" args $
          "integer arithmetic host call: expected 2 Int arguments, got "
            ++ show (length args)
    floatArith2 op = HostCallFn $ \case
      [VFloat a, VFloat b] -> pure (VFloat (op a b))
      args ->
        argError "float arithmetic host call" args $
          "float arithmetic host call: expected 2 Float arguments, got "
            ++ show (length args)
    -- The four ordering operators are declared over @int@, @float@ and
    -- @string@ (see the @:- class@ blocks in @libraries\/prelude.chr@).
    -- Strings order lexicographically by code point: 'Ord' on 'T.Text'
    -- agrees with 'Ord' on 'String', so this is the same ordering
    -- Haskell code sorting on a file name or an identifier would get.
    ordCmp intOp floatOp textOp = HostCallFn $ \case
      [VInt a, VInt b] -> pure (VBool (intOp a b))
      [VFloat a, VFloat b] -> pure (VBool (floatOp a b))
      [VText a, VText b] -> pure (VBool (textOp a b))
      args ->
        argError "comparison host call" args $
          "comparison host call: expected 2 int, float or string arguments"
            ++ " of the same type, got "
            ++ show (length args)
    toFloatFn = HostCallFn $ \case
      [VInt n] -> pure (VFloat (fromIntegral n))
      [VFloat n] -> pure (VFloat n)
      args ->
        argError "int_to_float" args "int_to_float: expected 1 numeric argument"
    toIntFn = HostCallFn $ \case
      [VFloat n] -> pure (VInt (truncate n))
      [VInt n] -> pure (VInt n)
      args ->
        argError "float_to_int" args "float_to_int: expected 1 numeric argument"
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
      args -> argError "string_concat" args "string_concat: expected 2 Text arguments"
    stringLength = HostCallFn $ \case
      [VText s] -> pure (VInt (fromIntegral (T.length s)))
      args -> argError "string_length" args "string_length: expected 1 Text argument"
    stringUpper = HostCallFn $ \case
      [VText s] -> pure (VText (T.toUpper s))
      args -> argError "string_upper" args "string_upper: expected 1 Text argument"
    stringLower = HostCallFn $ \case
      [VText s] -> pure (VText (T.toLower s))
      args -> argError "string_lower" args "string_lower: expected 1 Text argument"
    -- Generated dispatch code passes the message body as an atom; the
    -- runtime only supplies the common prefix. The catch-all keeps a
    -- malformed call from being silently swallowed.
    chrError = HostCallFn $ \case
      [VAtom msg] -> chrErr (T.unpack msg)
      _ -> chrErr "no matching equation"
    -- The insufficient-instantiation counterpart of 'chrError'. Either
    -- the whole message body is already known at compile time, or a
    -- label plus the runtime-computed 1-based index of the argument
    -- that blocked dispatch (0 when the compiler could not attribute
    -- the blocking test to a single top-level argument).
    chrInstError = HostCallFn $ \case
      [VAtom detail] -> chrInstErr (T.unpack detail)
      [VAtom label, VInt 0] -> chrInstErr (T.unpack label <> notInstantiated)
      [VAtom label, VInt n] ->
        chrInstErr ("argument " <> show n <> " of " <> T.unpack label <> notInstantiated)
      _ -> chrInstErr ("dispatch" <> notInstantiated)
    notInstantiated =
      " is not sufficiently instantiated to select an equation"
        <> " (unbound variable at a matched position)"
    chrErr detail = runtimeErrorS ("CHR runtime error: " <> detail)
    chrInstErr detail = instantiationErrorS ("CHR runtime error: " <> detail)
    writeStr = HostCallFn $ \case
      [VText s] -> unit <$ liftIO (putStr (T.unpack s))
      args -> argError "write" args "write: expected 1 Text argument"
    writeStrLn = HostCallFn $ \case
      [VText s] -> unit <$ liftIO (putStrLn (T.unpack s))
      args -> argError "writeln" args "writeln: expected 1 Text argument"
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
      [v@(VAtom _)] -> pure (valueList [v])
      args ->
        argError
          "compound_to_list"
          args
          "compound_to_list: expected 1 compound or atom argument"
    listToCompound = HostCallFn $ \case
      args@[list] -> case fromValueList list of
        Just [VAtom f] -> pure (VAtom f)
        Just (VAtom f : fArgs) -> pure (VTerm f fArgs)
        _ ->
          argError
            "list_to_compound"
            args
            "list_to_compound: expected a non-empty list with an atom head"
      args -> argError "list_to_compound" args "list_to_compound: expected 1 list argument"
    copyTermHost = HostCallFn $ \case
      [v] -> copyTerm v
      _ -> runtimeErrorS "copy_term: expected 1 argument"
    -- Report a strict primitive's failure. Each caller is a total
    -- function of its arguments' values with no ignored positions, so
    -- reaching the failure path with an argument that is still an
    -- unbound variable means the value was demanded and was not there:
    -- an instantiation failure, which a rule guard catches and turns
    -- into a silent @false@. Any other failure (wrong type, wrong
    -- arity) is a general error and stays fatal everywhere.
    argError label args general = do
      unbound <- anyUnbound args
      if unbound
        then
          instantiationErrorS $
            label ++ ": argument is not sufficiently instantiated (unbound variable)"
        else runtimeErrorS general
    anyUnbound [] = pure False
    anyUnbound (v : vs) = do
      v' <- deref v
      if isVar v' then pure True else anyUnbound vs

-- ---------------------------------------------------------------------------
-- Utilities
-- ---------------------------------------------------------------------------

-- | The unit return value for host calls that are only used for side effects.
unit :: Value
unit = VAtom "()"

-- ---------------------------------------------------------------------------
-- Value predicates
-- ---------------------------------------------------------------------------

-- | Is the value an integer literal ('VInt')?
isInteger :: Value -> Bool
isInteger (VInt _) = True
isInteger _ = False

-- | Is the value a float literal ('VFloat')?
isFloat :: Value -> Bool
isFloat (VFloat _) = True
isFloat _ = False

-- | Is the value an atom ('VAtom')?
isAtom :: Value -> Bool
isAtom (VAtom _) = True
isAtom _ = False

-- | Is the value a boolean ('VBool')?
isBoolean :: Value -> Bool
isBoolean (VBool _) = True
isBoolean _ = False

-- | Is the value a string ('VText')?
isString :: Value -> Bool
isString (VText _) = True
isString _ = False

-- | Is the value a variable — a 'VVar' or a 'VWildcard'?
isVar :: Value -> Bool
isVar (VVar _) = True
isVar VWildcard = True
isVar _ = False

-- | Is the value not a variable? The negation of 'isVar'.
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
valueList [] = VAtom "prelude__[]"
valueList (x : xs) = VTerm "prelude__." [x, valueList xs]

-- | Decompose a Prolog-style list back into a Haskell list. Recognizes
-- both the canonicalized cons form (@prelude__.@/@prelude__[]@,
-- emitted by the renamer-driven pipeline) and the legacy bare form
-- (@.@/@[]@, used by Haskell-side code that constructs values without
-- going through the renamer — e.g. test fixtures, the DSL).
-- Returns 'Nothing' if the value is not a well-formed list.
fromValueList :: Value -> Maybe [Value]
fromValueList (VAtom "prelude__[]") = Just []
fromValueList (VAtom "[]") = Just []
fromValueList (VTerm "prelude__." [x, rest]) = (x :) <$> fromValueList rest
fromValueList (VTerm "." [x, rest]) = (x :) <$> fromValueList rest
fromValueList _ = Nothing
