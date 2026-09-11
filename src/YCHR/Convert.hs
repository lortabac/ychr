{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Pass and receive Haskell values at the CHR boundary instead of
-- hand-building 'Term's. The boundary is the pure 'Term' type — a goal is
-- a 'Term', a result is a @'Map' 'Text' 'Term'@ keyed by goal-variable
-- name — so both classes target 'Term' and never see runtime values.
-- Reference and examples:
-- <https://github.com/lortabac/ychr/blob/master/docs/reference/convert.md>.
--
-- Under GHC, "YCHR.Convert.Generic" derives both classes for
-- @deriving 'GHC.Generics.Generic'@ types; this module stays @Generic@-free.
module YCHR.Convert
  ( -- * Classes
    ToTerm (..),
    FromTerm (..),

    -- * Errors
    ConvertError (..),

    -- * Combinators for hand-written instances
    compound,
    atomTerm,
    matchCompound,
    decodeSum,
    argAt,
    ground,

    -- * The quote/1 quoting form
    quote,

    -- * Result decoding
    decodeVar,
    decodeVarMaybe,
    lookupBinding,

    -- * Host functions
    -- $hostFunctions
    HostCallFn (..),
    Chr,
    Value (..),
    hostFn0M,
    hostFn1,
    hostFn1M,
    hostFn2,
    hostFn2M,
    hostFn3,
    hostFn3M,
    hostFnN,
    hostFnValues,

    -- * Host-function registries
    HostCallRegistry,
    baseHostCallRegistry,
    hostFunctions,
    withDefaultHostFunctions,

    -- * Typed query wrapper
    runQuery,
    runQueryWith,
    runQueryWithHostCallRegistry,

    -- * Typed query wrapper over a compiled program
    CompiledProgram,
    runQueryCompiled,
    runQueryCompiledWith,
    runQueryCompiledWithHostCallRegistry,
  )
where

import Control.Exception (throwIO)
import Control.Monad.Trans.State.Strict (evalStateT)
import Data.Bits (toIntegralSized)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as Text
import YCHR.Internal.Meta (termToValue, valueToTerm)
import YCHR.Internal.Parsed (Module)
import YCHR.Internal.Runtime.Error (instantiationErrorS, runtimeErrorS)
import YCHR.Internal.Runtime.Monad (Chr)
import YCHR.Internal.Runtime.Registry (HostCallFn (..), HostCallRegistry, baseHostCallRegistry)
import YCHR.Internal.Runtime.Search (defaultHostCallRegistry)
import YCHR.Internal.Runtime.Types (Value (..))
import YCHR.Internal.VM qualified as VM
import YCHR.Run
  ( CompiledProgram,
    Error,
    compileParsedModules,
    runProgramWithGoalDSL,
  )
import YCHR.Types (Constraint (..), Name (..), Term (..))

-- ---------------------------------------------------------------------------
-- Classes
-- ---------------------------------------------------------------------------

-- | Encode a Haskell value as a 'Term'. Total.
class ToTerm a where
  toTerm :: a -> Term

-- | Decode a 'Term'. Wrong shape or an unbound variable where a ground
-- value is needed is a 'ConvertError', never a throw.
class FromTerm a where
  fromTerm :: Term -> Either ConvertError a

-- ---------------------------------------------------------------------------
-- Errors
-- ---------------------------------------------------------------------------

-- | Why a 'Term' could not be decoded.
data ConvertError
  = -- | Wrong shape: what was expected, and the term found.
    TypeMismatch Text Term
  | -- | Right functor, wrong argument count: functor, expected arity, found arity.
    ArityMismatch Name Int Int
  | -- | Functor matched none of a sum type's rows: accepted names, found.
    UnknownFunctor [Text] Name
  | -- | A ground value was required but the term was a variable or wildcard.
    UnboundValue Term
  | -- | Result-map decoding: the requested goal variable is absent.
    MissingBinding Text
  | -- | A typed query's goal is not a compound term (a constraint occurrence).
    MalformedGoal Term
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Combinators for hand-written instances
-- ---------------------------------------------------------------------------

-- | Unqualified compound term (the shape "YCHR.DSL"'s @term@ builds).
compound :: Text -> [Term] -> Term
compound n = CompoundTerm (Unqualified n)

-- | Nullary atom: an unqualified 0-arity compound.
atomTerm :: Text -> Term
atomTerm n = CompoundTerm (Unqualified n) []

-- | Wrap a decoder so an unbound variable or wildcard is 'UnboundValue'
-- before it runs. Every scalar 'FromTerm' instance uses it, so that
-- failure is uniform; use it in yours.
ground :: (Term -> Either ConvertError a) -> Term -> Either ConvertError a
ground _ t@(VarTerm _) = Left (UnboundValue t)
ground _ t@Wildcard = Left (UnboundValue t)
ground f t = f t

-- | The arguments of a compound with this functor and exact arity.
-- Variables\/wildcards are 'UnboundValue', another functor
-- 'UnknownFunctor', wrong arity 'ArityMismatch', non-compounds
-- 'TypeMismatch'. Only the local part of the functor is compared, so a
-- module-qualified result still decodes.
matchCompound :: Text -> Int -> Term -> Either ConvertError [Term]
matchCompound n arity = ground $ \t -> case t of
  CompoundTerm name args
    | nameLocal name == n ->
        if length args == arity
          then Right args
          else Left (ArityMismatch name arity (length args))
    | otherwise -> Left (UnknownFunctor [n] name)
  _ -> Left (TypeMismatch n t)

-- | Decode a sum type by dispatching on functor and arity over
-- @(functor, arity, handler)@ rows. No matching functor is
-- 'UnknownFunctor'; matching functor with the wrong arity is
-- 'ArityMismatch'. Local-part matching as in 'matchCompound'.
decodeSum ::
  [(Text, Int, [Term] -> Either ConvertError a)] ->
  Term ->
  Either ConvertError a
decodeSum rows = ground $ \t -> case t of
  CompoundTerm name args ->
    case lookupRow (nameLocal name) of
      Just (ar, h)
        | ar == length args -> h args
        | otherwise -> Left (ArityMismatch name ar (length args))
      Nothing -> Left (UnknownFunctor rowNames name)
  _ -> Left (TypeMismatch (Text.intercalate " | " rowNames) t)
  where
    rowNames = map (\(fn, _, _) -> fn) rows
    lookupRow k =
      foldr (\(fn, ar, h) acc -> if fn == k then Just (ar, h) else acc) Nothing rows

-- | 'fromTerm' on the argument at a 0-based position, for the list
-- 'matchCompound' \/ 'decodeSum' return (arity already checked).
argAt :: (FromTerm a) => Int -> [Term] -> Either ConvertError a
argAt i args = case drop i args of
  (t : _) -> fromTerm t
  [] -> Left (TypeMismatch ("positional argument #" <> Text.pack (show i)) Wildcard)

-- ---------------------------------------------------------------------------
-- The quote/1 quoting form
-- ---------------------------------------------------------------------------

-- | Wrap a value in @quote\/1@ so it stays symbolic. Goal and rule-body
-- arguments are /evaluated/: a compound whose functor names a declared
-- function is called, not kept as data; quoting opts out. Apply it where
-- the goal is built, not inside a 'ToTerm' instance:
--
-- > compound "typecheck" [quote expr, VarTerm "Result"]
--
-- 'toTerm' is applied implicitly; a plain 'Term' passes through.
quote :: (ToTerm a) => a -> Term
quote x = CompoundTerm (Unqualified "quote") [toTerm x]

-- | The local (unqualified) part of a name.
nameLocal :: Name -> Text
nameLocal (Unqualified n) = n
nameLocal (Qualified _ n) = n

-- ---------------------------------------------------------------------------
-- Base and stdlib instances
-- ---------------------------------------------------------------------------

instance ToTerm Term where
  toTerm = id

instance FromTerm Term where
  fromTerm = Right

instance ToTerm Integer where
  toTerm = IntTerm

instance FromTerm Integer where
  fromTerm = ground $ \t -> case t of
    IntTerm n -> Right n
    _ -> Left (TypeMismatch "Integer" t)

instance ToTerm Int where
  toTerm = IntTerm . toInteger

instance FromTerm Int where
  fromTerm = ground $ \t -> case t of
    IntTerm n -> maybe (Left (TypeMismatch "Int" t)) Right (toIntegralSized n)
    _ -> Left (TypeMismatch "Int" t)

-- | Strict: an 'IntTerm' is /not/ coerced to 'Double'.
instance ToTerm Double where
  toTerm = FloatTerm

instance FromTerm Double where
  fromTerm = ground $ \t -> case t of
    FloatTerm d -> Right d
    _ -> Left (TypeMismatch "Double" t)

-- | The canonical @true@ \/ @false@ atom, which the host-value bridge turns
-- into a native boolean. Decoding also accepts the @prelude@-qualified
-- forms that appear in results.
instance ToTerm Bool where
  toTerm True = atomTerm "true"
  toTerm False = atomTerm "false"

instance FromTerm Bool where
  fromTerm = ground $ \t -> case t of
    CompoundTerm (Unqualified "true") [] -> Right True
    CompoundTerm (Unqualified "false") [] -> Right False
    CompoundTerm (Qualified "prelude" "true") [] -> Right True
    CompoundTerm (Qualified "prelude" "false") [] -> Right False
    _ -> Left (TypeMismatch "Bool" t)

-- | The CHR string type: 'TextTerm'.
instance ToTerm Text where
  toTerm = TextTerm

instance FromTerm Text where
  fromTerm = ground $ \t -> case t of
    TextTerm s -> Right s
    _ -> Left (TypeMismatch "Text" t)

-- | A one-character 'TextTerm'. Hence @String = [Char]@ round-trips as a
-- /list/ of one-character 'TextTerm's; use 'Text' for a single string.
instance ToTerm Char where
  toTerm c = TextTerm (Text.singleton c)

instance FromTerm Char where
  fromTerm = ground $ \t -> case t of
    TextTerm s | Text.length s == 1 -> Right (Text.head s)
    _ -> Left (TypeMismatch "Char" t)

-- | The @()@ atom, the runtime's unit value.
instance ToTerm () where
  toTerm () = atomTerm "()"

instance FromTerm () where
  fromTerm = ground $ \t -> case t of
    CompoundTerm (Unqualified "()") [] -> Right ()
    _ -> Left (TypeMismatch "()" t)

instance (ToTerm a) => ToTerm (Maybe a) where
  toTerm Nothing = atomTerm "nothing"
  toTerm (Just x) = compound "just" [toTerm x]

instance (FromTerm a) => FromTerm (Maybe a) where
  fromTerm =
    decodeSum
      [ ("nothing", 0, \_ -> Right Nothing),
        ("just", 1, \as -> Just <$> argAt 0 as)
      ]

instance (ToTerm a, ToTerm b) => ToTerm (Either a b) where
  toTerm (Left x) = compound "left" [toTerm x]
  toTerm (Right y) = compound "right" [toTerm y]

instance (FromTerm a, FromTerm b) => FromTerm (Either a b) where
  fromTerm =
    decodeSum
      [ ("left", 1, \as -> Left <$> argAt 0 as),
        ("right", 1, \as -> Right <$> argAt 0 as)
      ]

-- Tuples encode to a @tuple@ compound, distinguished by arity.

instance (ToTerm a, ToTerm b) => ToTerm (a, b) where
  toTerm (a, b) = compound "tuple" [toTerm a, toTerm b]

instance (FromTerm a, FromTerm b) => FromTerm (a, b) where
  fromTerm t = do
    as <- matchCompound "tuple" 2 t
    (,) <$> argAt 0 as <*> argAt 1 as

instance (ToTerm a, ToTerm b, ToTerm c) => ToTerm (a, b, c) where
  toTerm (a, b, c) = compound "tuple" [toTerm a, toTerm b, toTerm c]

instance (FromTerm a, FromTerm b, FromTerm c) => FromTerm (a, b, c) where
  fromTerm t = do
    as <- matchCompound "tuple" 3 t
    (,,) <$> argAt 0 as <*> argAt 1 as <*> argAt 2 as

instance (ToTerm a, ToTerm b, ToTerm c, ToTerm d) => ToTerm (a, b, c, d) where
  toTerm (a, b, c, d) = compound "tuple" [toTerm a, toTerm b, toTerm c, toTerm d]

instance (FromTerm a, FromTerm b, FromTerm c, FromTerm d) => FromTerm (a, b, c, d) where
  fromTerm t = do
    as <- matchCompound "tuple" 4 t
    (,,,) <$> argAt 0 as <*> argAt 1 as <*> argAt 2 as <*> argAt 3 as

-- | Prolog list: cons @.\/2@, nil @[]@, as @library(lists)@ expects.
-- Decoding also accepts the @prelude@-qualified and mangled cons\/nil
-- forms that appear in results.
instance (ToTerm a) => ToTerm [a] where
  toTerm = foldr (\x acc -> compound "." [toTerm x, acc]) (atomTerm "[]")

instance (FromTerm a) => FromTerm [a] where
  fromTerm = ground go
    where
      go t = case t of
        CompoundTerm name []
          | isNil name -> Right []
        CompoundTerm name [h, tl]
          | isCons name -> (:) <$> fromTerm h <*> fromTerm tl
        _ -> Left (TypeMismatch "list" t)
      isNil name =
        name
          `elem` [ Unqualified "[]",
                   Qualified "prelude" "[]",
                   Unqualified "prelude__[]"
                 ]
      isCons name =
        name
          `elem` [ Unqualified ".",
                   Qualified "prelude" ".",
                   Unqualified "prelude__."
                 ]

-- ---------------------------------------------------------------------------
-- Result decoding
-- ---------------------------------------------------------------------------

-- | 'fromTerm' on one goal variable's binding; 'MissingBinding' if absent.
decodeVar :: (FromTerm a) => Text -> Map Text Term -> Either ConvertError a
decodeVar k m = case Map.lookup k m of
  Nothing -> Left (MissingBinding k)
  Just t -> fromTerm t

-- | 'decodeVar' with 'Nothing' for an absent variable. A present but
-- undecodable binding still fails.
decodeVarMaybe :: (FromTerm a) => Text -> Map Text Term -> Either ConvertError (Maybe a)
decodeVarMaybe k m = case Map.lookup k m of
  Nothing -> Right Nothing
  Just t -> Just <$> fromTerm t

-- | The raw bound 'Term' for a goal variable, if any.
lookupBinding :: Text -> Map Text Term -> Maybe Term
lookupBinding = Map.lookup

-- ---------------------------------------------------------------------------
-- Typed query wrapper
-- ---------------------------------------------------------------------------

{- Note [Goal argument canonicalization]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
A goal's arguments are renamed before the goal runs, exactly like the
arguments of a rule head: a bare reference to a data constructor the
program declares *and exports* becomes its qualified form, which is
what the compiled head patterns match.

  * A type the program declares but does not export is invisible to
    the query: its constructors stay unqualified and rules written
    against them silently never fire. That warns (YCHR-20101), but the
    typed wrappers have no warning channel and discard it. Use
    YCHR.Run.runProgramWithGoalDSLWithWarnings to see it.

  * Renaming can fail: a bare name visible both as a constructor and
    as a function (YCHR-20020), an ambiguous unqualified constructor
    (YCHR-20012), or a qualified name its module does not export
    (YCHR-20010). Those are thrown as Error, not returned as a
    ConvertError.

  * Goal arguments are still evaluated, like any tell. Wrap an
    undeclared compound in 'quote' to pass it as symbolic data.
-}

-- | Compile the modules (stdlib included), run the goal with the default
-- host-call registry, decode one goal variable's binding. The goal is a
-- compound built like a rule head; its arguments are canonicalized and
-- evaluated at tell time, so a constructor of a type the program does not
-- export never matches a rule — see Note [Goal argument canonicalization].
-- Compilation and rename failures are thrown as 'Error'; decoding failures
-- come back as 'Left'.
runQuery :: (FromTerm a) => [Module] -> Term -> Text -> IO (Either ConvertError a)
runQuery modules goal v = runQueryWith modules goal (decodeVar v)

-- | 'runQuery' with a decoder over the whole binding map (assemble a
-- record from several 'decodeVar's).
runQueryWith ::
  [Module] ->
  Term ->
  (Map Text Term -> Either ConvertError a) ->
  IO (Either ConvertError a)
runQueryWith = runQueryWithHostCallRegistry defaultHostCallRegistry

-- | 'runQueryWith' with an explicit host-call registry.
runQueryWithHostCallRegistry ::
  HostCallRegistry ->
  [Module] ->
  Term ->
  (Map Text Term -> Either ConvertError a) ->
  IO (Either ConvertError a)
runQueryWithHostCallRegistry hostCalls modules goal decode =
  -- Goal shape first, so a malformed goal is reported as data without
  -- compiling (or throwing).
  case goalConstraint goal of
    Left err -> pure (Left err)
    Right _ -> do
      cp <- compileOrThrow modules
      runQueryCompiledWithHostCallRegistry hostCalls cp goal decode

compileOrThrow :: [Module] -> IO CompiledProgram
compileOrThrow modules = case compileParsedModules True modules of
  Left err -> throwIO (err :: Error)
  Right (cp, _warnings) -> pure cp

-- ---------------------------------------------------------------------------
-- Typed query wrapper over a compiled program
-- ---------------------------------------------------------------------------

-- | 'runQuery' over a 'CompiledProgram' ('YCHR.Run.compileFiles' or
-- 'YCHR.Run.compileParsedModules'): compile once, query many. Each call
-- is an independent run with a fresh store. A constructor of a type the
-- program does not export never matches a rule; see Note [Goal argument
-- canonicalization].
runQueryCompiled ::
  (FromTerm a) => CompiledProgram -> Term -> Text -> IO (Either ConvertError a)
runQueryCompiled cp goal v = runQueryCompiledWith cp goal (decodeVar v)

-- | 'runQueryWith' over a 'CompiledProgram'.
runQueryCompiledWith ::
  CompiledProgram ->
  Term ->
  (Map Text Term -> Either ConvertError a) ->
  IO (Either ConvertError a)
runQueryCompiledWith =
  runQueryCompiledWithHostCallRegistry defaultHostCallRegistry

-- | 'runQueryWithHostCallRegistry' over a 'CompiledProgram'.
runQueryCompiledWithHostCallRegistry ::
  HostCallRegistry ->
  CompiledProgram ->
  Term ->
  (Map Text Term -> Either ConvertError a) ->
  IO (Either ConvertError a)
runQueryCompiledWithHostCallRegistry hostCalls cp goal decode =
  case goalConstraint goal of
    Left err -> pure (Left err)
    Right constraint -> do
      bindings <- runProgramWithGoalDSL cp hostCalls constraint
      pure (decode bindings)

-- | A goal must be a compound (a constraint occurrence); otherwise
-- 'MalformedGoal', as data — unlike "YCHR.DSL", which throws.
goalConstraint :: Term -> Either ConvertError Constraint
goalConstraint (CompoundTerm n args) = Right (Constraint n args)
goalConstraint t = Left (MalformedGoal t)

-- ---------------------------------------------------------------------------
-- Host functions
-- ---------------------------------------------------------------------------

-- $hostFunctions
--
-- A @host:f(args)@ call dispatches through a 'HostCallRegistry'. These
-- adapters lift Haskell functions into 'HostCallFn' entries, marshalling
-- through 'ToTerm' \/ 'FromTerm'. Assemble with 'hostFunctions' or
-- 'withDefaultHostFunctions'; pass to a @…WithHostCallRegistry@ query.
-- Walkthrough: section /Registering host functions/ of
-- <https://github.com/lortabac/ychr/blob/master/docs/reference/convert.md>.

-- | Decode one host-call argument. 'valueToTerm' dereferences recursively;
-- an unbound variable becomes 'Wildcard', which 'fromTerm' rejects as
-- 'UnboundValue'.
argFromValue :: (FromTerm a) => Value -> Chr (Either ConvertError a)
argFromValue v = fromTerm <$> valueToTerm Map.empty v

-- | Encode a host-function result. Results are expected ground.
resultToValue :: (ToTerm r) => r -> Chr Value
resultToValue r = evalStateT (termToValue (toTerm r)) Map.empty

hostArityError :: Int -> [a] -> Chr b
hostArityError n vs =
  runtimeErrorS
    ("host call: expected " ++ show n ++ " argument(s), got " ++ show (length vs))

-- | 'UnboundValue' is an instantiation failure: a rule guard catches it
-- and delays until the variable is bound. Any other decode failure is a
-- runtime error. Decode as 'Term' to accept a variable.
hostDecodeError :: ConvertError -> Chr a
hostDecodeError err@(UnboundValue _) = instantiationErrorS ("host call: " ++ show err)
hostDecodeError err = runtimeErrorS ("host call: " ++ show err)

-- | Nullary effectful host function (a clock, a fresh id). No pure
-- @hostFn0@: that would be a constant. The body runs in 'Chr';
-- 'Control.Monad.IO.Class.liftIO' for 'IO'.
hostFn0M :: (ToTerm r) => Chr r -> HostCallFn
hostFn0M act = HostCallFn $ \case
  [] -> act >>= resultToValue
  vs -> hostArityError 0 vs

-- | Pure unary host function.
hostFn1 :: (FromTerm a, ToTerm r) => (a -> r) -> HostCallFn
hostFn1 f = hostFn1M (pure . f)

-- | Effectful unary host function: the body runs in 'Chr'
-- ('Control.Monad.IO.Class.liftIO' for I\/O); arguments and result still
-- marshal via 'FromTerm' \/ 'ToTerm'.
hostFn1M :: (FromTerm a, ToTerm r) => (a -> Chr r) -> HostCallFn
hostFn1M f = HostCallFn $ \case
  [va] -> do
    ea <- argFromValue va
    case ea of
      Right a -> f a >>= resultToValue
      Left err -> hostDecodeError err
  vs -> hostArityError 1 vs

-- | Pure binary host function.
hostFn2 :: (FromTerm a, FromTerm b, ToTerm r) => (a -> b -> r) -> HostCallFn
hostFn2 f = hostFn2M (\a b -> pure (f a b))

-- | Effectful binary host function; see 'hostFn1M'.
hostFn2M :: (FromTerm a, FromTerm b, ToTerm r) => (a -> b -> Chr r) -> HostCallFn
hostFn2M f = HostCallFn $ \case
  [va, vb] -> do
    ea <- argFromValue va
    eb <- argFromValue vb
    case (,) <$> ea <*> eb of
      Right (a, b) -> f a b >>= resultToValue
      Left err -> hostDecodeError err
  vs -> hostArityError 2 vs

-- | Pure ternary host function.
hostFn3 ::
  (FromTerm a, FromTerm b, FromTerm c, ToTerm r) =>
  (a -> b -> c -> r) ->
  HostCallFn
hostFn3 f = hostFn3M (\a b c -> pure (f a b c))

-- | Effectful ternary host function; see 'hostFn1M'.
hostFn3M ::
  (FromTerm a, FromTerm b, FromTerm c, ToTerm r) =>
  (a -> b -> c -> Chr r) ->
  HostCallFn
hostFn3M f = HostCallFn $ \case
  [va, vb, vc] -> do
    ea <- argFromValue va
    eb <- argFromValue vb
    ec <- argFromValue vc
    case (,,) <$> ea <*> eb <*> ec of
      Right (a, b, c) -> f a b c >>= resultToValue
      Left err -> hostDecodeError err
  vs -> hostArityError 3 vs

-- | Variable-arity host function over 'Term's: arguments arrive
-- recursively dereferenced; a 'Left' 'UnboundValue' is an instantiation
-- failure (a guard delays), any other 'ConvertError' a runtime error.
hostFnN :: ([Term] -> Either ConvertError Term) -> HostCallFn
hostFnN g = HostCallFn $ \vs -> do
  ts <- traverse (valueToTerm Map.empty) vs
  case g ts of
    Right t -> resultToValue t
    Left err -> hostDecodeError err

-- | Raw host function over runtime 'Value's, no 'Term' marshalling.
-- Arguments are dereferenced at top level only: variables nested inside
-- a compound are /not/ chased ('YCHR.Run.deref' them yourself).
hostFnValues :: ([Value] -> Chr Value) -> HostCallFn
hostFnValues = HostCallFn

-- | Registry from named host functions: entry @("my_add", …)@ is called as
-- @host:my_add(...)@. Composes with '<>'.
hostFunctions :: [(Text, HostCallFn)] -> HostCallRegistry
hostFunctions = Map.fromList . map (\(n, fn) -> (VM.Name n, fn))

-- | 'hostFunctions' unioned over the default registry (builtins, meta and
-- search host calls). On a name clash the custom entry wins.
withDefaultHostFunctions :: [(Text, HostCallFn)] -> HostCallRegistry
withDefaultHostFunctions fns =
  hostFunctions fns <> defaultHostCallRegistry
