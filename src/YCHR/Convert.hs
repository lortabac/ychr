{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | An ergonomic bridge between ordinary Haskell data types and CHR
-- terms. Use it when @ychr@ is embedded as a library and you would rather
-- pass and receive Haskell values than hand-build and pattern-match
-- 'Term's.
--
-- This module is a companion to "YCHR.DSL": the DSL builds CHR /programs/,
-- while this module converts /values/ at the program boundary. The library
-- boundary is entirely the pure 'Term' type — a goal is a 'Term', and a
-- result is a @'Map' 'Text' 'Term'@ keyed by goal-variable name — so both
-- classes target 'Term' and never touch the runtime value representation.
--
-- = Worked example
--
-- > {-# LANGUAGE OverloadedStrings #-}
-- > import YCHR.Convert
-- > import YCHR.DSL (module', declaring, defining, term, var, int, (@:), (<=>), (|-))
-- >
-- > -- run a program and decode the "R" binding as a Haskell Int
-- > main = do
-- >   r <- runQuery [myModule] (term "compute" [var "R"]) "R"
-- >   print (r :: Either ConvertError Int)
--
-- = Generic derivation
--
-- Hand-writing instances is optional. Under GHC, "YCHR.Convert.Generic"
-- provides @genericToTerm@ / @genericFromTerm@ so a @deriving 'GHC.Generics.Generic'@
-- type gets instances for free. That module is GHC-only; this one carries
-- no @Generic@ dependency and provides the hand-written path.
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
import YCHR.Meta (metaHostCallRegistry, termToValue, valueToTerm)
import YCHR.Parsed (Module)
import YCHR.Run
  ( CompiledProgram,
    Error,
    compileParsedModules,
    runProgramWithGoalDSL,
  )
import YCHR.Runtime.Error (runtimeErrorS)
import YCHR.Runtime.Monad (Chr)
import YCHR.Runtime.Registry (HostCallFn (..), HostCallRegistry, baseHostCallRegistry)
import YCHR.Runtime.Types (Value (..))
import YCHR.Types (Constraint (..), Name (..), Term (..))
import YCHR.VM qualified as VM

-- ---------------------------------------------------------------------------
-- Classes
-- ---------------------------------------------------------------------------

-- | Encode a Haskell value as a CHR 'Term'. Total: encoding never fails.
class ToTerm a where
  toTerm :: a -> Term

-- | Decode a CHR 'Term' into a Haskell value. Fallible: the term may have
-- the wrong shape, or be an unbound variable where a ground value was
-- required. Failures are returned as data (a 'ConvertError'), never thrown.
class FromTerm a where
  fromTerm :: Term -> Either ConvertError a

-- ---------------------------------------------------------------------------
-- Errors
-- ---------------------------------------------------------------------------

-- | Why a 'Term' could not be decoded into a Haskell value.
--
-- The constructors are positional rather than record-shaped because the
-- \"what was found\" payload differs across cases ('Term' vs 'Name'), which a
-- single record could not share.
data ConvertError
  = -- | Wrong shape: a description of what was expected, and the term found.
    TypeMismatch Text Term
  | -- | Right functor, wrong argument count: functor, expected arity, found arity.
    ArityMismatch Name Int Int
  | -- | A compound whose functor matched none of a sum type's constructors:
    -- the accepted functor names, and the functor actually found.
    UnknownFunctor [Text] Name
  | -- | A ground value was required but the term was a variable or wildcard.
    UnboundValue Term
  | -- | Result-map decoding: the requested goal variable is absent.
    MissingBinding Text
  | -- | A typed query was given a goal that is not a compound term (a
    -- constraint occurrence). Carries the offending goal term.
    MalformedGoal Term
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Combinators for hand-written instances
-- ---------------------------------------------------------------------------

-- | Build an unqualified compound term (the same shape as "YCHR.DSL"'s
-- @term@). Handy in 'ToTerm' instances.
compound :: Text -> [Term] -> Term
compound n = CompoundTerm (Unqualified n)

-- | Build a nullary atom (an unqualified 0-arity compound).
atomTerm :: Text -> Term
atomTerm n = CompoundTerm (Unqualified n) []

-- | Wrap a decoder so that an unbound variable or wildcard is reported as
-- 'UnboundValue' before the decoder runs. Every scalar 'FromTerm' instance
-- uses this so \"decode a value from an unbound variable\" fails uniformly.
ground :: (Term -> Either ConvertError a) -> Term -> Either ConvertError a
ground _ t@(VarTerm _) = Left (UnboundValue t)
ground _ t@Wildcard = Left (UnboundValue t)
ground f t = f t

-- | Decode a compound with the given (local) functor name and exact arity,
-- returning its argument terms. Rejects variables/wildcards
-- ('UnboundValue'), a different functor ('UnknownFunctor'), a wrong arity
-- ('ArityMismatch'), and non-compound terms ('TypeMismatch'). The functor is
-- matched on its local part, so a result that comes back module-qualified
-- still decodes.
matchCompound :: Text -> Int -> Term -> Either ConvertError [Term]
matchCompound n arity = ground $ \t -> case t of
  CompoundTerm name args
    | nameLocal name == n ->
        if length args == arity
          then Right args
          else Left (ArityMismatch name arity (length args))
    | otherwise -> Left (UnknownFunctor [n] name)
  _ -> Left (TypeMismatch n t)

-- | Decode a sum type: dispatch on a compound's functor and arity against a
-- table of @(functor, arity, handler)@ rows. Produces 'UnknownFunctor' when
-- no row's functor matches and 'ArityMismatch' when the functor matches but
-- the arity does not.
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

-- | Decode the argument at a 0-based position with 'fromTerm'. Intended for
-- use on the argument list returned by 'matchCompound' \/ 'decodeSum', where
-- the arity has already been checked.
argAt :: (FromTerm a) => Int -> [Term] -> Either ConvertError a
argAt i args = case drop i args of
  (t : _) -> fromTerm t
  [] -> Left (TypeMismatch ("positional argument #" <> Text.pack (show i)) Wildcard)

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

-- | Strict: an 'IntTerm' is /not/ coerced to a 'Double'. Use 'Integer' \/
-- 'Int' for integral results.
instance ToTerm Double where
  toTerm = FloatTerm

instance FromTerm Double where
  fromTerm = ground $ \t -> case t of
    FloatTerm d -> Right d
    _ -> Left (TypeMismatch "Double" t)

-- | Encodes to the canonical @true@ \/ @false@ atom. Decoding also accepts
-- the @prelude@-qualified forms that appear in results.
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

-- | The idiomatic CHR string type: encodes to 'TextTerm'.
instance ToTerm Text where
  toTerm = TextTerm

instance FromTerm Text where
  fromTerm = ground $ \t -> case t of
    TextTerm s -> Right s
    _ -> Left (TypeMismatch "Text" t)

-- | A single-character 'TextTerm'. Note that @String = [Char]@ therefore
-- round-trips as a /list/ of one-character 'TextTerm's; prefer 'Text' when
-- you want a single 'TextTerm'.
instance ToTerm Char where
  toTerm c = TextTerm (Text.singleton c)

instance FromTerm Char where
  fromTerm = ground $ \t -> case t of
    TextTerm s | Text.length s == 1 -> Right (Text.head s)
    _ -> Left (TypeMismatch "Char" t)

-- | Encodes to the @()@ atom (matching the runtime's unit value).
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

-- | Prolog list encoding: cons is @.\/2@, nil is @[]@. Interoperates with
-- the @lists@ library. Decoding also accepts the @prelude@-qualified and
-- mangled cons\/nil forms that can appear in results.
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

-- | Decode a single goal variable's binding by name. 'MissingBinding' when
-- the variable is absent from the result map; otherwise delegates to
-- 'fromTerm'.
decodeVar :: (FromTerm a) => Text -> Map Text Term -> Either ConvertError a
decodeVar k m = case Map.lookup k m of
  Nothing -> Left (MissingBinding k)
  Just t -> fromTerm t

-- | Like 'decodeVar' but yields 'Nothing' for an absent variable instead of
-- failing. A present-but-undecodable binding still fails.
decodeVarMaybe :: (FromTerm a) => Text -> Map Text Term -> Either ConvertError (Maybe a)
decodeVarMaybe k m = case Map.lookup k m of
  Nothing -> Right Nothing
  Just t -> Just <$> fromTerm t

-- | Raw lookup escape hatch: the bound 'Term' for a goal variable, if any.
lookupBinding :: Text -> Map Text Term -> Maybe Term
lookupBinding = Map.lookup

-- ---------------------------------------------------------------------------
-- Typed query wrapper
-- ---------------------------------------------------------------------------

-- | Compile the modules, run the goal 'Term', and decode a single goal
-- variable's binding as a Haskell value. The goal is built exactly like a
-- rule head or "YCHR.DSL" body goal (e.g. @term \"leq\" [int 1, var \"R\"]@);
-- its 'ToTerm'-encoded arguments run at tell time.
--
-- Compilation failures are thrown as 'Error' (as 'YCHR.DSL.runDSL' does);
-- decoding failures are returned as 'Left'. Uses the base + meta host-call
-- registries and includes the standard library.
runQuery :: (FromTerm a) => [Module] -> Term -> Text -> IO (Either ConvertError a)
runQuery modules goal v = runQueryWith modules goal (decodeVar v)

-- | Like 'runQuery' but takes an explicit decoder over the whole binding
-- map, so a record can be assembled from several 'decodeVar' calls.
runQueryWith ::
  [Module] ->
  Term ->
  (Map Text Term -> Either ConvertError a) ->
  IO (Either ConvertError a)
runQueryWith = runQueryWithHostCallRegistry (baseHostCallRegistry <> metaHostCallRegistry)

-- | Like 'runQueryWith' but takes an explicit host-call registry. Use this
-- when the program calls custom @host:_@ functions registered by the
-- embedder.
runQueryWithHostCallRegistry ::
  HostCallRegistry ->
  [Module] ->
  Term ->
  (Map Text Term -> Either ConvertError a) ->
  IO (Either ConvertError a)
runQueryWithHostCallRegistry hostCalls modules goal decode =
  -- Check the goal shape before compiling, so a malformed goal is reported
  -- as data without doing (or throwing on) the compile.
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

-- | Like 'runQuery' but over an already-'CompiledProgram' instead of a
-- list of source modules. Compile once (with 'YCHR.Run.compileFiles' for
-- @.chr@ files, or 'YCHR.Run.compileParsedModules' for "YCHR.DSL"
-- modules), then run as many typed queries as you like against the same
-- program — each call is an independent run with a fresh store. This is
-- the entry point for embedding a real @.chr@ module and driving it with
-- 'ToTerm' \/ 'FromTerm'.
runQueryCompiled ::
  (FromTerm a) => CompiledProgram -> Term -> Text -> IO (Either ConvertError a)
runQueryCompiled cp goal v = runQueryCompiledWith cp goal (decodeVar v)

-- | Like 'runQueryWith' but over an already-'CompiledProgram'. Decodes the
-- whole binding map, so a record can be assembled from several 'decodeVar'
-- calls.
runQueryCompiledWith ::
  CompiledProgram ->
  Term ->
  (Map Text Term -> Either ConvertError a) ->
  IO (Either ConvertError a)
runQueryCompiledWith =
  runQueryCompiledWithHostCallRegistry (baseHostCallRegistry <> metaHostCallRegistry)

-- | Like 'runQueryWithHostCallRegistry' but over an
-- already-'CompiledProgram'. Use this when the program calls custom
-- @host:_@ functions registered by the embedder.
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

-- | A goal must be a compound term (a constraint occurrence). Unlike
-- "YCHR.DSL"'s @termToConstraint@, which crashes, this reports a malformed
-- goal as a 'ConvertError' so it flows through the errors-as-data query API.
goalConstraint :: Term -> Either ConvertError Constraint
goalConstraint (CompoundTerm n args) = Right (Constraint n args)
goalConstraint t = Left (MalformedGoal t)

-- ---------------------------------------------------------------------------
-- Host functions
-- ---------------------------------------------------------------------------

-- $hostFunctions
--
-- A @host:f(args)@ call in a CHR program is dispatched through a
-- 'HostCallRegistry'. The adapters below lift ordinary Haskell functions
-- into 'HostCallFn' entries using the same 'ToTerm' \/ 'FromTerm' classes
-- used for goals and results, so the common case needs no knowledge of the
-- runtime value representation. Assemble a registry with 'hostFunctions'
-- (or 'withDefaultHostFunctions') and pass it to
-- 'runQueryWithHostCallRegistry' \/ 'runQueryCompiledWithHostCallRegistry'.

-- | Marshal one dereferenced host-call argument 'Value' into a decoded
-- Haskell value. 'valueToTerm' recursively dereferences, so a logical
-- variable bound inside a compound argument is resolved; a genuinely
-- unbound argument becomes 'Wildcard' and 'fromTerm' rejects it as an
-- 'UnboundValue'.
argFromValue :: (FromTerm a) => Value -> Chr (Either ConvertError a)
argFromValue v = fromTerm <$> valueToTerm Map.empty v

-- | Marshal a host-function result Haskell value back into a runtime
-- 'Value'. Results are expected ground.
resultToValue :: (ToTerm r) => r -> Chr Value
resultToValue r = evalStateT (termToValue (toTerm r)) Map.empty

hostArityError :: Int -> [a] -> Chr b
hostArityError n vs =
  runtimeErrorS
    ("host call: expected " ++ show n ++ " argument(s), got " ++ show (length vs))

hostDecodeError :: ConvertError -> Chr a
hostDecodeError err = runtimeErrorS ("host call: " ++ show err)

-- | Adapt a nullary effectful action into a host function. There is no
-- pure @hostFn0@ because a nullary pure host function is just a constant;
-- use this for host calls that read external state (a clock, a fresh
-- identifier) or perform I\/O. The body runs in 'Chr' (use 'liftIO' for
-- 'IO').
hostFn0M :: (ToTerm r) => Chr r -> HostCallFn
hostFn0M act = HostCallFn $ \case
  [] -> act >>= resultToValue
  vs -> hostArityError 0 vs

-- | Adapt a pure unary Haskell function into a host function.
--
-- > hostFunctions [("shout", hostFn1 Data.Text.toUpper)]   -- host:shout(X)
hostFn1 :: (FromTerm a, ToTerm r) => (a -> r) -> HostCallFn
hostFn1 f = hostFn1M (pure . f)

-- | Effectful unary adapter: the body runs in 'Chr', so it may perform
-- I\/O (via 'liftIO'), dereference logical variables, or inspect the
-- constraint store. Arguments and result still marshal via
-- 'FromTerm' \/ 'ToTerm'.
hostFn1M :: (FromTerm a, ToTerm r) => (a -> Chr r) -> HostCallFn
hostFn1M f = HostCallFn $ \case
  [va] -> do
    ea <- argFromValue va
    case ea of
      Right a -> f a >>= resultToValue
      Left err -> hostDecodeError err
  vs -> hostArityError 1 vs

-- | Adapt a pure binary Haskell function into a host function.
--
-- > hostFunctions [("my_add", hostFn2 ((+) :: Int -> Int -> Int))]  -- host:my_add(X, Y)
hostFn2 :: (FromTerm a, FromTerm b, ToTerm r) => (a -> b -> r) -> HostCallFn
hostFn2 f = hostFn2M (\a b -> pure (f a b))

-- | Effectful binary adapter. See 'hostFn1M'.
hostFn2M :: (FromTerm a, FromTerm b, ToTerm r) => (a -> b -> Chr r) -> HostCallFn
hostFn2M f = HostCallFn $ \case
  [va, vb] -> do
    ea <- argFromValue va
    eb <- argFromValue vb
    case (,) <$> ea <*> eb of
      Right (a, b) -> f a b >>= resultToValue
      Left err -> hostDecodeError err
  vs -> hostArityError 2 vs

-- | Adapt a pure ternary Haskell function into a host function.
hostFn3 ::
  (FromTerm a, FromTerm b, FromTerm c, ToTerm r) =>
  (a -> b -> c -> r) ->
  HostCallFn
hostFn3 f = hostFn3M (\a b c -> pure (f a b c))

-- | Effectful ternary adapter. See 'hostFn1M'.
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

-- | Variable-arity escape hatch that still marshals through 'Term'. The
-- supplied function receives every argument already decoded to a 'Term'
-- (recursively dereferenced) and returns the result 'Term' or a
-- 'ConvertError'. Use it for host functions whose arity is not fixed
-- (e.g. an n-ary sum).
hostFnN :: ([Term] -> Either ConvertError Term) -> HostCallFn
hostFnN g = HostCallFn $ \vs -> do
  ts <- traverse (valueToTerm Map.empty) vs
  case g ts of
    Right t -> resultToValue t
    Left err -> hostDecodeError err

-- | The raw host-function escape hatch: build a 'HostCallFn' directly from
-- @'Value' -> 'Chr' 'Value'@, with no 'Term' marshalling. Arguments arrive
-- top-level dereferenced only (logical variables nested inside a compound
-- argument are /not/ chased — use 'YCHR.Run.deref' as needed). This is the
-- 'HostCallFn' constructor under a descriptive name, exposed so the raw
-- path needs no import of the internal runtime modules.
hostFnValues :: ([Value] -> Chr Value) -> HostCallFn
hostFnValues = HostCallFn

-- | Assemble a host-call registry from named host functions. The names are
-- the bare functors used at the call site: an entry @("my_add", …)@ is
-- invoked as @host:my_add(...)@ from CHR source. Composes with '<>'.
hostFunctions :: [(Text, HostCallFn)] -> HostCallRegistry
hostFunctions = Map.fromList . map (\(n, fn) -> (VM.Name n, fn))

-- | Like 'hostFunctions', but the given functions are unioned over the full
-- default registry (the base arithmetic \/ comparison \/ string builtins
-- plus the meta operations), so a program can call both the built-ins and
-- the custom functions. On a name clash the custom entry wins.
withDefaultHostFunctions :: [(Text, HostCallFn)] -> HostCallRegistry
withDefaultHostFunctions fns =
  hostFunctions fns <> baseHostCallRegistry <> metaHostCallRegistry
