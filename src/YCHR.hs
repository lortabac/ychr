{-# LANGUAGE OverloadedStrings #-}

-- | The entry point for embedding YCHR as a Haskell library.
--
-- This umbrella module gathers the common /compile-and-query/ surface into
-- a single import: compile a CHR program (from @.chr@ files or in-memory
-- sources), run goals against it, and marshal ordinary Haskell values in
-- and out with 'ToTerm' / 'FromTerm'. For most embedders,
--
-- > import YCHR
--
-- is all that is needed.
--
-- = Worked example: compile once, query many
--
-- > {-# LANGUAGE OverloadedStrings #-}
-- > import YCHR
-- >
-- > main :: IO ()
-- > main =
-- >   case compileModules True [("Order.chr", source)] of
-- >     Left err -> fail (show err)
-- >     Right (cp, _warnings) -> do
-- >       -- goal is a 'Term'; decode the "R" binding as a Haskell Int
-- >       r <- runQueryCompiled cp goal "R"
-- >       print (r :: Either ConvertError Int)
-- >   where
-- >     source = "..."               -- CHR source text
-- >     goal   = CompoundTerm (Unqualified "compute") [VarTerm "R"]
--
-- = Opt-in companions
--
-- Two capabilities live in their own modules and are intentionally /not/
-- re-exported here:
--
--   * "YCHR.DSL" — build CHR programs in Haskell (rules, functions, type
--     declarations) without @.chr@ source, using a combinator vocabulary
--     with operators. Import it directly when you construct programs
--     rather than load them. Its @Module@ values are queried with
--     'YCHR.Convert.runQuery' \/ 'YCHR.Convert.runQueryWith' \/
--     'YCHR.Convert.runQueryWithHostCallRegistry', which live in
--     "YCHR.Convert" alongside the DSL rather than here — this umbrella
--     covers the @.chr@-source path only.
--
--   * "YCHR.Convert.Generic" (GHC only) — @genericToTerm@ /
--     @genericFromTerm@ for @deriving 'GHC.Generics.Generic'@ types. It is
--     GHC-only; this umbrella and the core "YCHR.Convert" stay
--     @Generic@-free so they remain usable on every backend.
--
-- = Registering host functions
--
-- A @host:f(args)@ call in a CHR program is resolved against a
-- 'HostCallRegistry'. Beyond the built-ins, you can register your own by
-- lifting ordinary Haskell functions with 'hostFn1' \/ 'hostFn2' \/ … (or
-- their effectful @…M@ variants), assembling a registry with
-- 'withDefaultHostFunctions', and running with the
-- @…WithHostCallRegistry@ query variants:
--
-- > registry :: HostCallRegistry
-- > registry = withDefaultHostFunctions
-- >   [ ("my_add", hostFn2 ((+) :: Int -> Int -> Int)) ]  -- called as host:my_add(X, Y)
-- >
-- > main = do
-- >   r <- runQueryCompiledWithHostCallRegistry registry cp goal "R"
-- >   print (r :: Either ConvertError Int)
--
-- User entries override built-ins of the same name. Arguments and results
-- marshal through 'ToTerm' \/ 'FromTerm'; for I\/O or logic-variable access
-- use the @…M@ adapters (the body runs in 'Chr') or the raw 'hostFnValues'
-- escape hatch.
--
-- Other lower-level entry points — the raw CHR session API, the multi-goal
-- query API, the compiler pipeline internals — remain available by
-- importing "YCHR.Run", "YCHR.Convert", and the internal @YCHR.*@ modules
-- directly.
module YCHR
  ( -- * Compiling a program
    compileFiles,
    compileModules,
    CompiledProgram,
    Error (..),
    Warning (..),
    displayError,
    displayWarning,

    -- * Typed queries
    runQueryCompiled,
    runQueryCompiledWith,
    runQueryCompiledWithHostCallRegistry,

    -- * Raw-goal queries
    runProgramWithGoal,

    -- * Value marshalling
    ToTerm (..),
    FromTerm (..),
    ConvertError (..),

    -- ** Combinators for hand-written instances
    compound,
    atomTerm,
    matchCompound,
    decodeSum,
    argAt,
    ground,

    -- ** Result decoding
    decodeVar,
    decodeVarMaybe,
    lookupBinding,

    -- * Host functions
    HostCallRegistry,
    baseHostCallRegistry,
    HostCallFn (..),
    hostFunctions,
    withDefaultHostFunctions,
    hostFn0M,
    hostFn1,
    hostFn1M,
    hostFn2,
    hostFn2M,
    hostFn3,
    hostFn3M,
    hostFnN,
    hostFnValues,
    Chr,
    Value (..),

    -- ** Inspecting runtime values
    -- $runtimeValues
    deref,
    equal,
    newVar,

    -- * Core term types
    Term (..),
    Name (..),
  )
where

import YCHR.Convert
  ( Chr,
    ConvertError (..),
    FromTerm (..),
    HostCallFn (..),
    HostCallRegistry,
    ToTerm (..),
    Value (..),
    argAt,
    atomTerm,
    baseHostCallRegistry,
    compound,
    decodeSum,
    decodeVar,
    decodeVarMaybe,
    ground,
    hostFn0M,
    hostFn1,
    hostFn1M,
    hostFn2,
    hostFn2M,
    hostFn3,
    hostFn3M,
    hostFnN,
    hostFnValues,
    hostFunctions,
    lookupBinding,
    matchCompound,
    runQueryCompiled,
    runQueryCompiledWith,
    runQueryCompiledWithHostCallRegistry,
    withDefaultHostFunctions,
  )
import YCHR.Run
  ( CompiledProgram,
    Error (..),
    Warning (..),
    compileFiles,
    compileModules,
    deref,
    displayError,
    displayWarning,
    equal,
    newVar,
    runProgramWithGoal,
  )
import YCHR.Types (Name (..), Term (..))

-- $runtimeValues
-- A 'hostFnValues' handler receives raw 'Value's, which may be logical
-- variables that are bound to something else. Inspect them with these,
-- all of which run in 'Chr':
--
--   * 'deref' — follow a variable chain to the value it is bound to (or to
--     the unbound variable at the end). Call this before pattern-matching
--     on a 'Value' constructor, or a bound variable will look like a
--     'VVar' rather than its binding.
--
--   * 'equal' — CHR's @==@ (\"ask\") semantics: structural equality that
--     never binds, and where two distinct unbound variables compare
--     unequal. This is the correct comparison for 'Value'; there is
--     deliberately no 'Eq' instance, since a derived one would compare
--     variables by reference and silently disagree with the language.
--
--   * 'newVar' — allocate a fresh unbound logical variable.
--
-- The @hostFn1@ \/ @hostFn2@ \/ … adapters dereference for you, so reach
-- for these only with the raw 'hostFnValues' escape hatch.
--
-- Binding is deliberately not offered here. @unify@ (in "YCHR.Run")
-- returns the constraints that observe the variables it bound, and the
-- caller must hand them to the reactivation queue or those constraints
-- silently never wake up. Returning a value from your handler and letting
-- the generated code do the unification is the safe path; reach for
-- "YCHR.Run" only if you are driving a session yourself.
