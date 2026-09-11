{-# LANGUAGE OverloadedStrings #-}

-- | The entry point for embedding YCHR as a Haskell library: compile a
-- CHR program (from @.chr@ files or in-memory sources), run goals against
-- it, and marshal Haskell values in and out with 'ToTerm' \/ 'FromTerm'.
-- @import YCHR@ is all most embedders need.
--
-- Worked examples:
-- <https://github.com/lortabac/ychr/blob/master/README.md#using-ychr-as-a-haskell-library>
-- and
-- <https://github.com/lortabac/ychr/blob/master/docs/how-to/embed-a-chr-module.md>.
--
-- = Opt-in companions
--
-- Not re-exported here:
--
--   * "YCHR.DSL" — build programs in Haskell instead of loading @.chr@
--     source. Its @Module@ values are queried with 'YCHR.Convert.runQuery'
--     and friends, which live in "YCHR.Convert"; this umbrella covers the
--     @.chr@-source path only.
--
--   * "YCHR.Convert.Generic" (GHC only) — @genericToTerm@ \/
--     @genericFromTerm@ for @deriving 'GHC.Generics.Generic'@ types. Kept
--     separate so this module and "YCHR.Convert" stay @Generic@-free.
--
-- = Registering host functions
--
-- A @host:f(args)@ call resolves against a 'HostCallRegistry'. Lift Haskell
-- functions with 'hostFn1' \/ 'hostFn2' \/ … (or the effectful @…M@
-- variants), assemble with 'withDefaultHostFunctions', run with a
-- @…WithHostCallRegistry@ query variant. User entries override built-ins
-- of the same name. See
-- <https://github.com/lortabac/ychr/blob/master/docs/how-to/call-host-functions.md>.
--
-- Lower-level entry points (raw sessions, multi-goal queries, pipeline
-- stages) are in "YCHR.Run", "YCHR.Convert", and the @YCHR.Internal.*@ modules.
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

    -- ** The quote/1 quoting form
    quote,

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
    quote,
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
-- A 'hostFnValues' handler receives raw 'Value's, possibly bound logical
-- variables. All of these run in 'Chr':
--
--   * 'deref' — follow a variable chain to its binding (or the unbound
--     variable at the end). Call it before pattern-matching on a 'Value',
--     or a bound variable looks like a 'VVar'.
--
--   * 'equal' — CHR @==@ (ask): structural, never binds, two distinct
--     unbound variables are unequal. There is deliberately no 'Eq'
--     instance: a derived one would compare variables by reference.
--
--   * 'newVar' — a fresh unbound logical variable.
--
-- The 'hostFn1' \/ 'hostFn2' \/ … adapters dereference for you; these
-- matter only with 'hostFnValues'.
--
-- Binding is not offered here. @unify@ ("YCHR.Run") returns the
-- constraints observing the variables it bound, and the caller must
-- enqueue them for reactivation or they silently never wake up. Return a
-- value and let the generated code unify instead.
