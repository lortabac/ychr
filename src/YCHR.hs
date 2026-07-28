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
--     rather than load them.
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

    -- * Typed queries
    runQuery,
    runQueryWith,
    runQueryWithHostCallRegistry,
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
    runQuery,
    runQueryCompiled,
    runQueryCompiledWith,
    runQueryCompiledWithHostCallRegistry,
    runQueryWith,
    runQueryWithHostCallRegistry,
    withDefaultHostFunctions,
  )
import YCHR.Run
  ( CompiledProgram,
    Error (..),
    Warning (..),
    compileFiles,
    compileModules,
    runProgramWithGoal,
  )
import YCHR.Types (Name (..), Term (..))
