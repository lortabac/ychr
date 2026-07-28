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
-- The queries here run with the default host-call registry. Registering
-- your own host functions (a custom 'HostCallRegistry' built from
-- 'YCHR.Runtime.Registry.HostCallFn') is an advanced path: use the
-- @…WithHostCallRegistry@ variants in "YCHR.Convert" together with
-- "YCHR.Runtime.Registry". Other lower-level entry points — the raw CHR
-- session API, the multi-goal query API, the compiler pipeline internals —
-- likewise remain available by importing "YCHR.Run", "YCHR.Convert", and
-- the internal @YCHR.*@ modules directly.
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
    runQueryCompiled,
    runQueryCompiledWith,

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

    -- * Host-call registry
    HostCallRegistry,
    baseHostCallRegistry,

    -- * Core term types
    Term (..),
    Name (..),
  )
where

import YCHR.Convert
  ( ConvertError (..),
    FromTerm (..),
    ToTerm (..),
    argAt,
    atomTerm,
    compound,
    decodeSum,
    decodeVar,
    decodeVarMaybe,
    ground,
    lookupBinding,
    matchCompound,
    runQuery,
    runQueryCompiled,
    runQueryCompiledWith,
    runQueryWith,
  )
import YCHR.Run
  ( CompiledProgram,
    Error (..),
    Warning (..),
    compileFiles,
    compileModules,
    runProgramWithGoal,
  )
import YCHR.Runtime.Registry (HostCallRegistry, baseHostCallRegistry)
import YCHR.Types (Name (..), Term (..))
