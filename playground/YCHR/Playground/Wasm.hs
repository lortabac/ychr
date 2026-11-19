{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ImportQualifiedPost #-}

-- | The WASM bridge: the five C entry points the page calls, on top of
-- "YCHR.Playground".
--
-- This module is compiled only by the WASM build (@make playground-wasm@,
-- which invokes @mhs@ directly). It is deliberately /not/ listed in
-- @ychr.cabal@, so the GHC build never sees the @foreign export@
-- declarations and the native harness links the bridge logic alone.
--
-- The protocol is the response envelope documented in "YCHR.Playground":
-- every function returns a freshly allocated UTF-8 C string that the
-- caller must hand back to @ychr_pg_free@.
--
-- Strings are marshalled with 'peekCString' and 'newCString', which are
-- MicroHs's UTF-8 pair. (The @…AString@ names are the /eight-bit/ pair
-- there — the opposite of GHC's convention — and would truncate any
-- character the compiler generates outside Latin-1, such as the em dash
-- in a diagnostic.)
--
-- @mhs_init()@ (emitted by the MicroHs runtime, exported to JavaScript
-- by the build) brings the runtime up; the module is built with
-- @-sINVOKE_RUN=0@, so the @main@ below never runs — it exists only
-- because the MicroHs compiler wants a @main@ binding in the entry
-- module.
--
-- State lives in one 'IORef' because the page calls these functions one
-- at a time and the loaded program must survive between calls. The
-- exported closures are GC roots in the MicroHs runtime (the @ffe@ table
-- is marked on every collection), so the reference stays valid across
-- calls.
module YCHR.Playground.Wasm
  ( main,
  )
where

import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Text qualified as T
import Foreign.C.String (newCString, peekCString)
import Foreign.C.Types (CChar)
import Foreign.Marshal.Alloc (free)
import Foreign.Ptr (Ptr)
import System.IO.Unsafe (unsafePerformIO)
import YCHR.Embedded qualified as Embedded
import YCHR.Internal.Resources (Resources (Resources))
import YCHR.Playground
  ( Playground,
    Step (..),
    newPlayground,
    reload,
    response,
    runReplLine,
    statusError,
    statusOk,
    typecheck,
  )

-- | The MicroHs entry point. Never called: the module is built with
-- @INVOKE_RUN=0@ and JavaScript drives it through the exports below
-- after calling @mhs_init()@.
main :: IO ()
main = pure ()

-- ---------------------------------------------------------------------------
-- State
-- ---------------------------------------------------------------------------

{-# NOINLINE stateRef #-}

-- | The loaded playground, or 'Nothing' before a successful
-- @ychr_pg_init@.
stateRef :: IORef (Maybe Playground)
stateRef = unsafePerformIO (newIORef Nothing)

-- ---------------------------------------------------------------------------
-- Exports
-- ---------------------------------------------------------------------------

foreign export ccall "ychr_pg_init" pgInit :: IO (Ptr CChar)

foreign export ccall "ychr_pg_compile" pgCompile :: Ptr CChar -> IO (Ptr CChar)

foreign export ccall "ychr_pg_query" pgQuery :: Ptr CChar -> IO (Ptr CChar)

foreign export ccall "ychr_pg_check" pgCheck :: IO (Ptr CChar)

foreign export ccall "ychr_pg_free" pgFree :: Ptr CChar -> IO ()

-- | Make the playground ready, on the resources built into the module
-- (the standard library and the compiled type checker, decoded at build
-- time by @make resources@). Nothing is read or parsed here. A second
-- call drops whatever program was loaded.
pgInit :: IO (Ptr CChar)
pgInit = do
  writeIORef stateRef (Just (newPlayground resources))
  newCString (response statusOk "ready\n")
  where
    resources = Resources Embedded.stdlib Embedded.typeCheckerProgram

-- | Compile the editor's text (never type-checking it).
pgCompile :: Ptr CChar -> IO (Ptr CChar)
pgCompile srcPtr = do
  src <- peekCString srcPtr
  withState (\pg -> reload pg (T.pack src))

-- | Run one line from the REPL pane: a goal, or a colon command.
pgQuery :: Ptr CChar -> IO (Ptr CChar)
pgQuery linePtr = do
  line <- peekCString linePtr
  withState (\pg -> runReplLine pg (T.pack line))

-- | Type-check the loaded program. The slow call: seconds per check.
pgCheck :: IO (Ptr CChar)
pgCheck = withState typecheck

-- | Release a string returned by any of the four calls above.
pgFree :: Ptr CChar -> IO ()
pgFree = free

-- ---------------------------------------------------------------------------
-- Plumbing
-- ---------------------------------------------------------------------------

-- | Run an operation against the loaded playground, store the updated
-- state, and marshal the response out. Reports a missing 'pgInit'
-- instead of failing when the page calls out of order.
withState :: (Playground -> IO Step) -> IO (Ptr CChar)
withState act = do
  loaded <- readIORef stateRef
  case loaded of
    Nothing -> newCString (response statusError "Playground not initialised.\n")
    Just pg -> do
      Step {playground = pg', output = out} <- act pg
      writeIORef stateRef (Just pg')
      newCString out
