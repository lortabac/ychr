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
import YCHR.Playground
  ( Playground,
    initPlayground,
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
-- Lexical state
-- ---------------------------------------------------------------------------

{-# NOINLINE stateRef #-}

-- | The loaded playground, or 'Nothing' before a successful
-- @ychr_pg_init@.
stateRef :: IORef (Maybe Playground)
stateRef = unsafePerformIO (newIORef Nothing)

-- ---------------------------------------------------------------------------
-- Exports
-- ---------------------------------------------------------------------------

foreign export ccall "ychr_pg_init" pgInit :: Ptr CChar -> IO (Ptr CChar)

foreign export ccall "ychr_pg_compile" pgCompile :: Ptr CChar -> IO (Ptr CChar)

foreign export ccall "ychr_pg_query" pgQuery :: Ptr CChar -> IO (Ptr CChar)

foreign export ccall "ychr_pg_check" pgCheck :: IO (Ptr CChar)

foreign export ccall "ychr_pg_free" pgFree :: Ptr CChar -> IO ()

-- | Load @libraries\/@ and @typechecker\/@ from the root the page passes
-- (the preloaded directories are mounted at @\/@), and make the
-- playground ready. Repeatable, not idempotent: a second call re-parses
-- the standard library and drops whatever program was loaded.
pgInit :: Ptr CChar -> IO (Ptr CChar)
pgInit rootPtr = do
  root <- peekCString rootPtr
  result <- initPlayground root
  case result of
    Left err -> newCString (response statusError (err ++ "\n"))
    Right pg -> do
      writeIORef stateRef (Just pg)
      newCString (response statusOk "ready\n")

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

-- | Type-check the loaded program, forcing the type checker on first
-- use. This is the call that blocks for a long time the first time.
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
withState :: (Playground -> IO (Playground, String)) -> IO (Ptr CChar)
withState act = do
  loaded <- readIORef stateRef
  case loaded of
    Nothing -> newCString (response statusError "Playground not initialised.\n")
    Just pg -> do
      (pg', out) <- act pg
      writeIORef stateRef (Just pg')
      newCString out
