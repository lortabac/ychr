{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | Native harness for the playground bridge.
--
-- Runs the same operations as the page against the same
-- "YCHR.Playground" engine, reading a small command script on stdin and
-- writing one response per command followed by a @---@ framing line.
-- This is what @test\/playground\/test_native.py@ drives, so the bridge
-- can be tested — and debugged — without emscripten or a browser.
--
-- Commands:
--
-- > :load FILE         compile FILE as the loaded program
-- > :text              program text, until a line containing only "."
-- > :query LINE        one REPL line: a goal or a colon command
-- > :check             type-check the loaded program
-- > :quit              stop
--
-- Anything else — a goal, or a colon command such as @:help@ or
-- @:info@ — goes to the same dispatcher the page uses.
--
-- Every script ends with @:quit@: the harness reads with bare 'getLine',
-- which is all MicroHs offers, and an EOF would raise rather than end
-- the loop.
module Main (main) where

import Control.Exception (SomeException, displayException, try)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Environment (lookupEnv)
import System.Exit (exitFailure)
import System.IO (hFlush, hPutStr, stdout)
import YCHR.Playground
  ( Playground,
    initPlayground,
    reload,
    response,
    runReplLine,
    statusError,
    typecheck,
  )

main :: IO ()
main = do
  root <- resolveRoot
  result <- initPlayground root
  case result of
    Left err -> do
      hPutStr stdout (response statusError (err ++ "\n"))
      hFlush stdout
      exitFailure
    Right pg -> readCommand pg

-- | The resource root: @$YCHR_LIB_DIR@ when set, otherwise the current
-- directory — the same convention @YCHR.Internal.Resources@ uses.
resolveRoot :: IO FilePath
resolveRoot = do
  env <- lookupEnv "YCHR_LIB_DIR"
  pure $ case env of
    Just dir | not (null dir) -> dir
    _ -> "."

-- | Read commands until @:quit@. The playground is threaded explicitly,
-- so the loaded program survives a failed reload exactly as it does in
-- the browser.
--
-- Only the harness's own commands are handled here (file loading and
-- inline text); everything else — goals and the page's colon commands —
-- is forwarded to 'runReplLine', so the harness and the browser go
-- through the same dispatcher.
readCommand :: Playground -> IO ()
readCommand pg = do
  line <- getLine
  case words line of
    [] -> readCommand pg
    (":quit" : _) -> pure ()
    (":load" : rest) -> case rest of
      [] -> emit (pg, response statusError "usage: :load FILE\n")
      (file : _) -> do
        contents <- try @SomeException (TIO.readFile file)
        case contents of
          Left exc ->
            emit (pg, response statusError ("Error: " ++ displayException exc ++ "\n"))
          Right text -> run (reload pg text)
    (":text" : _) -> do
      src <- readProgramText
      run (reload pg (T.pack src))
    -- The page has a Typecheck button; the harness needs a command for
    -- the same operation.
    (":check" : _) -> run (typecheck pg)
    -- An explicit goal command, for scripts that read better with one.
    (":query" : rest) -> run (runReplLine pg (T.pack (unwords rest)))
    _ -> run (runReplLine pg (T.pack line))

-- | Run an operation, print its response with the framing line the tests
-- split on, and continue with the updated state.
run :: IO (Playground, String) -> IO ()
run act = do
  (pg', out) <- act
  emit (pg', out)

emit :: (Playground, String) -> IO ()
emit (pg, out) = do
  hPutStr stdout (out ++ "\n---\n")
  hFlush stdout
  readCommand pg

-- | Program text terminated by a line containing only @.@.
readProgramText :: IO String
readProgramText = go []
  where
    go acc = do
      line <- getLine
      if line == "."
        then pure (unlines (reverse acc))
        else go (line : acc)
