{-# LANGUAGE OverloadedStrings #-}

-- | @ychr-codegen@: the build step that precomputes the bundled
-- resources for the MicroHs build.
--
-- It decodes @libraries\/*.chr@ and @typechecker\/*.chr@ once, at build
-- time, and writes two Haskell modules holding the result as literal
-- data. The MicroHs @ychr@ executable compiles those modules instead of
-- parsing the standard library and compiling the type-checker on every
-- process, which is the fixed per-process cost measured in
-- @dev-docs\/MICROHS_PERFORMANCE.md@ §3.
--
-- Invoked by @make resources@; see that target for the output
-- directory. @--check@ re-emits in memory and diffs against what is on
-- disk, so a stale @generated\/@ can be detected without rewriting it.
module Main (main) where

import Data.Text (Text)
import Data.Text qualified as T
import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)
import System.FilePath (takeDirectory, (</>))
import System.IO (hPutStrLn, stderr)
import YCHR.Embedded.Generate.Emit
  ( EmitOptions (..),
    GeneratedModule (..),
    defaultEmitOptions,
    emitStdLib,
    emitTypeChecker,
  )
import YCHR.Internal.Resources (readChrDir)
import YCHR.Internal.StdLib (parseStdLib)
import YCHR.Internal.TypeCheck.Compiled (compileTypeCheckerModules)

-- | Where to read from, where to write to, and how finely to split.
data Options = Options
  { optRoot :: FilePath,
    optOut :: FilePath,
    optCheck :: Bool,
    optEmit :: EmitOptions
  }

defaultOptions :: Options
defaultOptions =
  Options
    { optRoot = ".",
      optOut = "generated",
      optCheck = False,
      optEmit = defaultEmitOptions
    }

main :: IO ()
main = do
  args <- getArgs
  case parseArgs defaultOptions args of
    Left err -> usage err
    Right (Left message) -> putStrLn message
    Right (Right opts) -> run opts

run :: Options -> IO ()
run opts = do
  let libraryDir = opts.optRoot </> "libraries"
      typeCheckerDir = opts.optRoot </> "typechecker"
  libraries <- readChrDir libraryDir
  typechecker <- readChrDir typeCheckerDir
  case loadBoth libraryDir typeCheckerDir libraries typechecker of
    Left err -> failWith (T.unpack err)
    Right (librarySources, typecheckerSources) ->
      case parseStdLib librarySources of
        Left err -> failWith ("cannot parse the standard library: " ++ show err)
        Right stdlib ->
          case compileTypeCheckerModules stdlib typecheckerSources of
            Left err -> failWith ("cannot compile the type-checker: " ++ show err)
            Right session ->
              let modules =
                    [ emitStdLib opts.optEmit stdlib,
                      emitTypeChecker opts.optEmit session
                    ]
               in if opts.optCheck
                    then checkModules opts modules
                    else writeModules opts modules

-- | Both directories' sources, or the first error either loader or the
-- emptiness check reports.
loadBoth ::
  FilePath ->
  FilePath ->
  Either Text [(FilePath, Text)] ->
  Either Text [(FilePath, Text)] ->
  Either Text ([(FilePath, Text)], [(FilePath, Text)])
loadBoth libraryDir typeCheckerDir libraries typechecker = do
  librarySources <- requireSources libraryDir libraries
  typecheckerSources <- requireSources typeCheckerDir typechecker
  pure (librarySources, typecheckerSources)

-- | An empty directory is almost always a root one level off, and an
-- empty standard library would otherwise be accepted silently — the
-- same rule "YCHR.Internal.Resources.loadResourcesAt" applies.
requireSources ::
  FilePath ->
  Either Text [(FilePath, Text)] ->
  Either Text [(FilePath, Text)]
requireSources dir result = do
  sources <- result
  if null sources
    then
      Left
        ( "resource directory has no .chr sources: "
            <> T.pack dir
            <> " (is --root pointing at a YCHR source tree?)"
        )
    else Right sources

failWith :: String -> IO a
failWith message = do
  hPutStrLn stderr ("ychr-codegen: " ++ message)
  exitFailure

-- ---------------------------------------------------------------------------
-- Writing and checking
-- ---------------------------------------------------------------------------

-- | Read a file and force its contents.
--
-- A lazy 'readFile' would leave the handle open when a comparison
-- short-circuits on the first difference, and rewriting the same path
-- then fails with @resource busy (file is locked)@.
readStrict :: FilePath -> IO String
readStrict path = do
  contents <- readFile path
  length contents `seq` pure contents

-- | Write each module, touching a file only when its contents actually
-- change: @mcabal@ rebuilds a component whose source file it sees
-- modified, and a regenerated file with identical contents would cause
-- a needless rebuild of a multi-megabyte module.
writeModules :: Options -> [GeneratedModule] -> IO ()
writeModules opts = mapM_ writeOne
  where
    writeOne m = do
      let path = opts.optOut </> m.modulePath
      createDirectoryIfMissing True (takeDirectory path)
      exists <- doesFileExist path
      same <-
        if exists
          then (== m.moduleSource) <$> readStrict path
          else pure False
      if same
        then putStrLn ("unchanged " ++ path)
        else do
          writeFile path m.moduleSource
          putStrLn ("wrote " ++ path)

-- | Report every module whose file is missing or differs from what the
-- current sources would generate, and exit non-zero if there is any.
checkModules :: Options -> [GeneratedModule] -> IO ()
checkModules opts modules = do
  problems <- concat <$> mapM checkOne modules
  if null problems
    then putStrLn "generated resources are up to date"
    else do
      mapM_ (hPutStrLn stderr) problems
      hPutStrLn stderr "run `make resources` to regenerate"
      exitFailure
  where
    checkOne m = do
      let path = opts.optOut </> m.modulePath
      exists <- doesFileExist path
      if not exists
        then pure ["missing: " ++ path]
        else do
          current <- readStrict path
          pure ["stale: " ++ path | current /= m.moduleSource]

-- ---------------------------------------------------------------------------
-- Command line
-- ---------------------------------------------------------------------------

-- | Parse the arguments. @Left@ is a usage error, @Right (Left message)@
-- is @--help@ (a message to print and exit successfully).
parseArgs :: Options -> [String] -> Either String (Either String Options)
parseArgs opts [] = Right (Right opts)
parseArgs opts ("--root" : value : rest) =
  parseArgs opts {optRoot = value} rest
parseArgs opts ("--out" : value : rest) =
  parseArgs opts {optOut = value} rest
parseArgs opts ("--chunk" : value : rest) = do
  n <- positive "--chunk" value
  parseArgs opts {optEmit = opts.optEmit {chunkSize = n}} rest
parseArgs opts ("--max-binding-bytes" : value : rest) = do
  n <- positive "--max-binding-bytes" value
  parseArgs opts {optEmit = opts.optEmit {maxBindingBytes = n}} rest
parseArgs opts ("--check" : rest) = parseArgs opts {optCheck = True} rest
parseArgs _ ("--help" : _) = Right (Left help)
parseArgs _ ("-h" : _) = Right (Left help)
parseArgs _ (arg : _) = Left ("unexpected argument: " ++ arg)

positive :: String -> String -> Either String Int
positive flag value = case reads value of
  [(n, "")] | n > 0 -> Right n
  _ -> Left (flag ++ " needs a positive integer, got: " ++ value)

usage :: String -> IO ()
usage err = do
  prog <- getProgName
  hPutStrLn stderr (prog ++ ": " ++ err)
  hPutStrLn stderr ""
  hPutStrLn stderr help
  exitFailure

help :: String
help =
  unlines
    [ "Usage: ychr-codegen [--root DIR] [--out DIR] [--check]",
      "                    [--chunk N] [--max-binding-bytes N]",
      "",
      "Decode DIR/libraries/*.chr and DIR/typechecker/*.chr and write the",
      "generated resource modules under OUT (default: --root . --out generated).",
      "",
      "  --check                  report stale or missing modules, write nothing",
      "  --chunk N                maximum list elements per binding (default 32)",
      "  --max-binding-bytes N    maximum characters per binding (default 8192)"
    ]
