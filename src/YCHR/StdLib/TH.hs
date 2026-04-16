{-# LANGUAGE TemplateHaskell #-}

-- | TemplateHaskell splice for embedding standard library files.
module YCHR.StdLib.TH (readLibraries) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Language.Haskell.TH (Code, Q, runIO)
import Language.Haskell.TH.Syntax (Lift (..), addDependentFile, unsafeCodeCoerce)
import System.Directory (listDirectory)
import System.FilePath (dropExtension, takeExtension, takeFileName, (</>))
import YCHR.Parsed (Module)
import YCHR.Parser (ModuleHeader (..), OpTable, builtinOps, collectModuleHeader, mergeOps, parseModuleWith)

readLibraries :: Code Q (Map Text Module)
readLibraries = unsafeCodeCoerce $ do
  let dir = "libraries"
  files <- runIO $ filter ((== ".chr") . takeExtension) <$> listDirectory dir
  -- Read all library source files and register dependencies
  sources <- mapM (readSource dir) files
  -- Collect operator declarations from all library sources via the
  -- lightweight first-pass header parser. Stdlib libraries are mutually
  -- trusted, so we merge every operator into one table for parsing them.
  allOps <- case mapM (\(fp, src) -> collectModuleHeader fp (T.pack src)) sources of
    Left err -> fail ("Failed to collect operators from libraries: " ++ show err)
    Right hdrs -> pure (concatMap (.exportOps) hdrs)
  -- Merge with builtins
  table <- case mergeOps builtinOps allOps of
    Left conflict -> fail ("Operator naming conflict in libraries: " ++ T.unpack conflict)
    Right t -> pure t
  -- Parse each library with the merged operator table
  entries <- mapM (parseLib table) sources
  lift (Map.fromList entries)

readSource :: FilePath -> FilePath -> Q (FilePath, String)
readSource dir file = do
  let path = dir </> file
  addDependentFile path
  contents <- runIO (readFile path)
  pure (path, contents)

parseLib :: OpTable -> (FilePath, String) -> Q (Text, Module)
parseLib table (path, contents) =
  let name = T.pack (dropExtension (takeFileName path))
   in case parseModuleWith table path (T.pack contents) of
        Left err -> fail ("Failed to parse library " ++ path ++ ": " ++ show err)
        Right m -> pure (name, m)
