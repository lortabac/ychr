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
import System.FilePath (dropExtension, takeExtension, (</>))
import YCHR.Parsed (Module)
import YCHR.Parser (parseModule)

readLibraries :: Code Q (Map Text Module)
readLibraries = unsafeCodeCoerce $ do
  let dir = "libraries"
  files <- runIO $ filter ((== ".chr") . takeExtension) <$> listDirectory dir
  entries <- mapM (readLibrary dir) files
  lift (Map.fromList entries)

readLibrary :: FilePath -> FilePath -> Q (Text, Module)
readLibrary dir file = do
  let path = dir </> file
      name = T.pack (dropExtension file)
  addDependentFile path
  contents <- runIO (readFile path)
  case parseModule path (T.pack contents) of
    Left err -> fail ("Failed to parse library " ++ file ++ ": " ++ show err)
    Right m -> pure (name, m)
