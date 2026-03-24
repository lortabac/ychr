module YCHR.EndToEnd
  ( Error (..),
    compileModules,
    compileFiles,
  )
where

import Data.Bifunctor (first)
import Data.Text (Text)
import Data.Text.IO qualified as TIO
import Data.Void (Void)
import Text.Megaparsec (ParseErrorBundle)
import YCHR.Compile (CompileError, compile)
import YCHR.Desugar (DesugarError, desugarProgram, extractSymbolTable)
import YCHR.Parser (parseModule)
import YCHR.Rename (RenameError, renameProgram)
import YCHR.VM (Program)

data Error
  = ParseError FilePath (ParseErrorBundle Text Void)
  | RenameErrors [RenameError]
  | DesugarErrors [DesugarError]
  | CompileErrors [CompileError]
  deriving (Show)

compileModules :: [(FilePath, Text)] -> Either Error Program
compileModules inputs = do
  parsed <- mapM (\(fp, txt) -> first (ParseError fp) (parseModule fp txt)) inputs
  renamed <- first RenameErrors (renameProgram parsed)
  desugared <- first DesugarErrors (desugarProgram renamed)
  let symTab = extractSymbolTable desugared
  first CompileErrors (compile desugared symTab)

compileFiles :: [FilePath] -> IO (Either Error Program)
compileFiles paths = do
  contents <- mapM (\fp -> (fp,) <$> TIO.readFile fp) paths
  pure (compileModules contents)
