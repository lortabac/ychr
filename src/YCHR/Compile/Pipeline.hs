{-# LANGUAGE OverloadedStrings #-}

-- | The compilation pipeline: parsing, renaming, resolving, desugaring,
-- and compiling CHR modules to VM programs.
--
-- Extracted from "YCHR.Run" so that 'compileModules' can be imported by
-- the type-checker TH splice without creating a circular dependency.
module YCHR.Compile.Pipeline
  ( -- * Compilation
    Error (..),
    Warning (..),
    CompiledProgram (..),
    ExportResolution (..),
    compileModules,
    compileFiles,
  )
where

import Control.Exception (Exception)
import Data.Bifunctor (first)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Void (Void)
import Language.Haskell.TH.Syntax (Lift)
import Text.Megaparsec (ParseErrorBundle)
import YCHR.Collect (CollectError, addLibraryPrelude, resolveLibraryClosure, rewriteImports)
import YCHR.Compile (CompileError, compile)
import YCHR.Desugar (DesugarError, desugarProgram, extractSymbolTable, liftAllLambdas)
import YCHR.Desugared qualified as D
import YCHR.Diagnostic (Diagnostic)
import YCHR.Parsed (AnnP (..), Import (..), Module (..), noAnnP)
import YCHR.Parser (ModuleHeader (..), OpTable, ParseValidationError (..), buildModuleOpTable, builtinOps, collectModuleHeader, extractOpDecls, mergeOps, parseModuleWith)
import YCHR.Rename (RenameError, RenameInputs (..), RenameWarning, buildExportEnv, renameProgram)
import YCHR.Rename.Types (toListExport)
import YCHR.Resolve (ResolveError, resolveProgram)
import YCHR.Resolved qualified as R
import YCHR.StdLib (stdlib)
import YCHR.Types (SymbolTable)
import YCHR.Types qualified as Types
import YCHR.VM (Program)

data Error
  = ParseError FilePath (ParseErrorBundle Text Void)
  | ParseValidationErrors [AnnP ParseValidationError]
  | CollectErrors [Diagnostic CollectError]
  | RenameErrors [Diagnostic RenameError]
  | DesugarErrors [Diagnostic DesugarError]
  | ResolveErrors [Diagnostic ResolveError]
  | CompileErrors [Diagnostic CompileError]
  | OperatorConflict (AnnP Text)
  deriving (Show)

instance Exception Error

data Warning
  = RenameWarnings [Diagnostic RenameWarning]
  deriving (Show)

-- | A compiled CHR program together with module visibility information.
data CompiledProgram = CompiledProgram
  { program :: Program,
    exportMap :: Map Types.UnqualifiedIdentifier ExportResolution,
    exportedSet :: Set Types.QualifiedIdentifier,
    symbolTable :: SymbolTable,
    allModules :: [Module],
    opTable :: OpTable,
    -- | All functions in the desugared program (for call dispatch in queries).
    allFunctions :: [D.Function],
    -- | Counter for the next lambda index (to avoid collisions in queries).
    nextLambdaIndex :: Int,
    -- | Set of declared function names (for query goal classification).
    functionNameSet :: Set Types.Name,
    -- | The desugared program (before lambda lifting), for type checking.
    desugaredProgram :: D.Program
  }

data ExportResolution
  = UniqueExport Types.Name
  | AmbiguousExport [Text]
  deriving (Show, Eq, Lift)

compileModules :: Bool -> [(FilePath, Text)] -> Either Error (CompiledProgram, [Warning])
compileModules includeStdlib inputs = do
  -- Phase 1: lightweight first parse of each user file to collect the
  -- module name, exported operators, header use_module imports, and the
  -- location at which header parsing stopped.
  userHeaders <-
    first (\(fp, e) -> ParseError fp e) $
      traverse (\(fp, src) -> (fp,) <$> first' (fp,) (collectModuleHeader fp src)) inputs
  -- Resolve the transitive closure of library imports starting from the
  -- libraries each user header asks for (plus prelude as an implicit
  -- seed, and every stdlib library if includeStdlib is True).
  let userLibrarySeeds =
        noAnnP "prelude"
          : [AnnP n loc p | (_, h) <- userHeaders, AnnP (LibraryImport n _) loc p <- h.headerImports]
  libraryMods <- first CollectErrors (resolveLibraryClosure includeStdlib stdlib userLibrarySeeds)
  -- Build the module-name → exported-operators map used by per-module op
  -- table construction and by the renamer's UnknownOperatorImport check.
  let stdlibOpExports = Map.fromList [(m.name, extractOpDecls m) | m <- libraryMods]
      userOpExports = Map.fromList [(h.modName, h.exportOps) | (_, h) <- userHeaders]
      opExports = stdlibOpExports `Map.union` userOpExports
      preludeOps = Map.findWithDefault [] "prelude" opExports
  -- Build per-module operator tables and full-parse each user file with
  -- its specific table. A first conflict in any table aborts the whole
  -- compilation with OperatorConflict.
  parsedWithErrors <-
    traverse
      ( \((fp, src), (_, hdr)) -> do
          table <- case buildModuleOpTable builtinOps preludeOps opExports hdr of
            Left conflict -> Left (OperatorConflict (AnnP conflict hdr.modLoc hdr.modOrigin))
            Right t -> Right t
          first (ParseError fp) (parseModuleWith table fp src)
      )
      (zip inputs userHeaders)
  let parsed = map fst parsedWithErrors
      validationErrors = concatMap snd parsedWithErrors
  case validationErrors of
    [] -> pure ()
    errs -> Left (ParseValidationErrors errs)
  -- Auto-import prelude into every user module and into every library
  -- module (except prelude itself), then rewrite all LibraryImports to
  -- ModuleImports for the renamer.
  let allMods = rewriteImports (addLibraryPrelude libraryMods ++ map addPreludeImport parsed)
  let exportEnv = buildExportEnv allMods
      exportMap =
        Map.fromList
          [ (Types.UnqualifiedIdentifier n a, toResolution n ms)
          | ((n, a), ms) <- toListExport exportEnv
          ]
      exportedSet =
        Set.fromList
          [Types.QualifiedIdentifier m n a | ((n, a), ms) <- toListExport exportEnv, m <- ms]
      renameInputs =
        RenameInputs
          { riOperatorExports = opExports,
            riTrailingLoc = Map.fromList [(h.modName, h.trailingLoc) | (_, h) <- userHeaders]
          }
  (renamed, renameWarnings) <- first RenameErrors (renameProgram renameInputs allMods)
  resolved <- first ResolveErrors (resolveProgram renamed)
  desugared <- first DesugarErrors (desugarProgram resolved)
  desugared' <- first DesugarErrors (liftAllLambdas desugared)
  let symTab = extractSymbolTable desugared'
      warnings = [RenameWarnings renameWarnings | not (null renameWarnings)]
  prog <- first CompileErrors (compile desugared' symTab)
  -- The query parser uses the union of every user module's operator
  -- visibility, so a query at the REPL can use any operator any user
  -- module declares.
  queryTable <- case mergeOps builtinOps (concat (Map.elems opExports)) of
    Left conflict -> Left (OperatorConflict (noAnnP conflict))
    Right t -> Right t
  let lambdaCount = length [() | f <- desugared'.functions, isLambdaName f.name]
  pure (CompiledProgram prog exportMap exportedSet symTab allMods queryTable desugared'.functions lambdaCount resolved.functionNames desugared, warnings)
  where
    first' f (Left e) = Left (f e)
    first' _ (Right x) = Right x
    toResolution n [m] = UniqueExport (Types.Qualified m n)
    toResolution _ ms = AmbiguousExport ms

-- | Prepend a synthetic @use_module(library(prelude))@ to a user module so
-- the renamer treats prelude exports as visible.
addPreludeImport :: Module -> Module
addPreludeImport m = m {imports = noAnnP (LibraryImport "prelude" Nothing) : m.imports}

compileFiles :: Bool -> [FilePath] -> IO (Either Error (CompiledProgram, [Warning]))
compileFiles includeStdlib paths = do
  contents <- mapM (\fp -> (fp,) <$> TIO.readFile fp) paths
  pure (compileModules includeStdlib contents)

-- | Check if a name is a lambda (generated by lambda lifting).
isLambdaName :: Types.Name -> Bool
isLambdaName (Types.Qualified _ n) = T.isPrefixOf "__lambda_" n
isLambdaName (Types.Unqualified n) = T.isPrefixOf "__lambda_" n
