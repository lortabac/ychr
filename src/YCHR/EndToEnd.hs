{-# LANGUAGE DataKinds #-}

module YCHR.EndToEnd
  ( Error (..),
    compileModules,
    compileFiles,
    runQueryDSL,
    runQuery,
  )
where

import Data.Bifunctor (first)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text.IO qualified as TIO
import Data.Void (Void)
import Effectful
import Effectful.State.Static.Local (State, evalState, get, modify)
import Effectful.Writer.Static.Local (runWriter)
import Text.Megaparsec (ParseErrorBundle)
import YCHR.Compile (CompileError, compile, procNameFor)
import YCHR.Desugar (DesugarError, desugarProgram, extractSymbolTable)
import YCHR.Parser (parseConstraint, parseModule)
import YCHR.Rename (RenameError, renameProgram)
import YCHR.Runtime.History (runPropHistory)
import YCHR.Runtime.Interpreter (HostCallRegistry, callProc)
import YCHR.Runtime.Reactivation (runReactQueue)
import YCHR.Runtime.Store (runCHRStore)
import YCHR.Runtime.Types (RuntimeVal (..), SuspensionId, Value (..))
import YCHR.Runtime.Var (Unify, deref, newVar, runUnify)
import YCHR.Types (Constraint (..), Term (..))
import YCHR.Types qualified as T
import YCHR.VM (Program (..), procName)

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

-- | Run a single CHR constraint against a compiled program.
--
-- Creates fresh logical variables for each distinct 'VarTerm' name in the
-- constraint's argument list, calls the corresponding @tell_*@ procedure,
-- and returns the procedure's result along with a map from every input
-- variable name to its fully-dereferenced value.  Unbound variables in the
-- result are represented as @VarTerm <original-name>@; unbound variables
-- that appear nested inside compound terms are represented as @VarTerm "_"@.
runQueryDSL :: Program -> HostCallRegistry -> Constraint -> IO (RuntimeVal, Map String Term)
runQueryDSL Program {progNumTypes, progProcedures} hostCalls (Constraint name args) = do
  let procMap = Map.fromList [(procName p, p) | p <- progProcedures]
      tellName = procNameFor "tell" name
  runEff
    . runUnify
    . fmap fst
    . runWriter @[SuspensionId]
    . runCHRStore progNumTypes
    . runPropHistory
    . runReactQueue
    . evalState (Map.empty :: Map String Value)
    $ do
      argVals <- traverse termToValue args
      result <- callProc procMap hostCalls tellName (map RVal argVals)
      varMap <- get
      bindings <- Map.traverseWithKey valueToTerm varMap
      pure (result, bindings)

-- | Like 'runQueryDSL' but accepts a query as surface-language 'Text'.
--
-- The text is parsed as a single constraint (e.g. @"leq(X, Y)"@).
-- A parse failure is raised as an 'IOError' via 'fail'.
runQuery :: Program -> HostCallRegistry -> Text -> IO (RuntimeVal, Map String Term)
runQuery prog hostCalls src =
  case parseConstraint "<query>" src of
    Left err -> fail (show err)
    Right c -> runQueryDSL prog hostCalls c

-- | Convert a 'Term' to a runtime 'Value', allocating fresh logical
-- variables for 'VarTerm' names.  The same name always maps to the same
-- variable (sharing enforced via 'State').
termToValue :: (Unify :> es, State (Map String Value) :> es) => Term -> Eff es Value
termToValue (VarTerm n) = do
  varMap <- get
  case Map.lookup n varMap of
    Just v -> pure v
    Nothing -> do
      v <- newVar
      modify (Map.insert n v)
      pure v
termToValue (IntTerm n) = pure (VInt n)
termToValue (AtomTerm s) = pure (VAtom s)
termToValue Wildcard = pure VWildcard
termToValue (CompoundTerm (T.Unqualified f) ts) = VTerm f <$> traverse termToValue ts
termToValue (CompoundTerm (T.Qualified m f) ts) = VTerm (m ++ ":" ++ f) <$> traverse termToValue ts

-- | Convert a runtime 'Value' back to a 'Term' after dereferencing.
-- @varName@ is used as the name for a still-unbound variable (pass @"_"@
-- for anonymous nested variables).
valueToTerm :: (Unify :> es) => String -> Value -> Eff es Term
valueToTerm varName v = do
  v' <- deref v
  case v' of
    VInt n -> pure (IntTerm n)
    VAtom s -> pure (AtomTerm s)
    VBool True -> pure (AtomTerm "true")
    VBool False -> pure (AtomTerm "false")
    VWildcard -> pure Wildcard
    VTerm f ts -> CompoundTerm (T.Unqualified f) <$> traverse (valueToTerm "_") ts
    VVar _ -> pure (VarTerm varName)
