{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

-- | The CHR session: a running interpreter state for a compiled
-- program (constraint store, propagation history, reactivation queue,
-- unification variables, call stack), packaged as the 'Chr' monad.
--
-- Lives in its own module so the type-checker can open a CHR session
-- without depending on "YCHR.Run" (which would otherwise form a cycle
-- once "YCHR.Run" calls into the type-checker for goal-time checks).
module YCHR.Runtime.Session
  ( -- * The CHR monad (re-exported)
    Chr,
    SessionEnv (..),
    initSessionEnv,
    runChr,

    -- * Session input
    SessionInput (..),
    toSessionInput,

    -- * Session setup
    withCHR,
    withCHRExtra,

    -- * Telling constraints
    tellConstraint,
  )
where

import Control.Monad (unless)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask)
import Data.IORef (readIORef)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text qualified as T
import Language.Haskell.TH.Syntax (Lift)
import YCHR.Compile (tellProcName)
import YCHR.Compile.Pipeline (CompiledProgram (..), ExportResolution (..))
import YCHR.Runtime.Error (runtimeErrorS)
import YCHR.Runtime.Interpreter (HostCallRegistry, callProc)
import YCHR.Runtime.Monad
  ( Chr,
    SessionEnv (..),
    initSessionEnv,
    runChr,
  )
import YCHR.Runtime.Types (CallVal (..), Value (..))
import YCHR.Types qualified as Types
import YCHR.VM (Name (..), Procedure (..), Program (..))

-- | The narrow slice of a compiled program that 'withCHR' /
-- 'withCHRExtra' need: the VM 'Program' and the export-resolution maps
-- used by 'tellConstraint' to canonicalize unqualified constraint
-- names. A 'CompiledProgram' projects to one via 'toSessionInput'; the
-- pre-compiled type-checker bundle is a 'SessionInput' directly.
data SessionInput = SessionInput
  { program :: Program,
    exportMap :: Map Types.UnqualifiedIdentifier ExportResolution,
    exportedSet :: Set Types.QualifiedIdentifier
  }
  deriving (Lift)

-- | Project a 'CompiledProgram' down to the slice 'withCHR' /
-- 'withCHRExtra' actually read.
toSessionInput :: CompiledProgram -> SessionInput
toSessionInput cp =
  SessionInput
    { program = cp.program,
      exportMap = cp.exportMap,
      exportedSet = cp.exportedSet
    }

-- | Run a CHR action in a fresh session for a compiled program. All
-- runtime state (constraint store, propagation history, reactivation
-- queue, unification variables, call stack) is initialised and
-- persists for the duration of the computation.
withCHR :: SessionInput -> HostCallRegistry -> Chr a -> IO a
withCHR si hc action = withCHRExtra si hc [] action

-- | Like 'withCHR' but merges extra procedures (e.g. query-time lambda
-- compilations and updated call dispatches) into the procedure map
-- visible to the action.
withCHRExtra ::
  SessionInput ->
  HostCallRegistry ->
  [Procedure] ->
  Chr a ->
  IO a
withCHRExtra si hc extraProcs action = do
  let baseProcMap =
        Map.fromList [(p.name, p) | p <- si.program.procedures]
      extraProcMap = Map.fromList [(p.name, p) | p <- extraProcs]
      procMap = extraProcMap `Map.union` baseProcMap
  env <- initSessionEnv si.program.typeNames procMap hc si.exportMap si.exportedSet
  runChr action env

-- | Add a constraint to the store. The constraint name can be
-- unqualified (resolved via the session's export map) or fully
-- qualified.
tellConstraint :: Types.Name -> [Value] -> Chr ()
tellConstraint name args = do
  SessionEnv {procMap, exportMap, exportedSet} <- ask
  let arity = length args
  resolved <- case resolveByExport exportMap exportedSet name arity of
    Left err -> runtimeErrorS err
    Right qname -> pure qname
  let tellName = tellProcName resolved arity
  pm <- liftIO (readIORef procMap)
  unless (Map.member tellName pm) $
    runtimeErrorS ("Constraint not found: " ++ T.unpack tellName.unName)
  _ <- callProc tellName (map CVal args)
  pure ()

-- | Name resolution against the export map and qualified-name set.
-- Used by 'tellConstraint' to canonicalize an unqualified constraint
-- name to its module-qualified form so the proc-map lookup matches.
resolveByExport ::
  Map Types.UnqualifiedIdentifier ExportResolution ->
  Set Types.QualifiedIdentifier ->
  Types.Name ->
  Int ->
  Either String Types.Name
resolveByExport expMap expSet name arity = case name of
  Types.Unqualified n ->
    case Map.lookup (Types.UnqualifiedIdentifier n arity) expMap of
      Just (UniqueExport qname) -> Right qname
      Just (AmbiguousExport ms) ->
        Left
          ( "Ambiguous constraint: "
              ++ T.unpack n
              ++ "/"
              ++ show arity
              ++ ", exported by: "
              ++ intercalate ", " (map T.unpack ms)
          )
      Nothing -> Left ("Unknown constraint: " ++ T.unpack n ++ "/" ++ show arity)
  Types.Qualified m n ->
    if Set.member (Types.QualifiedIdentifier m n arity) expSet
      then Right name
      else
        Left
          ( "Constraint not exported: "
              ++ T.unpack m
              ++ ":"
              ++ T.unpack n
              ++ "/"
              ++ show arity
          )
