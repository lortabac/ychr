{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

-- | The CHR session: a running interpreter state for a compiled
-- program (constraint store, propagation history, reactivation queue,
-- unification variables, call stack), packaged as an 'Effectful'
-- effect.
--
-- Lives in its own module so the type-checker can open a CHR session
-- without depending on "YCHR.Run" (which would otherwise form a cycle
-- once "YCHR.Run" calls into the type-checker for goal-time checks).
module YCHR.Runtime.Session
  ( -- * The CHR effect
    CHR,
    CHREffects,
    StaticRep (CHRRep),
    ProcMap,

    -- * Session input
    SessionInput (..),
    toSessionInput,

    -- * Session setup
    runCHR,
    withCHR,
    withCHRExtra,

    -- * Telling constraints
    tellConstraint,
  )
where

import Control.Monad (unless)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text qualified as T
import Effectful
import Effectful.Dispatch.Static
import Effectful.State.Static.Local (State, evalState)
import Effectful.Writer.Static.Local (Writer, runWriter)
import Language.Haskell.TH.Syntax (Lift)
import YCHR.Compile (tellProcName)
import YCHR.Compile.Pipeline (CompiledProgram (..), ExportResolution (..))
import YCHR.Runtime.Error (CallStack, runtimeErrorS)
import YCHR.Runtime.History (PropHistory, runPropHistory)
import YCHR.Runtime.Interpreter (HostCallRegistry, callProc)
import YCHR.Runtime.Reactivation (ReactQueue, runReactQueue)
import YCHR.Runtime.Store (CHRStore, runCHRStore)
import YCHR.Runtime.Types (CallVal (..), SuspensionId, Value (..))
import YCHR.Runtime.Var (Unify, runUnify)
import YCHR.Types qualified as Types
import YCHR.VM (Name (..), Procedure (..), Program (..))

type ProcMap = Map Name Procedure

-- | The narrow slice of a compiled program that 'runCHR' / 'withCHR'
-- need: the VM 'Program' and the export-resolution maps used by
-- 'tellConstraint' to canonicalize unqualified constraint names. A
-- 'CompiledProgram' projects to one via 'toSessionInput'; the
-- pre-compiled type-checker bundle is a 'SessionInput' directly.
data SessionInput = SessionInput
  { program :: Program,
    exportMap :: Map Types.UnqualifiedIdentifier ExportResolution,
    exportedSet :: Set Types.QualifiedIdentifier
  }
  deriving (Lift)

-- | Project a 'CompiledProgram' down to the slice 'runCHR' / 'withCHR'
-- actually read.
toSessionInput :: CompiledProgram -> SessionInput
toSessionInput cp =
  SessionInput
    { program = cp.program,
      exportMap = cp.exportMap,
      exportedSet = cp.exportedSet
    }

data CHR :: Effect

type instance DispatchOf CHR = Static WithSideEffects

data instance StaticRep CHR
  = CHRRep
      ProcMap
      HostCallRegistry
      (Map Types.UnqualifiedIdentifier ExportResolution)
      ( Set
          Types.QualifiedIdentifier
      )

-- | Shorthand for the full set of effects available inside a CHR session.
type CHREffects es =
  ( CHR :> es,
    Unify :> es,
    CHRStore :> es,
    PropHistory :> es,
    ReactQueue :> es,
    Writer [SuspensionId] :> es,
    State CallStack :> es,
    IOE :> es
  )

-- | Set up a CHR session for a compiled program. All runtime state (constraint
-- store, propagation history, reactivation queue, unification variables) is
-- initialised and persists for the duration of the computation.
runCHR ::
  (IOE :> es) =>
  SessionInput ->
  HostCallRegistry ->
  Eff
    ( CHR
        : State CallStack
        : Writer [SuspensionId]
        : ReactQueue
        : PropHistory
        : CHRStore
        : Unify
        : es
    )
    a ->
  Eff es a
runCHR si hc =
  runUnify
    . runCHRStore si.program.typeNames
    . runPropHistory
    . runReactQueue
    . fmap fst
    . runWriter @[SuspensionId]
    . evalState @CallStack []
    . evalStaticRep (CHRRep procMap hc si.exportMap si.exportedSet)
  where
    procMap =
      Map.fromList
        [(pname, p) | p@Procedure {name = pname} <- si.program.procedures]

-- | Convenience wrapper that runs a CHR session in 'IO'.
withCHR ::
  SessionInput ->
  HostCallRegistry ->
  (forall es. (CHREffects es) => Eff es a) ->
  IO a
withCHR si hc action = runEff (runCHR si hc action)

-- | Like 'withCHR' but merges extra procedures (e.g. query-time lambda
-- compilations and updated call dispatches) into the ProcMap.
withCHRExtra ::
  SessionInput ->
  HostCallRegistry ->
  [Procedure] ->
  (forall es. (CHREffects es) => Eff es a) ->
  IO a
withCHRExtra si hc extraProcs action =
  runEff
    . runUnify
    . runCHRStore si.program.typeNames
    . runPropHistory
    . runReactQueue
    . fmap fst
    . runWriter @[SuspensionId]
    . evalState @CallStack []
    . evalStaticRep (CHRRep procMap hc si.exportMap si.exportedSet)
    $ action
  where
    baseProcMap =
      Map.fromList
        [ ( pname,
            p
          )
        | p@Procedure {name = pname} <- si.program.procedures
        ]
    extraProcMap = Map.fromList [(pname, p) | p@Procedure {name = pname} <- extraProcs]
    procMap = extraProcMap `Map.union` baseProcMap

-- | Add a constraint to the store. The constraint name can be unqualified
-- (resolved via the export map) or fully qualified.
tellConstraint :: (CHREffects es) => Types.Name -> [Value] -> Eff es ()
tellConstraint name args = do
  CHRRep procMap hc exportMap exportedSet <- getStaticRep
  let arity = length args
  resolved <- case resolveByExport exportMap exportedSet name arity of
    Left err -> runtimeErrorS err
    Right qname -> pure qname
  let tellName = tellProcName resolved arity
  unless (Map.member tellName procMap) $
    runtimeErrorS ("Constraint not found: " ++ T.unpack tellName.unName)
  _ <- callProc procMap hc tellName (map CVal args)
  pure ()

-- | Name resolution against the export map and qualified-name set. Used by
-- 'tellConstraint' to canonicalize an unqualified constraint name to its
-- module-qualified form so the proc-map lookup matches.
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
