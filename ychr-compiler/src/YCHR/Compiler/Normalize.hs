{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

module YCHR.Compiler.Normalize
  ( normalizeRule,
  )
where

import Control.Monad.State.Strict
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text.Show
import YCHR.Types.Common
import YCHR.Types.Normalized
import YCHR.Types.Parsed
import YCHR.Types.Renamed

data NmState = NmState
  { varIndex :: Int,
    visitedVars :: Set Variable
  }
  deriving (Eq, Show)

emptyNmState :: NmState
emptyNmState =
  NmState
    { varIndex = 0,
      visitedVars = mempty
    }

normalizeRule :: RnRule -> NormalRule
normalizeRule (Simplification _ h g b) = flip evalState emptyNmState $ do
  (r', rGuard) <- normalizeHead (getHead h)
  pure
    NormalRule
      { head = Head [],
        remove = Remove r',
        guard = Guard (rGuard ++ getGuard g),
        body = b
      }
normalizeRule (Simpagation _ h r g b) = flip evalState emptyNmState $ do
  (h', hGuard) <- normalizeHead (getHead h)
  (r', rGuard) <- normalizeHead (getRemove r)
  pure
    NormalRule
      { head = Head h',
        remove = Remove r',
        guard = Guard (hGuard ++ rGuard ++ getGuard g),
        body = b
      }
normalizeRule (Propagation _ h g b) = flip evalState emptyNmState $ do
  (h', hGuard) <- normalizeHead (getHead h)
  pure
    NormalRule
      { head = Head h',
        remove = Remove [],
        guard = Guard (hGuard ++ getGuard g),
        body = b
      }

normalizeHead :: [NmChrConstraint] -> State NmState ([NmChrConstraint], [NmConstraint])
normalizeHead constrs = do
  results <- traverse normalizeChrConstraint constrs
  let constrs' = map fst results
      args' = concatMap snd results
  pure (constrs', args')

normalizeChrConstraint :: RnChrConstraint -> State NmState (NmChrConstraint, [NmConstraint])
normalizeChrConstraint constr@(ChrConstraint name _) = do
  results <- traverse normalizeArgVar constr.args
  let args' = map fst results
      constrs = concatMap snd results
  pure (ChrConstraint name (map Var args'), constrs)

normalizeArgVar :: PsTerm -> State NmState (Variable, [NmConstraint])
normalizeArgVar (Var var) = do
  visited <- gets visitedVars
  if var `Set.member` visited
    then do
      var' <- freshenVar var
      pure (var', [EqConstr (Var var) (Var var')])
    else do
      modify' (\s -> s {visitedVars = Set.insert var visited})
      pure (var, [])
normalizeArgVar t = do
  var <- freshVar
  pure (var, [EqConstr (Var var) t])

freshVar :: State NmState Variable
freshVar = do
  i <- gets varIndex
  modify' (\s@NmState {varIndex} -> s {varIndex = varIndex + 1})
  pure $ Variable ("$" <> tshow i)

freshenVar :: Variable -> State NmState Variable
freshenVar (Variable var) = do
  Variable var' <- freshVar
  pure $ Variable (var <> var')
