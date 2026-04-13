-- | Source location types shared across all AST representations.
module YCHR.Loc
  ( SourceLoc (..),
    Ann (..),
    noAnn,
    dummyLoc,
  )
where

import Language.Haskell.TH.Syntax (Lift)

-- | A source file location (file, line, column).
data SourceLoc = SourceLoc
  { file :: String,
    line :: Int,
    col :: Int
  }
  deriving (Show, Eq, Lift)

-- | A value annotated with a source location.
data Ann a = Ann
  { node :: a,
    sourceLoc :: SourceLoc
  }
  deriving (Show, Eq, Lift, Functor, Foldable, Traversable)

-- | A dummy source location for programmatically-constructed nodes.
dummyLoc :: SourceLoc
dummyLoc = SourceLoc "<generated>" 1 1

-- | Wrap a value with a dummy source location.
noAnn :: a -> Ann a
noAnn x = Ann x dummyLoc
