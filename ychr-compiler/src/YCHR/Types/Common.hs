{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module YCHR.Types.Common where

import Data.Data (Data)
import Data.List.NonEmpty (NonEmpty)
import Data.String (IsString)
import Data.Text (Text)

-- | A YCHR module
data Module var name = Module
  { moduleName :: Text,
    imports :: [Import],
    constraints :: [ConstraintDef],
    rules :: [Rule var name]
  }
  deriving (Eq, Show, Data, Functor, Foldable, Traversable)

-- | Imported module with explicit list of identifiers
data Import = Import
  { importedModule :: ModuleName,
    identifiers :: [Text]
  }
  deriving (Eq, Show, Data)

-- | Constraint definition (functor/arity)
data ConstraintDef = ConstraintDef
  { functor :: Text
  }
  deriving (Eq, Show, Data)

newtype ModuleName = ModuleName {getModuleName :: Text}
  deriving stock (Eq, Show, Data)
  deriving newtype (IsString)

newtype RuleName = RuleName {getRuleName :: Text}
  deriving stock (Eq, Show, Data)
  deriving newtype (IsString)

data Rule var name
  = Simplification (Maybe RuleName) (Head var name) (Guard var name) (Body var name)
  | Propagation (Maybe RuleName) (Head var name) (Guard var name) (Body var name)
  | Simpagation (Maybe RuleName) (Head var name) (Remove var name) (Guard var name) (Body var name)
  deriving (Eq, Show, Data, Functor, Foldable, Traversable)

data Term var
  = Var var
  | Int Integer
  | String Text
  deriving (Eq, Show, Ord, Data, Functor, Foldable, Traversable)

-- | Qualified name (module name and identifier)
data QualifiedName = QualifiedName Text Text
  deriving (Eq, Show, Ord, Data)

-- | Textual variable
newtype Variable = Variable {getVariable :: Text}
  deriving stock (Eq, Show, Ord, Data)
  deriving newtype (IsString)

-- | CHR constraint
data ChrConstraint var name = ChrConstraint
  { name :: name,
    arguments :: [Term var]
  }
  deriving (Eq, Show, Ord, Data, Functor, Foldable, Traversable)

-- | Constraint in the host language
data HostConstraint var = HostConstraint
  { name :: Text,
    arguments :: [Term var]
  }
  deriving (Eq, Show, Data)

-- | Any constraint
data Constraint var name
  = ChrConstr (ChrConstraint var name)
  | EqConstr (Term var) (Term var)
  | TrueConstr
  | FalseConstr
  | OpConstr (Operator var)
  | HostConstr (HostConstraint var)
  deriving (Eq, Show, Data, Functor, Foldable, Traversable)

newtype Head var name = Head {getHead :: [ChrConstraint var name]}
  deriving (Eq, Show, Data, Functor, Foldable, Traversable)

newtype Remove var name = Remove {getRemove :: [ChrConstraint var name]}
  deriving (Eq, Show, Data, Functor, Foldable, Traversable)

newtype Guard var name = Guard {getGuard :: [Constraint var name]}
  deriving (Eq, Show, Data, Functor, Foldable, Traversable)

emptyGuard :: Guard var name
emptyGuard = Guard []

newtype Body var name = Body {getConstraint :: NonEmpty (Constraint var name)}
  deriving (Eq, Show, Data, Functor, Foldable, Traversable)

data Operator var
  = Plus (Term var) (Term var)
  | Minus (Term var) (Term var)
  deriving (Eq, Show, Data)
