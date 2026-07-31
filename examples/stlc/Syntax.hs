{-# LANGUAGE OverloadedStrings #-}

-- | The object language shared by the parser and the driver. Kept in its
-- own module so "Parser" and "Main" can both import it without a cycle;
-- the 'ToTerm' instance lives here too (with the type it encodes) so it is
-- not an orphan.
module Syntax
  ( Expr (..),
  )
where

import Data.Text (Text)
import YCHR (ToTerm (..), compound)

-- | Unannotated lambda terms. @let x = e1 in e2@ is desugared by the
-- parser to @(\\x. e2) e1@, so it needs no constructor of its own.
data Expr
  = Var Text
  | Lam Text Expr
  | App Expr Expr
  | IntLit Integer
  | Add Expr Expr
  deriving (Eq, Show)

-- | Encode a term as the CHR data the inferencer matches on. These are
-- plain compounds (@var@, @lam@, …), which the driver passes in quoted
-- with @quote/1@ so they are treated as data rather than evaluated.
instance ToTerm Expr where
  toTerm (Var x) = compound "var" [toTerm x]
  toTerm (Lam x body) = compound "lam" [toTerm x, toTerm body]
  toTerm (App f a) = compound "app" [toTerm f, toTerm a]
  toTerm (IntLit n) = compound "lit_int" [toTerm n]
  toTerm (Add a b) = compound "add" [toTerm a, toTerm b]
