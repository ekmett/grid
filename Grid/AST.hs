{-# LANGUAGE
  GADTs,
  TypeFamilies,
  ConstraintKinds
  #-}

module Grid.AST
  ( AST(..)
  ) where

import Grid.Symantics

data AST p t a where
  Var  :: {-# UNPACK #-} !Int -> AST p t a
  App  :: AST p t (a -> b) -> AST p t a -> AST p t b
  Lam  :: (AST p t a -> AST p t b) -> AST p t (a -> b)
  Lit  :: p a => a -> AST p t a
  Prim :: t a -> AST p t a
  Iff  :: AST p t Bool -> AST p t a -> AST p t a -> AST p t a
  Let  :: AST p t a -> (AST p t a -> AST p t b) -> AST p t b
  Fix  :: (AST p t a -> AST p t a) -> AST p t a
  Bool :: Bool -> AST p t Bool

instance Symantics (AST p t) where
  type Lit (AST p t) = p
  type Prim (AST p t) = t
  app_  = App
  lam_  = Lam
  lit_  = Lit
  let1_ = Let
  fix1_ = Fix
  iff_  = Iff
  bool_ = Bool
  prim_ = Prim
