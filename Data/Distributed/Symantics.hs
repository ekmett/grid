{-# LANGUAGE
  GADTs,
  Rank2Types,
  TypeFamilies,
  KindSignatures,
  FlexibleInstances,
  ConstraintKinds
  #-}

module Data.Distributed.Symantics
  ( Trivial
  , Symantics(..)
  -- * Closed terms, reusable under different symantics
  , Sym(..)
  ) where

class Trivial a
instance Trivial a

-- a lightweight syntax/semantics
class Symantics t where
  type Lit t :: * -> Constraint
  type Lit t = Trivial
  type Prim t :: * -> *
  type Prim t = t
  app_  :: t (a -> b) -> t a -> t b
  lam_  :: (t a -> t b) -> t (a -> b)
  lit_  :: Lit t a => a -> t a
  iff_  :: t Bool -> t a -> t a -> t a
  bool_ :: Bool -> t Bool
  fix1_ :: (t a -> t a) -> t a
  prim_ :: Prim t a -> t a
  let1_ :: t a -> (t a -> t b) -> t b
  let1_ x f = lam_ f `app_` x

-- a closed term
newtype Sym p t a = Sym { runSym :: forall s. (Symantics s, p ~ Lit s, t ~ Prim s) => s a }
