{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Safe #-}
module Grid.Symantics
  ( Trivial
  -- * Syntax/Semantics
  , Symantics(..)
  , IfThenElse(..)
  -- * Closed terms
  , Closed(..)
  -- Helper functions
  , Wrapped(..)
  ) where

import Control.Applicative
import Control.Comonad
import Control.Monad
import Data.Foldable
import Data.String
import Data.Traversable
import Prelude

class Trivial a
instance Trivial a

class Wrapped t ta | ta -> t where
  wrapped :: (forall a. t a -> r) -> ta -> r
instance Wrapped t (t a) where
  wrapped f a = f a

class IfThenElse b where
  type IfThenElseBranch b :: * -> Constraint
  ifThenElse :: IfThenElseBranch b a => b -> a -> a -> a
  default ifThenElse :: (Symantics t, b ~ t Bool, a ~ t x) => t Bool -> t x -> t x -> t x
  ifThenElse = iff

instance IfThenElse Bool where
  type IfThenElseBranch Bool = Trivial
  ifThenElse True t _  = t
  ifThenElse False _ e = e

infix  4 .==, ./=, .<=, .<, .>, .>=
infixr 3 .&&
infixr 2 .||

-- a lightweight syntax/semantics
class ( Num (t Int)
      , Num (t Float)
      , IsString (t String)
      , IfThenElse (t Bool)
      , IfThenElseBranch (t Bool) ~ Wrapped t
      ) => Symantics t where

  type Lit t :: * -> Constraint
  type Lit t = Trivial
  type Prim t :: * -> *
  type Prim t = t
  type EqT t :: * -> Constraint
  type EqT t = Eq
  type OrdT t :: * -> Constraint
  type OrdT t = Ord

  lit   :: Lit t a => a -> t a
  prim  :: Prim t a -> t a
  iff   :: t Bool -> t a -> t a -> t a
  bool  :: Bool -> t Bool
  not_  :: t Bool -> t Bool
  (.||) :: t Bool -> t Bool -> t Bool
  (.&&) :: t Bool -> t Bool -> t Bool
  (.==) :: EqT t a => t a -> t a -> t Bool
  (./=) :: EqT t a => t a -> t a -> t Bool
  (.<=) :: OrdT t a => t a -> t a -> t Bool
  (.<)  :: OrdT t a => t a -> t a -> t Bool
  (.>)  :: OrdT t a => t a -> t a -> t Bool
  (.>=) :: OrdT t a => t a -> t a -> t Bool
  max_  :: OrdT t a => t a -> t a -> t a
  min_  :: OrdT t a => t a -> t a -> t a
  let_  :: t a -> (t a -> t b) -> t b
  let_ x f = f x

  default not_ :: Functor t => t Bool -> t Bool
  not_ = fmap not
  default bool :: Applicative t => Bool -> t Bool
  bool = pure
  default (.||) :: Applicative t => t Bool -> t Bool -> t Bool
  (.||) = liftA2 (||)
  default (.&&) :: Applicative t => t Bool -> t Bool -> t Bool
  (.&&) = liftA2 (&&)
  default (.==) :: (Applicative t, Eq a) => t a -> t a -> t Bool
  (.==) = liftA2 (==)
  default (./=) :: (Applicative t, Eq a) => t a -> t a -> t Bool
  (./=) = liftA2 (/=)
  default (.<=) :: (Applicative t, Ord a) => t a -> t a -> t Bool
  (.<=) = liftA2 (<=)
  default (.<) :: (Applicative t, Ord a) => t a -> t a -> t Bool
  (.<) = liftA2 (<)
  default (.>) :: (Applicative t, Ord a) => t a -> t a -> t Bool
  (.>) = liftA2 (>)
  default (.>=) :: (Applicative t, Ord a) => t a -> t a -> t Bool
  (.>=) = liftA2 (>=)
  default min_ :: (Applicative t, Ord a) => t a -> t a -> t a
  min_ = liftA2 min
  default max_ :: (Applicative t, Ord a) => t a -> t a -> t a
  max_ = liftA2 max

newtype Closed p a = Closed { runClosed :: forall t. p t => t a }

