{-# LANGUAGE
  GADTs,
  Rank2Types,
  TypeFamilies,
  KindSignatures,
  DefaultSignatures,
  ScopedTypeVariables,
  FlexibleInstances,
  FlexibleContexts,
  RebindableSyntax,
  ConstraintKinds,
  FunctionalDependencies,
  UndecidableInstances
  #-}

module Data.Distributed.Symantics
  ( Proxy(..)
  , IfThenElse(..)
  , IsEq(..)
  , Trivial
  , Symantics(..)
  -- * Closed terms, reusable under different symantics
  -- , Sym(..)
  -- Helper functions
  , Wrapped(..)
  ) where

-- import Data.Distributed.Boolean
import Data.String
import Prelude hiding ((==),(/=))
import qualified Prelude

data Proxy (p :: * -> Constraint) = Proxy

class Trivial a
instance Trivial a

class Wrapped p t ta | ta -> t where
  wrapped       :: Proxy p -> (forall a. p a => t a -> r) -> ta -> r
  wrappedBinary :: Proxy p -> (forall a. p a => t a -> t a -> t a) -> ta -> ta -> ta
  wrappedEq     :: Proxy p -> (forall a. p a => t a -> t a -> r) -> ta -> ta -> r

instance p a => Wrapped p t (t a) where
  wrapped       _ f a   = f a
  wrappedBinary _ f a b = f a b
  wrappedEq     _ f a b = f a b

class IfThenElse b where
  type IfThenElseBranch b :: * -> Constraint
  ifThenElse :: IfThenElseBranch b a => b -> a -> a -> a
  default ifThenElse :: (b ~ t Bool, Symantics t, a ~ t x) => t Bool -> t x -> t x -> t x
  -- default ifThenElse :: (b ~ t Bool, Symantics t, Wrapped Trivial t a) => t Bool -> a -> a -> a
  ifThenElse b t e = wrappedBinary (Proxy :: Proxy Trivial) (iff_ b) t e

-- subobject classifier
class IsEq b where
  type IsEqBranch b :: * -> Constraint
  (==) :: IsEqBranch b a => a -> a -> b
  default (==) :: (b ~ t Bool, Symantics t, a ~ t x, EqT t x) => t x -> t x -> t Bool
  -- default (==) :: (b ~ t Bool, Symantics t, Wrapped (EqT t) t a) => a -> a -> t Bool
  (==) = eq_

  (/=) :: IsEqBranch b a => a -> a -> b
  default (/=) :: (b ~ t Bool, Symantics t, a ~ t x, EqT t x) => t x -> t x -> t Bool
  (/=) = neq_

eqDefault :: forall (t :: * -> *) a. (IsEq (t Bool), Symantics t, Wrapped (EqT t) t a) => a -> a -> t Bool
eqDefault a b = wrappedEq (Proxy :: Proxy (EqT t)) eq_ a b

neqDefault :: forall (t :: * -> *) a. (IsEq (t Bool), Symantics t, Wrapped (EqT t) t a) => a -> a -> t Bool
neqDefault a b = wrappedEq (Proxy :: Proxy (EqT t)) neq_ a b

-- eqDefault :: (IsEq (t Bool), Symantics t, Wrapped (EqT t

instance IsEq Bool where
  type IsEqBranch Bool = Eq
  (==) = (Prelude.==)
  (/=) = (Prelude./=)

instance IfThenElse Bool where
  type IfThenElseBranch Bool = Trivial
  ifThenElse True t _  = t
  ifThenElse False _ e = e

-- a lightweight syntax/semantics
class ( Num (t Int)
      , Num (t Float)
      -- , Boolean (t Bool)
      , IsString (t String)
      , IfThenElse (t Bool)
      , IfThenElseBranch (t Bool) ~ Wrapped (EqT t) t
      , IsEq (t Bool)
      , IsEqBranch (t Bool) ~ EqT t
      ) => Symantics t where
  type Lit t :: * -> Constraint
  type Lit t = Trivial
  type Prim t :: * -> *
  type Prim t = t
  type EqT t :: * -> Constraint
  type EqT t = Eq
  app_  :: t (a -> b) -> t a -> t b
  lam_  :: (t a -> t b) -> t (a -> b)
  lit_  :: Lit t a => a -> t a
  iff_  :: t Bool -> t a -> t a -> t a
  fix1_ :: (t a -> t a) -> t a
  prim_ :: Prim t a -> t a
  eq_   :: EqT t a => t a -> t a -> t Bool
  neq_  :: EqT t a => t a -> t a -> t Bool
  let1_ :: t a -> (t a -> t b) -> t b
  let1_ x f = lam_ f `app_` x

newtype Closed p a = Closed { runClosed :: forall t. p t => t a }
