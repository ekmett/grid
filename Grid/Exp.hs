{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
module Grid.Exp
  ( Exp(..)
  , Fun
  , fun
  ) where

import Control.Applicative
import Control.Comonad
import Control.Monad
import Data.Foldable
import Data.String
import Data.Traversable
import Grid.Symantics
import Prelude

-- | A trivial semantics transformer, used to avoid overlapping instances in Fun
newtype Exp t a = Exp { runExp :: t a } deriving
  ( Eq
  , Ord
  , Functor
  , Applicative
  , Alternative
  , Monad
  , MonadPlus
  , Extend
  , Comonad
  , Foldable
  , Traversable
  )

instance Show (t a) => Show (Exp t a) where
  showsPrec d (Exp as) = showParen (d > 10) $ showString "Exp " . showsPrec 11 as

instance Symantics t => Symantics (Exp t) where
  type Lit (Exp t) = Lit t
  type Prim (Exp t) = Prim t
  type EqT (Exp t) = EqT t
  type OrdT (Exp t) = OrdT t
  not_ (Exp a) = Exp (not_ a)
  iff (Exp b) (Exp t) (Exp e) = Exp (iff b t e)
  bool a = Exp (bool a)
  Exp a .<  Exp b = Exp (a .<  b)
  Exp a .<= Exp b = Exp (a .<= b)
  Exp a .== Exp b = Exp (a .== b)
  Exp a ./= Exp b = Exp (a ./= b)
  Exp a .>= Exp b = Exp (a .>= b)
  Exp a .>  Exp b = Exp (a .>  b)
  Exp a .&& Exp b = Exp (a .&& b)
  Exp a .|| Exp b = Exp (a .|| b)
  lit a = Exp (lit a)
  let_ (Exp x) f = Exp (let_ x (runExp . f . Exp))
  prim a = Exp (prim a)

class Symantics t => FunSymantics t where
  app_  :: t (a -> b) -> t a -> t b
  lam_  :: (t a -> t b) -> t (a -> b)
  fix1_ :: (t a -> t a) -> t a

app :: FunSymantics t => Exp t (a -> b) -> Exp t a -> Exp t b
Exp f `app` Exp x = Exp (app_ f x)
{-# INLINE app #-}

lam :: FunSymantics t => (Exp t a -> Exp t b) -> Exp t (a -> b)
lam f = Exp $ lam_ $ runExp . f . Exp
{-# INLINE lam #-}

fun :: Fun f => f -> f
fun = korma . recur . unkorma
{-# INLINE fun #-}

fix1 :: Symantics t => (Exp t a -> Exp t a) -> Exp t a
fix1 f = Exp $ fix1_ $ runExp . f . Exp
{-# INLINE fix1 #-}

-- Plumbing used to implement fun

data TList :: (* -> *) -> * -> * where
  Cons :: Exp t a -> TList t as -> TList t (a, as)
  Nil  :: TList t ()

class FunSymantics (CurS as r) => Cur as r where
  type CurF as r
  type CurS as r :: * -> *
  uncur :: Exp (CurS as r) (CurF as r) -> TList (CurS as r) as -> r
  cur :: (TList (CurS as r) as -> r) -> Exp (CurS as r) (CurF as r)
  recur :: (TList (CurS as r) as -> r) -> TList (CurS as r) as -> r
  recur = uncur . cur

instance FunSymantics t => Cur () (Exp t a) where
  type CurF () (Exp t a) = a
  type CurS () (Exp t a) = t
  uncur f Nil = f
  cur f = f Nil

instance Cur as r => Cur (a,as) r where
  type CurF (a,as) r = a -> CurF as r
  type CurS (a,as) r = CurS as r
  uncur f (Cons a as) = uncur (app f a) as
  cur f = lam (\x -> cur (f . Cons x))

class (Cur (FunL rs) (FunR rs), CurS (FunL rs) (FunR rs) ~ FunS rs) => Fun rs where
  type FunS rs :: * -> *
  type FunL rs
  type FunR rs
  korma :: (TList (FunS rs) (FunL rs) -> FunR rs) -> rs
  unkorma :: rs -> TList (FunS rs) (FunL rs) -> FunR rs

instance FunSymantics t => Fun (Exp t a) where
  type FunS (Exp t a) = t
  type FunL (Exp t a) = ()
  type FunR (Exp t a) = Exp t a
  korma f = f Nil
  unkorma r _ = r

instance (Fun rs, FunS rs ~ t) => Fun (Exp t a -> rs) where
  type FunS (Exp t a -> rs) = t
  type FunL (Exp t a -> rs) = (a, FunL rs)
  type FunR (Exp t a -> rs) = FunR rs
  korma f x = korma (f . Cons x)
  unkorma f (Cons a as) = unkorma (f a) as
  unkorma _ _ = error "unkorma: Nil"

-- default (Int, Float, Exp Local Bool, Exp Local Int, Exp Local Float)
