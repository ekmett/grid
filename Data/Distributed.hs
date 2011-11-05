{-# LANGUAGE
  GADTs,
  TypeFamilies,
  DeriveFunctor,
  TypeOperators,
  KindSignatures,
  ConstraintKinds,
  FlexibleContexts,
  FlexibleInstances,
  UndecidableInstances,
  OverlappingInstances,
  FunctionalDependencies,
  GeneralizedNewtypeDeriving
  #-}

module Data.Distributed
  ( Trivial(..)
  , Sym(..)
  , T(..)
  , Id(..)
  , Fun, fun
  , Exp(..)
  , E(..)
  ) where

import Control.Comonad

class Trivial a
instance Trivial a

-- a very simple syntax/semantics
class Sym t where
  type Lit t :: * -> Constraint
  type Lit t = Trivial
  app  :: t (a -> b) -> t a -> t b
  lam  :: (t a -> t b) -> t (a -> b)
  lit  :: Lit t a => a -> t a
  let1 :: t a -> (t a -> t b) -> t b
  let1 x f = lam f `app` x

-- a trivial symantics transformer, used for type pattern matching in Fun
newtype T t a = T { runT :: t a }
  deriving (Eq,Ord,Show,Functor)

instance Extend t => Extend (T t) where
  extend f (T t) = T (extend (f . T) t)

instance Comonad t => Comonad (T t) where
  extract (T t) = extract t

instance Sym t => Sym (T t) where
  type Lit (T t) = Lit t
  T f `app` T x = T (f `app` x)
  lam f = T $ lam $ runT . f . T
  lit a = T (lit a)
  let1 (T x) f = T $ let1 x $ runT . f . T

-- local evaluation symantics
newtype Id a = Id { runId :: a }
  deriving (Eq,Ord,Enum,Show,Functor,Num,Real,Floating,Fractional,Integral,RealFrac,RealFloat)

instance Sym Id where
  Id f `app` Id x = Id (f x)
  lam f = Id (runId . f . Id)
  lit = Id
  let1 x f = f x

data TList :: (* -> *) -> * -> * where
  Cons :: T t a -> TList t as -> TList t (a, as)
  Nil  :: TList t ()

class Sym t => Cur t as r | as r -> t where
  type CurF as r
  uncur :: T t (CurF as r) -> TList t as -> r
  cur :: (TList t as -> r) -> T t (CurF as r)

instance Sym t => Cur t () (T t a) where
  type CurF () (T t a) = a
  uncur f Nil = f
  cur f = f Nil

instance Cur t as r => Cur t (a,as) r where
  type CurF (a,as) r = a -> CurF as r
  uncur f (Cons a as) = uncur (app f a) as
  cur f = lam (\x -> cur (f . Cons x))

recur :: Cur t as r => (TList t as -> r) -> TList t as -> r
recur = uncur . cur

class Cur t (FunL rs) (FunR rs) => Fun t rs | rs -> t where
  type FunL rs
  type FunR rs

  korma :: (TList t (FunL rs) -> FunR rs) -> rs
  unkorma :: rs -> TList t (FunL rs) -> FunR rs

instance Sym t => Fun t (T t a) where
  type FunL (T t a) = ()
  type FunR (T t a) = T t a
  korma f = f Nil
  unkorma r _ = r

instance Fun t rs => Fun t (T t a -> rs) where
  type FunL (T t a -> rs) = (a, FunL rs)
  type FunR (T t a -> rs) = FunR rs
  korma f x = korma (f . Cons x)
  unkorma f (Cons a as) = unkorma (f a) as

fun :: Fun t rs => rs -> rs
fun = korma . recur . unkorma

data E p where
  Var :: {-# UNPACK #-} !Int -> E p
  App :: E p -> E p -> E p
  Lam :: (E p -> E p) -> E p
  Let :: E p -> (E p -> E p) -> E p
  Lit :: p a => a -> E p

instance Show (E p) where
  showsPrec d (Var i) = showParen (d > 10) $ showString "Var ..."
  showsPrec d (App x y) = showParen (d > 10) $
    showString "App " . showsPrec 11 x . showChar ' ' . showsPrec 11 y
  showsPrec d (Lam f) = showParen (d >= 0) $
    showString "Lam $ \\ ... -> " . showsPrec (-1) (f (Var 0))
  showsPrec d (Lit _) = showParen (d > 10) $ showString "Lit ..."

newtype Exp p a = Exp { runExp :: E p }
  deriving Show

instance Sym (Exp p) where
  type Lit (Exp p) = p
  Exp f `app` Exp x = Exp (App f x)
  lam f = Exp $ Lam $ runExp . f . Exp
  lit a = Exp $ Lit a
  let1 (Exp x) f = Exp $ Let x $ runExp . f . Exp
