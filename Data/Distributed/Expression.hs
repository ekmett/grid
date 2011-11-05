{-# LANGUAGE
  GADTs,
  Rank2Types,
  TypeFamilies,
  TypeOperators,
  KindSignatures,
  ConstraintKinds,
  FlexibleContexts,
  FlexibleInstances,
  FunctionalDependencies,
  GeneralizedNewtypeDeriving
  #-}

module Data.Distributed.Expression
  (
  -- * DSL
    Exp(..)
  , Fun
  , fun
  , lit
  , iff
  , bool
  , fix1
  , let1
  , lam
  , app
  ) where

import Control.Applicative
import Control.Comonad
import Control.Monad
import Data.Foldable
import Data.Traversable
import Data.Distributed.Symantics

-- | A trivial semantics transformer, used to avoid overlapping instances in Fun

newtype Exp t a = Exp { runExp :: t a }
  deriving
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
  app_ = app
  lam_ = lam
  lit_ = lit
  iff_ = iff
  fix1_ = fix1
  let1_ = let1
  prim_ = prim
  bool_ = bool

app :: Symantics t => Exp t (a -> b) -> Exp t a -> Exp t b
Exp f `app` Exp x = Exp (app_ f x)
{-# INLINE app #-}

lam :: Symantics t => (Exp t a -> Exp t b) -> Exp t (a -> b)
lam f = Exp $ lam_ $ runExp . f . Exp
{-# INLINE lam #-}

lit :: (Symantics t, Lit t a) => a -> Exp t a
lit a = Exp (lit_ a)
{-# INLINE lit #-}

iff :: Symantics t => Exp t Bool -> Exp t a -> Exp t a -> Exp t a
iff (Exp b) (Exp t) (Exp e) = Exp (iff_ b t e)
{-# INLINE iff #-}

bool :: Symantics t => Bool -> Exp t Bool
bool b = Exp (bool_ b)
{-# INLINE bool #-}

let1 :: Symantics t => Exp t a -> (Exp t a -> Exp t b) -> Exp t b
let1 (Exp x) f = Exp $ let1_ x $ runExp . f . Exp
{-# INLINE let1 #-}

fix1 :: Symantics t => (Exp t a -> Exp t a) -> Exp t a
fix1 f = Exp $ fix1_ $ runExp . f . Exp
{-# INLINE fix1 #-}

prim :: Symantics t => Prim t a -> Exp t a
prim b = Exp (prim_ b)
{-# INLINE prim #-}

fun :: Fun f => f -> f
fun = korma . uncur . cur . unkorma
{-# INLINE fun #-}

-- Plumbing used to implement fun

data TList :: (* -> *) -> * -> * where
  Cons :: Exp t a -> TList t as -> TList t (a, as)
  Nil  :: TList t ()

class Symantics (CurS as r) => Cur as r where
  type CurF as r
  type CurS as r :: * -> *
  uncur :: Exp (CurS as r) (CurF as r) -> TList (CurS as r) as -> r
  cur :: (TList (CurS as r) as -> r) -> Exp (CurS as r) (CurF as r)

instance Symantics t => Cur () (Exp t a) where
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

instance Symantics t => Fun (Exp t a) where
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

