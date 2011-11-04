{-# LANGUAGE
  GADTs,
  ConstraintKinds,
  TypeOperators,
  FunctionalDependencies,
  FlexibleInstances,
  FlexibleContexts,
  KindSignatures,
  OverlappingInstances,
  TypeFamilies,
  DeriveFunctor,
  UndecidableInstances,
  ImplicitParams
  #-}

import Data.Functor.Apply

-- a very simple syntax/semantics
class Apply t => Sym t where
  type Lit t :: * -> Constraint
  lam  :: (t a -> t b) -> t (a -> b)
  lit  :: Lit t a => a -> t a

let1 :: Sym t => t a -> (t a -> t b) -> t b
let1 x f = lam f <.> x

-- a trivial symantics transformer, used for type pattern matching in Fun
newtype T t a = T { runT :: t a }
  deriving (Eq,Ord,Show,Functor)

instance Apply t => Apply (T t) where
  T f <.> T x = T (f <.> x)

instance Sym t => Sym (T t) where
  type Lit (T t) = Lit t
  lam f = T $ lam $ runT . f . T
  lit a = T (lit a)

class Trivial a
instance Trivial a

-- local evaluation symantics
newtype Id a = Id { runId :: a }
  deriving (Eq,Ord,Show,Functor)

instance Apply Id where
  Id f <.> Id x = Id (f x)

instance Sym Id where
  type Lit Id = Trivial
  lam f = Id (runId . f . Id)
  lit = Id

{-
data HList (as :: [*]) where
  Cons :: a -> HList as -> HList '(a:as)
  Nil :: HList '[]
-}

data TList :: (* -> *) -> * -> * where
  Cons :: T t a -> TList t as -> TList t (a, as)
  Nil  :: TList t ()

class Rev xs ys zs | xs ys -> zs, ys zs -> xs where
  rev' :: TList t xs -> TList t ys -> TList t zs

instance Rev xs () xs where
  rev' xs _ = xs

instance Rev (y, xs) ys zs => Rev xs (y, ys) zs where
  rev' xs (Cons y ys) = rev' (Cons y xs) ys

rev :: Rev () ys zs => TList t ys -> TList t zs
rev = rev' Nil

app :: Sym t => t (a -> b) -> t a -> t b
app f x = f <.> x

class Sym t => SymList f t as r rs | t as -> f r rs, rs -> t as f r where
  unc :: T t f -> TList t as -> r
  cur :: (TList t as -> r) -> T t f
  korma :: (TList t as -> r) -> rs
  unkorma :: rs -> TList t as -> r

instance Sym t => SymList a t () (T t a) (T t a) where
  unc f Nil = f
  cur f = f Nil
  korma f = f Nil
  unkorma r _ = r

instance SymList b t bs r rs => SymList (a -> b) t (a,bs) r (T t a -> rs) where
  unc f (Cons a as) = unc (f <.> a) as
  cur f = lam (\x -> cur (f . Cons x))
  korma f x = korma (f . Cons x)
  unkorma f (Cons a as) = unkorma (f a) as

type family FunB rs
type instance FunB (T t a) = a
type instance FunB (T t a -> rs) = a -> FunB rs

type family FunT rs :: * -> *
type instance FunT (T t a) = t
type instance FunT (T t a -> rs) = t

type family FunL rs
type instance FunL (T t a) = ()
type instance FunL (T t a -> rs) = (a,FunL rs)

type family FunR rs
type instance FunR (T t a) = a
type instance FunR (T t a -> r) = FunR r

class SymList (FunB rs) (FunT rs) (FunL rs) (FunR rs) rs => Fun rs
instance SymList (FunB rs) (FunT rs) (FunL rs) (FunR rs) rs => Fun rs

fun :: Fun rs => rs -> rs
fun x = korma (unc (cur (unkorma x)))



{-
fun ::
  (Fun o t as (T t a -> r)
  , ApplyList (T t a -> i) t as o
  ) => (T t a -> i) -> T t a -> r
fun i = unpack (applyAll i)
-}

-- fun i = unpack (pack i)

{-
instance Fun (T t a -> 
  funk f = f Nil -- applyAll f (rev as)
  funk f a = funk f (Cons a as)

class Collect t as where
  collect :: (TList t as -> o) -> i

instance Fun (T t a) t () (T t a) where
  funk i Nil = i

  apply f Nil = f
  apply f (Cons a as) = pack (f <.> a) as

  funk f as a = funk f (Cons a as)

fun :: Fun i t l o => o -> o
fun i = pack i

instance Fun (T t bi) t cs o => Fun (T t (c -> bi)) t (x,xs) (T t c -> o) where
-}

{-
-- variadic captured lambda abstractions
class Fun (t :: * -> *) x | x -> t where
  type FunL x -- :: [*]
  funk :: T t a -> TList t (FunL x) -> T t a -> x

fun :: 

instance Fun t (T t a) where
  type FunL (T t a) = ()
  funk x Nil y = T (app x y)

instance Fun t x => Fun t (T t a -> x) where
  type FunL (T t a) = (a, FunL x)
  funK 

{-
  pack :: x -> HList (FunH x) -> x
  unpack :: (HList (FunH x) -> x) -> x
-}

instance Fun t (T t a) where
  type FunH (T t a) = () -- '[]
  pack i Nil = i
  unpack f = f Nil

instance Fun t x => Fun t (T t a -> x) where
  type FunH (T t a -> x) = (T t a, FunH x) -- a : FunH x
  -- pack f (Cons a as) = pack (f a) as
  unpack f a = unpack $ \as -> f (Cons a as)

fun :: Fun t x => (T t a -> x) -> (T t a -> x)
fun = undefined

{-
data E p where
  Var :: {-# UNPACK #-} !Int -> E p
  App :: E p -> E p -> E p
  Lam :: (E p -> E p) -> E p
  Lit :: p a => a -> E p

newtype Exp p a = Exp { runExp :: E p }
-}

{-
lam :: (Exp p a -> Exp p b) -> Exp p (a -> b)
lam f = Exp $ Lam $ runExp . f . Exp

app :: Exp p (a -> b) -> Exp p a -> Exp p b
Exp f `app` Exp x = Exp $ App f x

lit :: p a => a -> Exp p a
lit a = Exp $ Lit a
-}
-}
