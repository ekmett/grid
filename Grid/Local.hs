{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Grid.Local
  ( Local(..)
  , eval
  ) where

import Control.Applicative
import Control.Comonad
import Control.Monad.Fix
import Data.Foldable
import Data.Traversable
import Grid.Symantics
import Grid.Exp

newtype Local a = Local { runLocal :: a }
  deriving (Eq,Ord,Num,Enum,Fractional,Floating,Real,Integral,RealFrac,RealFloat)

instance Foldable Local where
  foldMap f (Local a) = f a

instance Traversable Local where
  traverse f (Local a) = Local <$> f a

instance Functor Local where
  fmap f (Local a) = Local (f a)
  b <$ _ = Local b

instance Applicative Local where
  pure = Local
  Local f <*> Local x = Local (f x)
  a <* _ = a
  _ *> b = b

instance Monad Local where
  return = Local
  Local a >>= f = f a
  _ >> b = b

instance Show a => Show (Local a) where
  showsPrec d (Local a) = showParen (d > 10) $ showString "Local " . showsPrec 11 a

instance Extend Local where
  extend f w@(Local _) = Local (f w)

instance Comonad Local where
  extract = runLocal

-- direct local evaluation
instance Symantics Local where
  Local f `app_` Local x = Local (f x)
  lam_ f = Local (runLocal . f . Local)
  lit_ = Local
  let1_ x f = f x
  fix1_ = fix
  bool_ = Local
  iff_ (Local b) x y = if b then x else y
  prim_ x = x

-- |
--
-- > eval = extract
eval :: Exp Local a -> a
eval = extract
{-# INLINE eval #-}
