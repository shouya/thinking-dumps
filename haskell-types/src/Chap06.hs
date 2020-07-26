{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}

module Chap06 where

import Data.Typeable (Proxy)
import Control.Monad.Trans.Class (MonadTrans (..))

-- Chapter 6 Rank-N Types

-- applyToFive :: (a -> a) -> Int
-- applyToFive f = f 5

--
-- The type is labeled "Rank-N" where N is the number of foralls which
-- are nested and cannot be merged with a previous one.
-- https://wiki.haskell.org/Rank-N_types

-- Ex 6.3-i What is the rank of Int -> forall a. a -> a
-- 1. add parentheses:
--    Int -> forall a. a -> a
-- ~  Int -> (forall a. (a -> a))
-- ~  forall a. Int -> (a -> a)
-- ~  forall a. Int -> a -> a
--
-- 2. number of nested unmergeable "forall": 1, thus it's a Rank-1 type
--

-- Ex 6.3-ii What is the rank of (a -> b) -> (forall c. c -> a) -> b
--   (a -> b) -> (forall c. c -> a) -> b
-- ~ forall a b. (a -> b) -> (forall c. c -> a) -> b
--
-- The latter forall is cannot be moved to the left because it appears on the
-- left of "-> b". Thus this type has Rank-2.
--

-- Ex 6.3-iii What is the rank of
-- ((forall x. m x -> b (z m x)) -> b (z m a)) -> m a?
--
--   ((forall x. m x -> b (z m x)) -> b (z m a)) -> m a
--   forall m b z. ((forall x. m x -> b (z m x)) -> b (z m a)) -> m a
-- The deepest nested "forall" layer is 3, so it's a Rank-3 type.

newtype Cont a = Cont
  { runCont :: forall r. (a -> r) -> r
  }

fromCont :: Cont a -> a
fromCont (Cont f) = f id

toCont :: a -> Cont a
toCont a = Cont $ \ar -> ar a

instance Functor Cont where
  fmap :: (a -> b) -> Cont a -> Cont b
  fmap f (Cont arr) = Cont (\br -> arr (br . f))
  -- fmap f (Cont arr) = Cont (\br -> br (arr f))

instance Applicative Cont where
  pure a = Cont (\ar -> ar a)

  (<*>) :: forall a b. Cont (a -> b) -> Cont a -> Cont b
  -- abrr :: ((a -> b) -> r) -> r
  (Cont abrr) <*> (Cont arr) = fmap ab (Cont arr)
    where ab :: a -> b
          ab = abrr id

instance Monad Cont where
  (>>=) :: forall a b. Cont a -> (a -> Cont b) -> Cont b
  (Cont arr) >>= acb = Cont $ \br ->
    let a        = arr id
        Cont brr = acb a
    in brr br

newtype ContT m a = ContT
  { runContT :: forall r. (a -> m r) -> m r
  }

instance Functor (ContT m) where
  fmap :: (a -> b) -> ContT m a -> ContT m b
  fmap f (ContT a) = ContT $ \br -> a (br . f)

instance Applicative (ContT m) where
  pure :: a -> ContT m a
  pure a = ContT $ \amr -> amr a

  (<*>) :: forall a b. ContT m (a -> b) -> ContT m a -> ContT m b
  -- bmr :: b -> m r
  -- abmrmr :: ((a -> b) -> m r) -> m r
  -- amrmr :: (a -> m r) -> m r
  -- goal :: m r
  (ContT abmrmr) <*> (ContT amrmr) = ContT $ \bmr ->
    abmrmr $ \ab -> amrmr $ \a -> bmr $ ab a

instance Monad (ContT m) where
  (>>=) :: ContT m a -> (a -> ContT m b) -> ContT m b

  -- ma :: (a -> m r) -> m r
  -- f :: a -> ContT m b
  -- bmr :: b -> m r
  -- goal :: mr
  (ContT ma) >>= f = ContT $ \bmr ->
    ma $ \a -> runContT (f a) $ \b -> bmr b

instance MonadTrans ContT where
  -- lift :: Monad m => m a -> ContT m a
  -- ma :: m a
  -- amr :: a -> m r
  -- goal :: m r
  lift ma = ContT $ \amr -> ma >>= amr

usageExample :: IO ()
usageExample = flip runContT (putStrLn) $ do
  i <- lift (return 10 :: IO Int)
  i' <- ContT $ \k -> k $ i + 1
  i'' <- ContT $ \k -> k $ i' * 2
  return (show i'') -- prints 22
