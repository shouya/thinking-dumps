{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes#-}
{-# LANGUAGE InstanceSigs #-}

module Yoneda where

import Prelude (Functor(..), (.), IO, Monad(..), print, Integer, Int, ($), (+), (-), take)

-- Hom functor
newtype Hom a b = Hom { unHom :: a -> b }

instance Functor (Hom a) where
  -- fmap :: (b -> c) -> Hom a b -> Hom a c
  fmap f g = Hom (f . unHom g)


-- a functor f is representable by (Rep f) if Hom(Rep f, -)
-- is isomorphic to f. ie. tabulate . index = index . tabulate = id
class (Functor f) => Representable f where
  type Rep f :: *
  tabulate :: forall a. Hom (Rep f) a -> f a
  index :: forall a. f a -> Hom (Rep f) a

-- an infinite stream is representable by (non-negative) Integer
data Stream e = Stream e (Stream e)

instance Functor Stream where
  fmap f (Stream x xs) = Stream (f x) (fmap f xs)

instance Representable Stream where
  type Rep Stream = Integer

  tabulate :: Hom Integer a -> Stream a
  tabulate f = foo 0
    where foo n = Stream (unHom f n) (foo $ n + 1)
  
  index :: Stream a -> Hom Integer a
  index (Stream x xs)  = Hom $ foo
    where foo 0 = x
          foo n = (unHom $ index xs) (n - 1)

streamToList :: Stream a -> [a]
streamToList (Stream x xs) = x:(streamToList xs)

-- a stream of an incrementing sequence [10..]
incStream :: Stream Integer
incStream = Stream 10 $ fmap (+1) incStream
-- the hom functor representation of above stream
incFunc :: Hom Integer Integer
incFunc = Hom $ \n -> n + 10

main :: IO ()
main = do
  -- these show output the same list
  print $ take 10 $ streamToList $ tabulate incFunc
  print $ take 10 $ streamToList $ (tabulate . index) incStream
