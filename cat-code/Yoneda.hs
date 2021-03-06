{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes#-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Yoneda where

import Prelude (Functor(..), (.), IO, Monad(..), print, Integer, Int, ($), (+), (-), take, undefined, id)

-- Hom functor
type Hom a b = a -> b

-- instance Functor (a ->) where
  -- fmap :: (b -> c) -> Hom a b -> Hom a c
  -- fmap f g = f . g


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
    where foo n = Stream (f n) (foo $ n + 1)

  index :: Stream a -> Hom Integer a
  index (Stream x _)  0 = x
  index (Stream _ xs) n = index xs (n - 1)

streamToList :: Stream a -> [a]
streamToList (Stream x xs) = x:(streamToList xs)

-- a stream of an incrementing sequence [10..]
incStream :: Stream Integer
incStream = Stream 10 $ fmap (+1) incStream
-- the hom functor representation of above stream
incFunc :: Hom Integer Integer
incFunc n = n + 10

-- Yoneda Lemma

-- Yoneda on a functor F: C -> Set on a given object A in C is given by
-- [C;Set](C(A,-), F)
newtype Yoneda f a = Yoneda { runYoneda :: forall x. (a -> x) -> f x }

-- Yoneda is functorial on both f and a
instance Functor (Yoneda f) where
  -- fmap :: (a -> b) ->
  --         (forall x. (a -> x) -> f x) ->
  --         (forall y. (b -> y) -> f y)
  fmap f (Yoneda yo) = Yoneda $ \by -> yo (by . f)


-- to prove functoriality on F, we need to define a new functor class which can
-- be implemented for higher order functors
class HFunctor h where
  hfmap :: (Functor f, Functor g) => (forall a. f a -> g a) -> (forall b. h f b -> h g b)
  ffmap :: (Functor f) => forall a b. (a -> b) -> (h f a -> h f b)

instance HFunctor Yoneda where
  hfmap :: (Functor f, Functor g) => (forall a. f a -> g a) -> (forall b. Yoneda f b -> Yoneda g b)
  -- f   :: (forall a. f a -> g a)
  -- yo  :: forall x. (b -> x) -> f b
  -- ret :: forall y. (b -> y) -> g b
  hfmap f (Yoneda yo) = Yoneda $ \by -> f (yo by)


  ffmap :: (Functor f) => forall a b. (a -> b) -> (Yoneda f a -> Yoneda f b)
  -- f   :: (a -> b)
  -- yo  :: forall x. (a -> x) -> f x
  -- ret :: forall y. (b -> y) -> f y
  ffmap f (Yoneda yo) = Yoneda $ \by -> yo (by . f)

-- now we prove Yoneda F A is isomorphic to F A,
-- [C;Set](C(A,-), F) ~= F A
--
-- ((a -> x) -> f x) ~ f a
--
-- Identity ~ (* -> *) -> * -> *
newtype HIdentity f a = HIdentity { runHIdentity :: f a }

forward :: (Functor f) => forall a. Yoneda f a -> HIdentity f a
forward (Yoneda yo) = HIdentity (yo id)

backward :: (Functor f) => forall a. HIdentity f a -> Yoneda f a
backward (HIdentity fa) = Yoneda $ \ax -> fmap ax fa

main :: IO ()
main = do
  -- these show output the same list
  print $ take 10 $ streamToList $ tabulate incFunc
  print $ take 10 $ streamToList $ (tabulate . index) incStream

