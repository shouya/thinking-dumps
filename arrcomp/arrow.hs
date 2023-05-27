{-# LANGUAGE InstanceSigs #-}

import Control.Category
import Control.Arrow

import Prelude hiding (id, (.))

-- Exerciser 1: Write Arrow instances for the following types
newtype Reader s i o = R ((s,i) -> o)
newtype Writer i o = W (i -> (String, o))

--- Solution:
instance Category (Reader s) where
  id :: Reader s i i
  id = R $ \(_s,i) -> i

  (.) :: Reader s b c -> Reader s a b -> Reader s a c
  (.) (R f) (R g) = R $ \(s,a) -> f (s, g (s,a))

instance Arrow (Reader s) where
  arr :: (i -> o) -> Reader s i o
  arr f = R $ \(_s,i) -> f i

  first :: Reader s i o -> Reader s (i, b) (o, b)
  first (R f) = R $ \(s,(i,b)) -> (f (s,i), b)

instance Category Writer where
  id :: Writer i i
  id = W $ \i -> ("", i)

  (.) :: Writer b c -> Writer a b -> Writer a c
  (.) (W f) (W g) = W $ \a -> let (s1, b) = g a
                                  (s2, c) = f b
                              in (s1 ++ s2, c)

instance Arrow Writer where
  arr :: (i -> o) -> Writer i o
  arr f = W $ \i -> ("", f i)

  first :: Writer i o -> Writer (i, b) (o, b)
  first (W f) = W $ \(i,b) -> let (s, o) = f i
                              in (s, (o, b))

-- Exerciser 2: The following is almost an arrow type, what goes wrong?
newtype ListMap i o = LM ([i] -> [o])

-- Solution: we just try it!
instance Category ListMap where
  id :: ListMap i i
  id = LM id

  (.) :: ListMap b c -> ListMap a b -> ListMap a c
  (.) (LM f) (LM g) = LM $ f . g

instance Arrow ListMap where
  arr :: (i -> o) -> ListMap i o
  arr f = LM $ map f

  first :: ListMap i o -> ListMap (i, b) (o, b)
  first (LM f) = LM $ \xs ->
    let (is, os) = unzip xs
    --- note: there is no guarantee that `length (f is) == length is`.
    --- so the zip is not working. this is the problem.
    in zip (f is) os

-- Exerciser 3: Define the following as an arrow type
data Stream a = Cons a (Stream a)
newtype StreamMap i o = SM (Stream i -> Stream o)

-- Solution:
runSM :: StreamMap i o -> Stream i -> Stream o
runSM (SM f) = f

instance Category StreamMap where
  id :: StreamMap i i
  id = SM id

  (.) :: StreamMap b c -> StreamMap a b -> StreamMap a c
  (.) (SM f) (SM g) = SM $ f . g

instance Arrow StreamMap where
  arr :: (i -> o) -> StreamMap i o
  arr f = SM $ \(Cons i s) -> Cons (f i) (runSM (arr f) s)

  first :: StreamMap i o -> StreamMap (i, b) (o, b)
  first (SM f) = SM $ lift f
    where
      lift :: (Stream i -> Stream o) -> Stream (i, b) -> Stream (o, b)
      lift f s = zipStream (f (runSM (arr fst) s)) ((runSM (arr snd) s))

      zipStream :: Stream a -> Stream b -> Stream (a, b)
      zipStream (Cons a as) (Cons b bs) = Cons (a, b) (zipStream as bs)

-- Exerciser 4: Show that the following is a functor:
zipRf :: (Arrow y) => y a b -> (c -> c') -> y (a, c) (b, c')
zipRf f g = first f >>> arr (id *** g)
