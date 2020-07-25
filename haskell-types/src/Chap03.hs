{-# LANGUAGE InstanceSigs #-}

module Chap03 where

{-
Chapter 3 Variance
-}

import Data.Functor.Contravariant
import Data.Functor.Invariant

{-
Ex 3-i Which of these types are Functors? Give instances for the ones that are.
-}
newtype T1 a = T1 (Int -> a)
instance Functor T1 where
  fmap f (T1 ia) = T1 (f . ia)

newtype T2 a = T2 (a -> Int)
instance Contravariant T2 where
  contramap f (T2 ai) = T2 (ai . f)

newtype T3 a = T3 (a -> a)
instance Invariant T3 where
  invmap :: (a -> b) -> (b -> a) -> T3 a -> T3 b
  invmap ab ba (T3 aa) = T3 (ab . aa . ba)

newtype T4 a = T4 ((Int -> a) -> Int)
instance Contravariant T4 where
  contramap :: (b -> a) -> T4 a -> T4 b
  contramap ba (T4 iai) = T4 (\ib -> iai $ ba . ib)

newtype T5 a = T5 ((a -> Int) -> Int)
instance Functor T5 where
  fmap ab (T5 aii) = T5 (\bi -> aii $ bi . ab)
