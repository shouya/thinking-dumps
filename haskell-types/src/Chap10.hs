{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
module Chap10 where
-- Chapter 10: First class families

-- Ex 10.1-i Defunctionalize listToMaybe :: [a] -> Maybe a

import Data.Kind (Constraint, Type)
import GHC.TypeLits

newtype ListToMaybe a = ListToMaybe [a]

class Eval l r | l -> r where
  eval :: l -> r

instance Eval (ListToMaybe a) (Maybe a) where
  eval (ListToMaybe (x:_)) = Just x
  eval (ListToMaybe []) = Nothing

testDefuncOfListToMaybe = do
  print $ eval $ ListToMaybe [1,2,3]

-- higher order defunctionalization
data MapList a dfb = MapList (a -> dfb) [a]

instance Eval dfb dft => Eval (MapList a dfb) [dft] where
  eval (MapList f []) = []
  eval (MapList f (a:as)) = eval (f a) : eval (MapList f as)

testMapList = do
  print $ eval $ MapList ListToMaybe [[1,2,3], [1], []]

-- defunctionalization on type level, i.e. first class families

-- the only important thing about TExp is that it needs to return "Type" and
-- have type variable 'a' in it. It can be any of the followings:
-- type TExp a = Type -> a -> Type
-- type TExp a = [a] -> Int -> Type
type TExp a = a -> Type

type family TEval (e :: TExp a) :: a

-- this type has no data constructor
data Snd :: (a, b) -> TExp b

--- type level tuple: '(,)
type instance TEval (Snd '(a, b)) = b

data FromMaybe :: a -> Maybe a -> TExp a
type instance TEval (FromMaybe _ ('Just a)) = a
type instance TEval (FromMaybe a 'Nothing) = a
-- :kind! TEval (FromMaybe 2 'Nothing)  => 2
-- :kind! TEval (FromMaybe 2 ('Just 1)) => 1

-- Ex 10.2-i defuncitionalize listToMaybe at the type level
data TListToMaybe :: [a] -> TExp (Maybe a)
type instance TEval (TListToMaybe '[]) = 'Nothing
type instance TEval (TListToMaybe (x ': xs)) = 'Just x
-- :kind! TEval (TListToMaybe '[1,2,3]) => 'Just 1
-- :kind! TEval (TListToMaybe '[]) => 'Nothing

-- defunctionalization of higher-order functions on type level
data TMapList :: (a -> TExp b) -> [a] -> TExp [b]
type instance TEval (TMapList f '[]) = '[]
type instance TEval (TMapList f (x ': xs)) =
  TEval (f x) ': TEval (TMapList f xs)


-- ex 10.2-ii defunctionalize foldr :: (a -> b -> b) -> b -> [a] -> b
data Foldr :: (a -> b -> TExp b) -> b -> [a] -> TExp b
type instance TEval (Foldr f b '[]) = b
type instance TEval (Foldr f b (a ': as)) =
  TEval (f a (TEval (Foldr f b as)))

-- a helper defunc of a function for demonstration
data Minus :: Nat -> Nat -> TExp Nat
type instance TEval (Minus n m) = n - m
-- :kind! TEval (Minus 3 2) :: Nat = 1

{-
λ> :kind! TEval (Foldr Minus 1 '[4, 3, 2])
TEval (Foldr Minus 1 '[4, 3, 2]) :: Nat
= 2

λ> foldr (-) 1 [4, 3, 2]
2
-}

-- first-class families form a monad at type-level
data Pure :: a -> TExp a
data (>>=) :: TExp a -> (a -> TExp b) -> TExp b

type instance TEval (Pure a) = a
type instance TEval (a >>= f) = TEval (f (TEval a))


{-
| data level           | type level              |
|----------------------+-------------------------|
| value/term           | type                    |
| type of function     | type family             |
| function defn        | type instance           |
| type                 | kind                    |
| typeclass & function | typeclass & assoc type  |
|----------------------+-------------------------|
| data constructor     | type constructor        |
| higher-order func    | higher-order type       |
-}

data Map :: (a -> TExp b) -> f a -> TExp (f b)

-- Ex 10.4-i write a promoted functor instance for tuples

type instance TEval (Map f '(a, b)) = '(TEval (f b), a)
