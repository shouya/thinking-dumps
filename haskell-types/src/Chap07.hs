{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}


module Chap07 where

import Data.Typeable (Typeable, cast)
import Data.Maybe (fromMaybe)
import Data.Foldable (asum)
import Data.Kind (Constraint, Type)

import System.IO.Unsafe (unsafePerformIO)
import Data.IORef (IORef, newIORef, readIORef, writeIORef, modifyIORef)

-- Chapter 7: Existential Types

data Any = forall a. Any a

-- "Any" as a data constructor: Any :: a -> Any

-- alternatively, use GADTs

{-
data Any where
  Any :: a -> Any
-}

anyList :: [Any]
anyList = [Any 5, Any True, Any "hello"]

elimAny :: (forall a. a -> r) -> Any -> r
elimAny f (Any a) = f a

-- Ex 7.1-i Are functions of type forall a. a -> r interesting? Why or why not?
--
-- Not interesting. (forall a. a -> r) means that r can be derived for all
-- possible values of a, therefore r cannot be depend on a.

data HasShow where
  -- t is hidden in HasShow, so this is an existential type
  HasShow :: Show t => t -> HasShow

{-
instance Show HasShow where
  show (HasShow s) = show s
-}

showableList :: [HasShow]
showableList = [HasShow 1, HasShow "5", HasShow True]

printShowableList :: IO ()
-- print :: Show a => a -> IO ()
printShowableList = mapM_ print showableList

-- Ex 7.1-ii what happens to this instance if you remove the Show t =>
-- constraint from HasShow?
-- A: It will become the same as Any.

elimHasShow :: (forall a. Show a => a -> r) -> HasShow -> r
elimHasShow f (HasShow a) = f a

-- Ex 7.1-iii write the Show instance for HasShow in terms of elimHasShow
instance Show HasShow where
  show a = elimHasShow show a


-- Dynamic typing
data Dynamic where
  Dynamic :: Typeable t => t -> Dynamic

elimDynamic :: (forall a. Typeable a => a -> r) -> Dynamic -> r
elimDynamic f (Dynamic a) = f a

fromDynamic :: Typeable a => Dynamic -> Maybe a
fromDynamic = elimDynamic cast

pyPlus :: Dynamic -> Dynamic -> Dynamic
pyPlus a b = fromMaybe (error "bad types for pyPlus") $ asum
  [ defBinOp @String @String (++)
  , defBinOp @Int @Int (+)
  , defBinOp @Int @String (\a b -> show a ++ b)
  , defBinOp @String @Int (\a b -> a ++ show b)
  ]
  where defBinOp :: forall a b r. (Typeable a, Typeable b, Typeable r) =>
          (a -> b -> r) -> Maybe Dynamic
        defBinOp f = do
          da <- fromDynamic a
          db <- fromDynamic b
          return $ Dynamic $ f da db
-- this is crazy!!!

data Has (c :: Type -> Constraint) where
  Has :: c t => t -> Has c

elimHas :: (forall a. c a => a -> r) -> Has c -> r
elimHas f (Has a) = f a

-- :i MonoidAndEq
-- type MonoidAndEq a = (Monoid a, Eq a) :: Constraint
type MonoidAndEq a = (Monoid a, Eq a)

-- constraint synonym
class    (Monoid a, Eq a) => MonoidEq a
instance (Monoid a, Eq a) => MonoidEq a

-- since s is nowhere found in the definition, it cannot be leaked out.
newtype ST s a = ST { unsafeRunST :: a }

instance Functor (ST s) where
  fmap f (ST a) = a `seq` ST $ f a

instance Applicative (ST s) where
  pure = ST
  ST f <*> ST a = f `seq` a `seq` ST $ f a

instance Monad (ST s) where
  ST a >>= f = a `seq` f a

-- now we introduce mutable variables
newtype STRef s a = STRef { unSTRef :: IORef a }

-- unifying the two type variables 's' below
newSTRef :: a -> ST s (STRef s a)
newSTRef a = ST $ STRef $ unsafePerformIO $ newIORef a

readSTRef :: STRef s a -> ST s a
readSTRef ref = ST $ unsafePerformIO $ readIORef $ unSTRef ref

writeSTRef :: STRef s a -> a -> ST s ()
writeSTRef ref a = ST $ unsafePerformIO $ writeIORef (unSTRef ref) a

modifySTRef :: STRef s a -> (a -> a) -> ST s ()
modifySTRef ref f = ST $ unsafePerformIO $ modifyIORef (unSTRef ref) f

runST :: (forall s. ST s a) -> a
runST = unsafeRunST

safeExample :: ST s String
safeExample = do
  ref <- newSTRef "hello"
  modifySTRef ref (++ " world")
  readSTRef ref

-- λ> :t runST
-- runST :: (forall s. ST s a) -> a
-- λ> :t unsafeRunST
-- unsafeRunST :: ST s a -> a
