{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Chap05 where

{- Chapter 5. Constraints and GADTs -}

import Data.Kind (Constraint, Type)
import Data.List (intercalate)

five :: Int
five = 5

five_ :: (a ~ Int) => a
five_ = 5

data Expr a where
  LitInt :: Int    -> Expr Int
  LitBool :: Bool  -> Expr Bool
  Add :: Expr Int  -> Expr Int -> Expr Int
  Not :: Expr Bool -> Expr Bool
  If :: Expr Bool  -> Expr a -> Expr a -> Expr a

-- above GADTs definition is equivalent to the following
data Expr_ a
  = (a ~ Int)  => LitInt_ Int
  | (a ~ Bool) => LitBool_ Bool
  | (a ~ Int)  => Add_ (Expr Int) (Expr Int)
  | (a ~ Bool) => Not_ (Expr Int)
  | If_ (Expr Bool) (Expr a) (Expr a)

evalExpr :: Expr a -> a
evalExpr (LitInt i) = i
evalExpr (LitBool b) = b -- return type is different from the previous one!
evalExpr (Add a b) = evalExpr a + evalExpr b
evalExpr (Not a) = not $ evalExpr a
evalExpr (If b x y) = if evalExpr b
                      then evalExpr x
                      else evalExpr y

data HList (ts :: [Type]) where
  HNil :: HList '[]
  (:#) :: t -> HList ts -> HList (t ': ts)

infixr 5 :#

hLength :: HList ts -> Int
hLength HNil = 0
hLength (_ :# xs) = 1 + hLength xs

-- instance Show (HList '[]) where
--   show _ = "[]"

-- instance (Show t, Show (HList ts)) => Show (HList (t ': ts)) where
--   show (x :# xs) = show x ++ ":" ++ show xs

-- instance Eq (HList '[]) where
--   HNil == HNil = True

-- instance (Eq t, Eq (HList ts)) => Eq (HList (t ': ts)) where
--   (x:#xs) == (y:#ys) = x == y && xs == ys

-- instance Ord (HList '[]) where
--   HNil <= HNil = True

-- instance (Ord t, Ord (HList ts)) => Ord (HList (t ': ts)) where
--   (x:#xs) <= (y:#ys) = x <= y || xs <= ys

-- The [Type] here is already type-level list
type family AllEq (ts :: [Type]) :: Constraint where
  AllEq '[] = ()
  AllEq (t ': ts) = (Eq t, AllEq ts)

type family All (c :: Type -> Constraint) (ts :: [Type]) :: Constraint where
  All c '[] = ()
  All c (t ': ts) = (c t, All c ts)


instance All Eq ts => Eq (HList ts) where
  HNil == HNil = True
  (a :# as) == (b :# bs) = a == b && as == bs

instance (All Eq ts, All Ord ts) => Ord (HList ts) where
  HNil <= HNil = True
  (a :# as) <= (b :# bs) = a <= b || as <= bs


instance All Show ts => Show (HList ts) where
  show HNil = "[]"
  show xs = "[" ++ (intercalate "," $ showAll xs) ++ "]"
    where showAll :: All Show ts => HList ts -> [String]
          showAll (x :# HNil) = [show x]
          showAll (x :# xs) = (show x) : (showAll xs)

sampleHList :: HList '[String, Int, Float, Bool]
sampleHList = "hello" :# 5 :# 12.0 :# True :# HNil
