{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Chap11 where

import Fcf
import GHC.TypeLits
import Data.Proxy
import Data.Kind
import Unsafe.Coerce

data OpenSum (f :: k -> Type) (ts :: [k]) where
  UnsafeOpenSum :: Int -> f t -> OpenSum f ts

-- data FindIndex :: (a -> Exp Bool) -> [a] -> Exp (Maybe Nat)
-- data TyEq :: a -> b -> Exp Bool
-- data FromMaybe :: k -> Maybe k -> Exp k
-- type family Stuck :: a
--   A stuck type that can be used like a type-level undefined.
--

-- :kind Member: k -> [k] -> Expr Nat
type FindElem (key :: k) (ts :: [k]) =
  FromMaybe Stuck =<< FindIndex (TyEq key) ts
-- This function returns "Stuck" if the element is not found.

-- :kind Member: k -> [k] -> Constraint
type Member t ts = KnownNat (Eval (FindElem t ts))

-- this will only accept t and ts where t is found in ts, returns the
-- index of t in ts
findElem :: forall t ts. Member t ts => Int
findElem = fromIntegral $ natVal $ Proxy @(Eval (FindElem t ts))

inj :: forall f t ts. Member t ts => f t -> OpenSum f ts
inj ft = UnsafeOpenSum (findElem @t @ts) ft

prj :: forall f t ts. Member t ts => OpenSum f ts -> Maybe (f t)
prj (UnsafeOpenSum i ft) = if i == findElem @t @ts
                           then Just $ unsafeCoerce ft
                           else Nothing

-- I am not capable of following the text for this chapter. Other than
-- repeating what author says without able to comprehend, I decided to skip
-- the chapter. May come back later.
