{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- Chapter 9: Associated type families

module Chap09 where

import Data.Kind (Type)
import Data.Monoid ((<>))
import Data.Proxy (Proxy (..))
import GHC.TypeLits

data (a :: k1) :<< (b :: k2)
infixr 5 :<<

class HasPrintf a where
  -- associated type family
  type Printf a :: *
  format :: String -> Proxy a -> Printf a

instance KnownSymbol text => HasPrintf (text :: Symbol) where
  type Printf text = String
  format s _p = s <> (symbolVal (Proxy @text))

instance (HasPrintf a, KnownSymbol text) =>
         HasPrintf ((text :: Symbol) :<< a) where
  type Printf (text :<< a) = Printf a
  format s _p = format s' (Proxy @a)
    where s' = s <> (symbolVal (Proxy @text))

instance (HasPrintf a, Show t) => HasPrintf (t :<< a) where
  type Printf (t :<< a) = t -> Printf a
  format s _p x = format s' (Proxy @a)
    where s' = s <> show x

-- this case is there to prevent showing double quote for strings
instance {-# OVERLAPPING #-} HasPrintf a => HasPrintf (String :<< a) where
  type Printf (String :<< a) = String -> Printf a
  format s _p x = format s' (Proxy @a)
    where s' = s <> x

--  format :: String -> Proxy a -> Printf a
printf :: forall a. HasPrintf a => Proxy a -> Printf a
printf _ = format "" (Proxy @a)

testOut :: IO ()
testOut = do
  putStrLn $ printf (Proxy @(String :<< " world")) "hello"
  putStrLn $ printf (Proxy @(Int :<< " + " :<< Int :<< " = " :<< Int :<< "")) 1 2 3

  -- Please note that the following is not supported because only symbols can be the base case
  -- putStrLn $ printf (Proxy @(Int :<< " + " :<< Int :<< " = " :<< Int)) 1 2 3

  return ()

-- I have tried to make it support non-symbol as the base case but
-- didn't find a successful way to do that. I have to hope the rest of the book
-- to have more about it.
