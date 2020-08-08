{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Chap08 where

-- Chapter 8: Roles

import Data.Coerce (Coercible(..), coerce)
import Data.Monoid (Sum(..), Product(..))
import qualified Data.Map as M

slowSum :: [Int] -> Int
slowSum = getSum . mconcat . fmap Sum

fastSum :: [Int] -> Int
fastSum = getSum . mconcat . coerce

newtype Reverse a = Reverse { getReverse :: a }

instance Eq a => Eq (Reverse a) where
  Reverse a == Reverse b = a == b
instance Ord a => Ord (Reverse a) where
  compare (Reverse a) (Reverse b) = compare b a

{-
λ> coerce (M.singleton 'S' True) :: M.Map Char (Reverse Bool)
coerce (M.singleton 'S' True) :: M.Map Char (Reverse Bool)
  :: M.Map Char (Reverse Bool)

λ> coerce (M.singleton 'S' True) :: M.Map (Reverse Char) Bool

<interactive>:16:1-29: error:
    • Couldn't match type ‘Char’ with ‘Reverse Char’
        arising from a use of ‘coerce’
    • In the expression:
          coerce (M.singleton 'S' True) :: M.Map (Reverse Char) Bool
      In an equation for ‘it’:
          it = coerce (M.singleton 'S' True) :: M.Map (Reverse Char) Bool
(0.01 secs,)
-}

{-
A role is a property of type variables. There are three kinds of roles:

- nominal: the usual (~) constraint
- representational: types that has same memory layout
- phantom: a phantom type is not used anywhere so they always equal
-}

{-
Ex 8.2-i What is the role signature of `Either a b`?

The role signature of a and b in Either a b are both representational,
because they are applied in the data constructor Left or Right.

See https://gitlab.haskell.org/ghc/ghc/-/wikis/roles#role-inference
for the rules for inferring role signatures.
-}

{-
Ex 8.2-ii What is the role signature of `Proxy a`?

Phantom, this one is obvious.
-}
