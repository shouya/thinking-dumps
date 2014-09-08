module RE where
-- Regular Expression

import DFA
import State

import Prelude hiding (concat)
import Data.List hiding (concat, union)
import Control.Monad

data RE a = Concat [RE a]
          | Union  [RE a]
          | Closure (RE a)
          | Symbol a
          | Epsilon
          | EmptySet

instance (Eq a) => Eq (RE a) where
  Concat xs == Concat ys = xs == ys
  Union xs == Union ys = xs == ys
  Closure x == Closure y = x == y
  Symbol a == Symbol b = a == b
  Epsilon == Epsilon = True
  EmptySet == EmptySet = True
  _ == _ = False


concat :: (Eq a) => [RE a] -> RE a
concat xs = case length xs' of
  0 -> Epsilon
  1 -> head xs'
  _ -> Concat xs'
  where xs' = if any (== EmptySet) xs then []
              else filter (/= Epsilon) xs
union :: (Eq a) => [RE a] -> RE a
union xs = case length xs' of
  0 -> Epsilon
  1 -> head xs'
  _ -> Union xs'
  where xs' = nub $ filter (/= EmptySet) xs

closure :: RE a -> RE a
closure Epsilon = Epsilon
closure x = Closure x


{- {- For debug uses -}
union = Union
closure = Closure
concat = Concat
-}

instance (Show a) => Show (RE a) where
  show (Concat xs) = join $ map optAddParen xs
    where optAddParen x = case x of
            Closure _ -> "(" ++ show x ++ ")"
            Union _   -> "(" ++ show x ++ ")"
            _         -> show x
  show (Union xs) = intercalate "+" $ map show xs
  show (Closure xs) = optAddParen xs ++ "*"
    where optAddParen x = case x of
            Symbol _  -> show x
            Closure _ -> show x
            _         -> "(" ++ show x ++ ")"
  show (Symbol a) = show a
  show Epsilon = "ε"
  show EmptySet = "∅"




kPath :: (IntState s, Eq s, Eq i) =>
         Integer -> Integer -> Integer ->    -- i,j,k
         DFA s i -> RE i
kPath i j 0 (DFA _ _ transFunc) =
  if i == j then Epsilon
  else case find (\(s,_,s') -> noToState i == s &&
                               noToState j == s') transtbl of
         Just (_,input,_) -> Symbol input
         Nothing          -> EmptySet
  where transtbl = transFuncToTable transFunc
kPath i j k dfa =
  union [kPath i j (k - 1) dfa
        ,concat [kPath i k (k - 1) dfa
                ,closure (kPath k k (k - 1) dfa)
                ,kPath k j (k - 1) dfa
                ]]





-- kPath :: DFA (Integer)
