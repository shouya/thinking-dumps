module RE where
-- Regular Expression

import DFA

import Data.List
import Control.Monad

data RE a = Concat [RE a]
          | Union  [RE a]
          | Closure (RE a)
          | Symbol a

instance (Show a) => Show (RE a) where
  show (Concat xs) = join $ map optAddParen xs
    where optAddParen x = case x of
            Closure _ -> "(" ++ show x ++ ")"
            _         -> show x
  show (Union xs) = intercalate "+" $ map show xs
  show (Closure xs) = optAddParen xs ++ "*"
    where optAddParen x = case x of
            Symbol _  -> show x
            Closure _ -> show x
            _         -> "(" ++ show x ++ ")"
  show (Symbol a) = show a




kPath :: (State s) => Integer -> Integer -> Integer -> DFA s i -> RE i
kPath i j k (DFA startState acceptStates transFunc) =
  case k of
    0 -> if i == j then

kPath i j k (DFA startState acceptStates transFunc) =





-- kPath :: DFA (Integer)
