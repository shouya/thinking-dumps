module With

import Data.Vect

filter' : (a -> Bool) -> Vect n a -> (p ** Vect p a)
filter' f [] = (_ ** [])
filter' f (x :: xs) =
  let (_ ** xs') = filter' f xs
  in if f x
    then (_ ** x :: xs')
    else (_ ** xs')

filter'' : (a -> Bool) -> Vect n a -> (p ** Vect p a)
filter'' f [] = (_ ** [])
filter'' f (x :: xs) with (filter'' f xs)
  | (_ ** xs') = if f x then (_ ** x :: xs') else (_ ** xs')


-- similar to view pattern in haskell?
-- https://ghc.haskell.org/trac/ghc/wiki/ViewPatterns#Basicviewpatterns


data Parity : Nat -> Type where
  Even : Parity (n + n)
  Odd  : Parity (S (n + n))

parity : (n : Nat) -> Parity n
parity Z = Even {n = Z}
parity (S Z) = Odd {n = Z}
parity (S (S k)) = ?incomplete
-- parity (S (S k)) with (parity k)
--   parity (S (S (j + j)))     | Even = Even { n = S j }
--   parity (S (S (S (j + j)))) | Odd  = Odd  { n = S j }
  -- don't know how to go futher, the error message shows it cannot prove:
  --  (S j) + (S j) ~ S (S (j + j))


-- `with' syntax can be used to further decompose (pattern matchin) on the
-- parameter with respect to the result of an expression

natToBin : Nat -> List Bool
natToBin Z = Nil
natToBin k with (parity k)
  natToBin (j + j)    | Even = False :: natToBin j
  natToBin (S (j + j))| Odd  = True  :: natToBin j
