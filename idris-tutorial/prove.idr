module Prove

-- One can prove theorems with idris (of course!)

-- propositional equality is defined as below:
--
-- data (=) : a -> b -> Type where
--   Refl : x = x

twoPlusTwo : 2 + 2 = 4
twoPlusTwo = Refl

-- The bottom type (Empty type) has no constructor, we can use it to represent
-- negation of proposition.

disjoint : {n : Nat} -> (Z = S n) -> Void
disjoint p = replace {P = disjointTy} p ()
  where disjointTy : Nat -> Type
        disjointTy Z     = ()
        disjointTy (S _) = Void

-- where the library function `replace' has type of
--
--    replace : (x = y) -> P x -> P y

-- above definition is reduced as:
--
-- replace { P = disjointTy } p ()
-- replace { P = disjointTy } (Z = S n) ()
-- (f : (disjointTy Z -> disjointTy (S n))) ()
-- (f : () -> Void) ()
-- Void


-- now we try prove some simple theorems

plusReduces : {n:Nat} -> (Z + n = n)
plusReduces = Refl
-- since 0 + n is n by the definition of (+).

plusReduces' : (n:Nat) -> (n + Z = n)
plusReduces' Z = Refl
plusReduces' (S k) = cong (plusReduces' k)
-- where `cong' is a library function with type (a = b) -> (f a = f b),
-- representing equality respects function application.

-- To finish the hole we had previously for function `parity', we need to prove
-- that (S (S (j + j))) = (S j) + (S j).


parityHelper1 : (j : Nat) -> (S j + S j) = S (S (j + j))
parityHelper1 Z = Refl
parityHelper1 (S j) = rewrite  in ?b
