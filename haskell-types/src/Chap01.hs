{-# LANGUAGE RankNTypes #-}
module Chap01 where

-- chapter 1: The Algebra Behind Types

-- Excercise 1.2-i
-- Q: Determine the cardinality of Either Bool (Bool, Maybe Bool) -> Bool.
-- A: 2 ^ (2 + (2 * (1 + 2))) = 256

-- Ex 1.4-i
-- Q: Use Curry–Howard to prove the exponent law that a^b × a^c = a^(b+c) .
-- That is, provide a function of the type
-- (b -> a) -> 16 (c -> -- a) -> Either b c -> a
-- and one of (Either b c -> a) -> (b -> a, c -> a).
--
type Ex14i_Left = forall a b c. (b -> a, c -> a)
type Ex14i_Right = forall a b c. Either b c -> a
ex14i_from :: Ex14i_Left -> Ex14i_Right
ex14i_from (ba, _ca) (Left b) = ba b
ex14i_from (_ba, ca) (Right c) = ca c

ex14i_to :: Ex14i_Right -> Ex14i_Left
ex14i_to ebca = (bc, ca)
  where bc b = ebca (Left b)
        ca c = ebca (Right c)

-- Ex 1.4-ii Prove (a*b)^c = a^c*b^c
type Ex14ii_Left = forall a b c. c -> (a, b)
type Ex14ii_Right = forall a b c. (c->a, c->b)
ex14ii_from :: Ex14ii_Left -> Ex14ii_Right
ex14ii_from cab = (ca, cb)
  where ca = fst . cab
        cb = snd . cab

ex14ii_to :: Ex14ii_Right -> Ex14ii_Left
ex14ii_to (ca, cb) c = (ca c, cb c)

-- Ex 1.4-iii Prove (a^b)^c = a^(b*c)
ex14iii_from :: (c -> b -> a) -> (c, b) -> a
ex14iii_from = uncurry
ex14iii_to :: ((c, b) -> a) -> (c -> b -> a)
ex14iii_to = curry
