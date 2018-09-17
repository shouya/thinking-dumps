module Basic where

class Category cat where
  id :: cat a a
  (.) :: cat b c -> cat a b -> cat a c

-- laws:
-- 1. id constraint: forall f, cId `cComp` f = f `cComp` cId = f
-- 2. assoc constraint: (f . g) . h = f . (g . h)


class Functor f where
  fmap :: (a -> b) -> (f a -> f b)

-- law:
-- structure preserving: fmap f . fmap g = fmap (f . g)


type NatTrans f g a = f a -> g a
-- law:
-- commutative square: for all a, b, f: a -> b, fmap_G f . m_a = m_b . fmap_F

-- this is automatically true in Hask category thanks to Haskell's parametric
-- polymorphism.
