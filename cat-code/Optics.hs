{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}

-- Based on "Profunctor Optics" by Matthew Pickering, Jeremy Gibbons, and
-- Nicolas Wu
-- First we have lens. A lens is a device that allows us to view and update a
-- product type.
data Lens a b s t = Lens { view :: s -> a, update :: (b, s) -> t }

pi_1 :: Lens a b (a, c) (b, c)
pi_1 = Lens view' update'
  where view' (a, _c) = a
        update' (b, (_a, c)) = (b, c)

-- A prism is the dual of a lens in the sense of reversing the arrows.
data Prism a b s t = Prism { build :: b -> t, match :: s -> Either t a }

the :: Prism a b (Maybe a) (Maybe b)
the = Prism build' match'
  where build' b = Just b
        match' (Just a) = Right a
        match' Nothing  = Left Nothing

-- a common specialization of lens and prism is an adapter (Iso)
data Adapter a b s t = Adapter { from :: s -> a, to :: b -> t }

flatten :: Adapter (a, b, c) (a', b', c') (a, (b, c)) (a', (b', c'))
flatten = Adapter from' to'
  where from' (a, (b, c)) = (a, b, c)
        to' (a', b', c') = (a', (b', c'))

adapterToLens :: Adapter a b s t -> Lens a b s t
adapterToLens Adapter { from, to } = Lens view' update'
  where view' = from
        update' (b, _s) = to b

adapterToPrism :: Adapter a b s t -> Prism a b s t
adapterToPrism Adapter { from, to } = Prism build' match'
  where build' = to
        match' s = Right (from s)

-- a common generalization of lens and prism is a traversal
-- Note that here contents :: s -> a^n and fill :: (s, b^n) -> t
data Traversal a b s t = Traversal { contents :: s -> [a], fill :: (s, [b]) -> t }

-- a tree traversing pair is a traversal
data Tree a = Empty | Node (Tree a) a (Tree a)

treeTraversal :: Traversal a b (Tree a) (Tree b)
treeTraversal = Traversal contents' fill'
  where contents' Empty = []
        contents' (Node l x r) = contents' l ++ [x] ++ contents' r
        fill' (Empty, []) = Empty
        -- we should not need to handle this because by definition, the length
        -- of [b] should match the size of the structure (Tree a). However,
        -- because of our implementation here we have to allow non-empty list.
        fill' (Empty,_) = Empty
        fill' ((Node l _x r), vs) = Node l' x' r'
          where l' = fill' (l, vs)
                x' = vs !! l_len
                r' = fill' (r, (drop (l_len + 1) vs))
                l_len = length (contents' l)

-- To capture the idea of the common `n`, we use this datatype proposed by
-- van Laarhoven.
-- Note that Traversal is equivalent to s -> (a^n, b^n -> t).
data FunList a b t = Done t | More a (FunList a b (b -> t))

-- we can verify inductively that (FunList a b t) is isomorphic to
-- Either t (a, (FunList a b (b -> t)).
-- When n = 0, FunList a b t  ~ Left t ~ ((), () -> t)
-- Given FunList a b t        ~ Right (a^n,     b^n -> t),
--  (a, FunList a b (b -> t)) ~ Right (a^(n+1), b^(n+1) -> t)











-- main = putStrLn "type checks!"
