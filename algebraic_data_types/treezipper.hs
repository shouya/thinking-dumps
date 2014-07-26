

data Tree a = Empty | Node a (Tree a) (Tree a)

data Empty' = Empty'                    -- 1
data Node' a = Node' (a, Tree' a, Tree' a)    -- a * T(a) * T(a)
type Tree' a = Either Empty' (Node' a)  -- 1 + a * T(a) * T(a)

{-

-}
