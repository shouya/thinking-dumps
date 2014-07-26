
data List a = Null | Cons a (List a)

data Null' = Null'                      -- 1
data Cons' a = Cons' (a, List' a)       -- a * L(a)
type List' a = Either Null' (Cons' a)   -- 1 + a * L(a)

---
--- [a] === List a
---

data ListZipper a = LZ a [a] [a]    -- LZ(a) = a * L(a)^2

left :: ListZipper a -> ListZipper a
left (LZ _ [] _) = error "already on the left end"
left (LZ a (x:l) r) = LZ x l (a:r)

right :: ListZipper a -> ListZipper a
right (LZ _ _ []) = error "already on the right end"
right (LZ a l (x:r)) = LZ x (a:l) r
