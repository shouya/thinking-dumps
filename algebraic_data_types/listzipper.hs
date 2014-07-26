
data List a = Null | Cons a (List a)

data Null' = Null'                      -- 1
data Cons' a = Cons' (a, List' a)       -- a * L(a)
type List' a = Either Null' (Cons' a)   -- 1 + a * L(a)

---
--- [a] === List a
---

data ListZipper a = LZ a [a] [a]    -- LZ(a) = a * L(a)^2

left :: ListZipper a -> ListZipper a
left (LZ a l r) = LZ (head l) (tail l) (a:r)

right :: ListZipper a -> ListZipper a
right (LZ a l r) = LZ (head r) (a:l) (tail r)
