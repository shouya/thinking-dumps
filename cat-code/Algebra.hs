{-# LANGUAGE GADTs #-}

module Algebra where

import Prelude (Functor(..), Int, Fractional, IO, return, (+), (-), (*), (/), (.), ($), print, Float, take, fromIntegral, Maybe(..), (>=))

class Group g where
  gid     :: g
  gappend :: g -> g -> g
  ginv    :: g -> g

-- Given a category C, an algebra is a endofunctor F in C with
-- a set of morphisms that map from F C to C. (nat trans?)
type Algebra f a = f a -> a

data GroupAlg a where
  GId     :: GroupAlg a
  GAppend :: a -> a -> GroupAlg a
  GInv    :: a -> GroupAlg a

instance Functor GroupAlg where
  fmap _f GId          = GId
  fmap f (GAppend a b) = GAppend (f a) (f b)
  fmap f (GInv a)      = GInv (f a)

gAlg :: Algebra GroupAlg Int
gAlg GId           = 0
gAlg (GAppend a b) = a + b
gAlg (GInv a)      = -a

gAlg2 :: (Fractional a) => Algebra GroupAlg a
gAlg2 GId           = 1
gAlg2 (GAppend a b) = a * b
gAlg2 (GInv a)      = 1/a

-- A fix point
newtype Fix f = Fix { unFix :: f (Fix f) }
fix :: f (Fix f) -> Fix f
fix = Fix
-- law: fix . unFix = unFix . fix = id

-- By Lambek's theorem, the initial object in the category of algebras on
-- endofunctor F is the isomorphism: Fix F. Using Fix we can handle recursive
-- algebras.

data Expr a = Zero
            | One
            | Add a a

instance Functor Expr where
  fmap _ Zero      = Zero
  fmap _ One       = One
  fmap f (Add a b) = Add (f a) (f b)

exprAlg :: Algebra Expr Int
exprAlg Zero      = 0
exprAlg One       = 1
exprAlg (Add a b) = a + b

deepExprAlg :: Fix Expr -> Int
deepExprAlg = exprAlg . fmap deepExprAlg . unFix

deepExprExample :: Fix Expr
deepExprExample = f $ Add (f One) (f $ Add (f Zero) (f One))
  where f = fix

-- catamorphism
cata :: (Functor f) => Algebra f a -> Fix f -> a
cata alg = alg . fmap (cata alg) . unFix


data List e a = Nil | Cons e a

instance Functor (List e) where
  fmap _  Nil       = Nil
  fmap f (Cons e a) = Cons e (f a)

sumAlg :: Algebra (List Int) Int
sumAlg Nil        = 0
sumAlg (Cons e a) = e + a

sum :: Fix (List Int) -> Int
sum = sumAlg . fmap sum . unFix

listExample :: Fix (List Int)
listExample = f $ Cons 1 (f $ Cons 2 (f $ Cons 3 (f Nil)))
  where f = fix

foldr :: a -> (e -> a -> a) -> Fix (List e) -> a
foldr x0 f = cata foldAlg
  where foldAlg Nil        = x0
        foldAlg (Cons e a) = f e a

sum' :: Fix (List Int) -> Int
sum' = foldr 0 (+)

type Coalgebra f a = a -> f a

ana :: (Functor f) => Coalgebra f a -> a -> Fix f
ana coalg = Fix . fmap (ana coalg) . coalg

data Stream e a = Stream e a

instance Functor (Stream a) where
  fmap f (Stream e a) = Stream e (f a)

-- generate an infinite list of elements starting at n + 0.5, incremented by 1
genStreamCoalg :: Int -> Stream Float Int
genStreamCoalg n = Stream (0.5 + fromIntegral n) (n + 1)

streamToList :: Fix (Stream e) -> [e]
streamToList s = let (Stream e f) = unFix s in e:(streamToList f)

listToHaskellList :: Fix (List e) -> [e]
listToHaskellList s = expand (unFix s)
  where expand Nil        = []
        expand (Cons e f) = e:(listToHaskellList f)

unfoldr :: (a -> Maybe (e, a)) -> a -> Fix (List e)
unfoldr f = ana unfoldrCoalg
  where unfoldrCoalg a = case f a of
          Just (e, a') -> Cons e a'
          Nothing      -> Nil

fibBounded :: Int -> [Int]
fibBounded bound = listToHaskellList $ unfoldr f (0,1)
  where f (a, b) = if b >= bound
                   then Nothing
                   else Just (b, (b, a+b))

          

main :: IO ()
main = do
  print (deepExprAlg deepExprExample)
  print (cata exprAlg deepExprExample)
  print (sum listExample)
  print (sum' listExample)
  print (take 3 $ streamToList $ ana genStreamCoalg 1)
  print (take 100 (fibBounded 30))

-- to make it compiles with simply `ghc <filename>`
