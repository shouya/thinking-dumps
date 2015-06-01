

data ExprF f = Const Int
             | Add f f
             | Mult f f

newtype Fix f = Fx (f (Fix f))
-- Fx :: f (Fix f) -> Fix f

type Expr = Fix ExprF


val :: Fix ExprF
val = Fx (Const 12)


instance Functor ExprF where
-- fmap :: (a -> b) -> ExprF a -> ExprF b
  fmap f (Const i)        = Const i
  fmap f (lhs `Add`  rhs) = (f lhs) `Add`  (f rhs)
  fmap f (lhs `Mult` rhs) = (f lhs) `Mult` (f rhs)

{-
alg :: ExprF Int -> Int
alg (Const i)    = i
alg (x `Add`  y) = x + y
alg (x `Mult` y) = x * y
-}

{-
An F-algebra consists of:

1. an endofunctor F in a category C,
2. an object A in that category, and
3. a morphism from F(A) to A. (i.e. must be able to take values out)
-}

-- Actually there has to be (Functor f) constraint
type Algebra f a = f a -> a

-- So an F-algebra is a functor f, a carrier type a, and a function
-- f a -> a

type SimpleA = Algebra ExprF Int

-- alg :: SimpleA
-- alg (Const i)    = i
-- alg (x `Add`  y) = x + y
-- alg (x `Mult` y) = x * y



type ExprInitAlg = Algebra ExprF (Fix ExprF)


-- Fx :: f (Fix f) -> Fix f
ex_init_alg :: ExprF (Fix ExprF) -> Fix ExprF
ex_init_alg = Fx


-- alg :: f a -> a
-- g :: Fix f -> a
-- fmap g :: f (Fix f) -> f a
-- Fx (f (Fix f)) :: Fix f
--
-- ![Please Refer to this diagram](https://www.fpcomplete.com/content-proxy?src=http%3A%2F%2Fbartosz.com%2Fimages%2FAlgebras%2FHomomorphism.png)


-- the inverse of Fx :: f (Fix f) -> Fix f
unFx :: Fix f -> f (Fix f)
unFx (Fx x) = x

-- What we are finding is a function g with type:
-- g :: Fix f -> a

-- It can be defined by:
-- g = alg . fmap g . unFx
-- where alg has type f a -> a is the algebra

-- if we let g takes an algebra as argument, it would become a
-- catamorphism
cata :: (Functor f) => (f a -> a) -> Fix f -> a
cata alg = alg . fmap (cata alg) . unFx
-- A catamorphism takes an algebra, and returns its evaluation
-- function of an arbitrary nested data

eval :: Fix ExprF -> Int
-- f = ExprF, a = Int
-- So we need an algebra of type: ExprF Int -> Int
-- Which we have already defined! the SimpleA algebra!
eval = cata alg
  where alg (Const i)    = i
        alg (x `Add`  y) = x + y
        alg (x `Mult` y) = x * y
-- OR as expanded: eval = alg . fmap eval . unFx

-- Let's analyze it: First, unFx allows us to peek at the top level of
-- the input expression: It's either a leaf Const i or an Add or Muli
-- whose children are, again, full-blown expression, albeit one degree
-- shallower.
-- remember, fmap eval :: f (Fix ExprF) -> f a


{- !!! WRONG !!!
data ListF l a = Nil | Cons a l

instance Functor (ListF l) where
  fmap f Nil        = Nil
  fmap f (Cons a l) = Cons (f a) l
-}

-- Above definition is WRONG and is a misunderstanding made by
-- myself. In fact, one should notice that the functor property of the
-- ListF is not on how to transform carrier type but how to traverse
-- the ListF, therefore it should be defined on type `l` rather than
-- `a`.

data ListF a l = Nil | Cons a l

instance Functor (ListF a) where
  fmap f Nil        = Nil
  -- fmap :: (l -> k) -> (ListF a l) -> (ListF a k)
  fmap f (Cons a l) = Cons a (f l)

type List a = Fix (ListF a)

myFoldr :: (a -> b -> b) -> b -> Fix (ListF a) -> b
-- List a == Fix (ListF a)
-- Fix m -> b is `g`'s type
myFoldr f b0 = alg . fmap (myFoldr f b0) . unFx
  where -- alg :: ListF a b -> b
    alg Nil        = b0
    alg (Cons a b) = f a b


-- we define some helper functions for conversion between ListF lists
-- and haskell built-in lists
hsToLst :: [a] -> List a
hsToLst []     = Fx Nil
hsToLst (x:xs) = Fx (Cons x (hsToLst xs))

lstToHs :: List a -> [a]
lstToHs (Fx Nil)         = []
lstToHs (Fx (Cons x xs)) = x : lstToHs xs

myFoldrHs :: (a -> b -> b) -> b -> [a] -> b
myFoldrHs f b0 = myFoldr f b0 . hsToLst


main :: IO ()
main = do
  print $ myFoldrHs (+) (0 :: Int) [1,2,3]
  -- It prints 6, it works!
