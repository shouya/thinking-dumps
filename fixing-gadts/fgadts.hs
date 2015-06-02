{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}
{-# LANGUAGE DeriveFunctor        #-}

import Control.Arrow ((&&&),first)
import Data.Function (on)
import Data.Maybe (isJust, fromJust)
import Data.Monoid
import Text.PrettyPrint.Leijen hiding ((<>))

-- I have read this article and will try reproduce the code described
-- in the article all from my understanding

{-
data Expr1 :: (* -> *) where
  Const  :: Int        -> Expr1 Int
  Add    :: Expr1 Int  -> Expr1 Int -> Expr1 Int
  Mult   :: Expr1 Int  -> Expr1 Int -> Expr1 Int
  IsZero :: Expr1 Int  -> Expr1 Bool
  If     :: Expr1 Bool -> Expr1 a -> Expr1 a -> Expr1 a
-}

data ExprF :: (* -> *) -> * -> * where
  Const  :: Int                  -> ExprF r Int
  Add    :: r Int  -> r Int      -> ExprF r Int
  Mult   :: r Int  -> r Int      -> ExprF r Int
  IsZero :: r Int                -> ExprF r Bool
  If     :: r Bool -> r a -> r a -> ExprF r a


-- data Fix :: (* -> *) -> *
-- data Fix f = Fx { unFx :: f (Fix f) -> Fix f }

data HFix :: ((* -> *) -> * -> *) -> * -> * where
  HFx :: f (HFix f) a -> HFix f a

unHFx :: HFix f a -> f (HFix f) a
unHFx (HFx a) = a


class HFunctor (h :: (* -> *) -> * -> *) where
  hfmap :: (forall a . f a -> g a) -> (forall a . h f a -> h f b)

type f :~> g = (forall a . f a -> g a)


instance HFunctor ExprF where
  hfmap h (Const i)  = Const i
  hfmap h (Add a b)  = Add    (h a) (h b)
  hfmap h (Mult a b) = Mult   (h a) (h b)
  hfmap h (IsZero a) = IsZero (h a)
  hfmap h (If a b c) = If     (h a) (h b) (h c)


hcata :: (h f a -> f a) -> HFix h a -> f a
hcata alg = alg . hfmap (hcata alg) . unHFx

newtype I x = I { unI :: x }


-- f = I, h = ExprF
-- alg :: ExprF I a -> I a
eval :: HFix ExprF a -> a
eval = unI . hcata alg
  where alg (Const i) = I i
        alg (Add a b) = I $ unI a + unI b
        alg (Mult a b) = I $ unI a + unI b
        alg (IsZero a) = I $ unI a == 0
        alg (If a b c) = if (unI a)
                         then b
                         else c

type Expr = HFix ExprF
-- copied from the article, slightly modified
x :: Expr Bool
x = HFx (IsZero (HFx (Add (HFx (Add (HFx (Const 1)) (HFx (Const 2))))
                      (HFx (Const (-3))))))
y :: Expr Int
y = HFx (If x (HFx (Const 1)) (HFx (Const 2)))
