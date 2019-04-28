{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

-- From Yoneda To Lens
--
-- Yoneda Lemma:
--
-- forall x. (a -> x) -> f x ~ f a
--
-- Yoneda Embedding - i.e. f x = (b -> x):
--
-- forall x. (a -> x) -> (b -> x) ~ (b -> a)


type Yo f a = (Functor f) => forall x. (a -> x) -> f x

-- Proof for Yo f a ~ f a

toYo :: (Functor f) => f a -> Yo f a
toYo fa ax = fmap ax fa

fromYo :: (Functor f) => Yo f a -> f a
fromYo y = y id


-- Yoneda Lemma for Functor category
--
-- forall f. (Functor f) => (g ~> f) -> h f ~ h g
--
-- where g ~> f is a natural transformation, defined as
--
--   forall x. g x -> f x
--
-- Yonena Embedding for Functor category
--
-- forall f. (Functor f) => (g ~> f) -> (h ~> f)  ~  (h ~> g)
--

type f ~> g = forall x. f x -> g x
type h @@ g = (HFunctor h) => forall x. h g x

infixr 1 ~>
infixl 2 @@

class HFunctor h where
  hfmap :: (Functor f, Functor g) => (f ~> g) -> (h f ~> h g)
  ffmap :: (Functor f) => (a -> b) -> (h f a -> h f b)

instance (HFunctor h, Functor f) => Functor (h f) where
  fmap :: (a -> b) -> (h f a -> h f b)
  fmap ab = ffmap ab

type HYo h g = (HFunctor h) => forall f. (g ~> f) -> (h @@ g)


toHYo :: (HFunctor h, Functor g) =>
  (h @@ g) ->
  (forall f. (Functor f) => ((g ~> f) -> h @@ f))
toHYo hg gf = hfmap gf hg

fromHYo :: (HFunctor h, Functor g) =>
  (forall f. (Functor f) => ((g ~> f) -> h @@ f)) ->
  (h @@ g)
fromHYo y = y id


-- Reader Functor in Functor Category
--

data HReader h f x = HReader (h x -> f x)

instance HFunctor (HReader h) where
  hfmap :: (Functor f, Functor g) => (f ~> g) -> (HReader h f ~> HReader h g)
  hfmap fg (HReader hf) = HReader (fg . hf)

  ffmap :: (Functor f) => (a -> b) -> (HReader h f a -> HReader h f b)
  ffmap ab hfa = fmap ab hfa


-- Higher order yoneda embedding
type HYoE h g = forall f. (Functor f) => (h ~> f) -> (g ~> f)


toHYoE :: (Functor h, Functor g) => (g ~> h) -> HYoE h g
toHYoE gh hf = hf . gh

fromHYoE :: (Functor h, Functor g) => HYoE h g -> (g ~> h)
fromHYoE y = y id


-- Now we define adjunction as follows

class (HFunctor l, HFunctor r) => HAdjunction l r where
  adj   :: forall f g. (Functor f, Functor g) => (l f ~> g) -> (f ~> r g)
  coadj :: forall f g. (Functor f, Functor g) => (f ~> r g) -> (l f ~> g)


step1 :: (HAdjunction l1 r1, HAdjunction l2 r2, Functor g, Functor h) =>
  HYoE (l1 h) (l2 g) -> (l2 g ~> l1 h)
step1 = fromHYoE

-- step2 :: (HAdjunction l1 r1, Functor g, Functor h)




main = putStrLn "type checks!"


