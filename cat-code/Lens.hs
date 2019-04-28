{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}

--- See: https://bartoszmilewski.com/2016/09/

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


-- Yoneda Lemma for functor category
--
-- forall f. (Functor f) => (g ~> f) -> h f ~ h g
--
-- where g ~> f is a natural transformation, defined as
--
--   forall x. g x -> f x
--
-- Yonena Embedding for functor category
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


-- Reader Functor on functor category
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


-- Adjunction on functor categories

class (HFunctor l, HFunctor r) => HAdjunction l r | l -> r, r -> l where
  hladj :: forall f g. (Functor f, Functor g) => (l f ~> g) -> (f ~> r g)
  hradj :: forall f g. (Functor f, Functor g) => (f ~> r g) -> (l f ~> g)

-- Substitute h := l1 h, g := l2 g

step1 :: (HAdjunction l1 r1, HAdjunction l2 r2, Functor g, Functor h) =>
  HYoE (l1 h) (l2 g) -> (l2 g ~> l1 h)
step1 = fromHYoE

step1' :: (HAdjunction l1 r1, HAdjunction l2 r2, Functor g, Functor h) =>
  (l2 g ~> l1 h) -> HYoE (l1 h) (l2 g)
step1' = toHYoE

-- Apply adjunction to natural transformations

adjHYoE :: (HAdjunction l1 r1, HAdjunction l2 r2, Functor g, Functor h) =>
  (forall f. (Functor f) => (l1 h ~> f) -> (l2 g ~> f)) ->
  (forall f. (Functor f) => (h ~> r1 f) -> (g ~> r2 f))
adjHYoE y hrf = hladj $ y $ hradj hrf

adjHYoE' :: (HAdjunction l1 r1, HAdjunction l2 r2, Functor g, Functor h) =>
  (forall f. (Functor f) => (h ~> r1 f) -> (g ~> r2 f)) ->
  (forall f. (Functor f) => (l1 h ~> f) -> (l2 g ~> f))
adjHYoE' y lhf = hradj $ y $ hladj lhf

step2 :: (HAdjunction l1 r1, HAdjunction l2 r2, Functor g, Functor h) =>
  (forall f. (Functor f) => (h ~> r1 f) -> (g ~> r2 f)) -> (g ~> r2 (l1 h))
step2 y = hladj $ fromHYoE $ adjHYoE' y

step2' :: (HAdjunction l1 r1, HAdjunction l2 r2, Functor g, Functor h) =>
  (g ~> r2 (l1 h)) -> (forall f. (Functor f) => (h ~> r1 f) -> (g ~> r2 f))
step2' grlh = adjHYoE $ toHYoE $ hradj grlh


-- now back to step 2, let's make:
--
--   h x := b -> x
--   g x := s -> x


step3 :: (HAdjunction l1 r1, HAdjunction l2 r2) =>
  (forall f. (Functor f) => (forall x. (b -> x) -> r1 f x) ->
                            (forall x. (s -> x) -> r2 f x)) ->
  (forall x. (s -> x) -> r2 (l1 ((->) b)) x)
step3 = step2

step3' :: (HAdjunction l1 r1, HAdjunction l2 r2) =>
  (forall x. (s -> x) -> r2 (l1 ((->) b)) x) ->
  (forall f. (Functor f) => (forall x. (b -> x) -> r1 f x) ->
                            (forall x. (s -> x) -> r2 f x))
step3' = step2'


-- Now let's apply yoneda's lemma again
step4 :: (HAdjunction l1 r1, HAdjunction l2 r2) =>
  (forall f. (Functor f) => (r1 f b) ->
                            (r2 f t)) ->
  (r2 (l1 ((->) b)) t)
step4 y = fromYo $ step3 (\bx2fx -> toYo $ y $ fromYo bx2fx)

step4' :: (HAdjunction l1 r1, HAdjunction l2 r2) =>
  (r2 (l1 ((->) b)) t) ->
  (forall f. (Functor f) => (r1 f b) ->
                            (r2 f t))
step4' rlbs rfb = fromYo $ step3' (toYo rlbs) (toYo rfb)

-- Nice and clean!
--
-- Now the problem becomes how we can chose for the two adjunctions.
-- The answer is upstar functor and its left adjunction.


-- Upstar functor, I'll call it RReader here
newtype RReader a f b = RReader { unRR :: a -> f b }

-- Left adjoint to upstar functor, I'll call it RWriter
newtype RWriter a g b = RWriter { unRW :: (a, g b) }

-- They are HFunctors
instance HFunctor (RReader a) where
  hfmap fg (RReader afb) = RReader (fg . afb)      -- wants agb
  ffmap bc (RReader afb) = RReader (fmap bc . afb) -- wants afc

instance HFunctor (RWriter a) where
  hfmap gh (RWriter (a, gb)) = RWriter (a, gh gb)      -- wants (a, h b)
  ffmap bc (RWriter (a, gb)) = RWriter (a, fmap bc gb) -- wants (a, g c)

-- Then they are adjoint functors
instance HAdjunction (RWriter a) (RReader a) where
  hladj :: forall f g. (Functor f, Functor g) => (RWriter a f ~> g) -> (f ~> RReader a g)
  hladj wfx2gx fx = RReader (\a -> wfx2gx (RWriter (a, fx)))

  hradj :: forall f g. (Functor f, Functor g) => (f ~> RReader a g) -> (RWriter a f ~> g)
  hradj fx2rgx (RWriter (a, fx)) = unRR (fx2rgx fx) a

-- let:
--
--  r1 f b := a -> f b  (RReader a f b)
--  r2 f t := s -> f t  (RReader s f t)
--
--  l1 f b := (a, f b)  (RWriter a f b)

step5 :: (forall f. (Functor f) => (RReader a f b) -> (RReader s f t)) ->
         (RReader s (RWriter a ((->) b)) t)
step5 = step4

step5' :: (RReader s (RWriter a ((->) b)) t) ->
          (forall f. (Functor f) => (RReader a f b) -> (RReader s f t))
step5' = step4'


-- We finally gets it!
step6 :: (forall f. (Functor f) => (a -> f b) -> s -> f t) ->
         (s -> (a, b -> t))
step6 afb2sft = sabt $ step5 rrafb2rrsft
  where rrafb2rrsft rrafb = RReader $ afb2sft $ unRR rrafb
        sabt rrsrwabt = \s -> unRW (unRR rrsrwabt s)

step6' :: (s -> (a, b -> t)) ->
          (forall f. (Functor f) => (a -> f b) -> s -> f t)
step6' sabt afb = unRR $ step5' rrsrwabt rrafb
  where rrsrwabt = RReader (\s -> RWriter (sabt s))
        rrafb = RReader afb

-- Bravo! I just proved the two notations to lens are indeed isomorphic!



main = putStrLn "type checks!"


