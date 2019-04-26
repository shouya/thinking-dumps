{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}

module ToyOptics where

type Yo f a = Functor f => forall x. (a -> x) -> f x

toYo :: Functor f => f a -> Yo f a
toYo fa = \atox -> fmap atox fa

fromYo :: Functor f => Yo f a -> f a
fromYo y = y id

type Reader a x = a -> x

readerToYo :: (b -> a) -> (forall x. (a -> x) -> (b -> x))
readerToYo = toYo

readerFromYo :: (forall x. (a -> x) -> (b -> x)) -> (b -> a)
readerFromYo = fromYo


type f ~> g = forall x. f x -> g x

type HReader g f = g ~> f

readerToHYo :: (h ~> g) -> forall f. (g ~> f) -> (h ~> f)
readerToHYo hxtogx gxtofx = \hx -> gxtofx (hxtogx hx)

readerFromHYo :: (forall f. (g ~> f) -> (h ~> f)) -> (h ~> g)
readerFromHYo y = y id

readerFromHYoExpanded ::
  (forall f. (forall x. g x -> f x) -> (forall x. h x -> f x)) ->
  (forall x. h x -> g x)
readerFromHYoExpanded y = y id

-- let g = Reader a
-- let h = Reader b

readerFromHYoExpanded' ::
  (forall f. (forall x. (a -> x) -> f x) -> (forall x. (b -> x) -> f x)) ->
  (forall x. ((b -> x) -> (a -> x)))
readerFromHYoExpanded' y = y id

readerFromHYoExpanded'' :: (forall f. (f a -> f b)) -> (a -> b)
readerFromHYoExpanded'' y = y id

readerToHYoExpanded'' :: (a -> b) -> (forall f. (Functor f) => (f a -> f b))
readerToHYoExpanded'' ab = fmap ab

-- Here we get our toy lens
type ToyLens a b = forall f. (Functor f) => (f a -> f b)

-- ToyLens a b ~ (a -> b)


data F = F Int
data G = G F
data H = H G

h2g :: ToyLens H G -- (f H -> f G)
h2g fh = fmap (\(H g) -> g) fh

g2f :: ToyLens G F
g2f fg = fmap (\(G f) -> f) fg

f2i :: ToyLens F Int
f2i ff = fmap (\(F i) -> i) ff

newtype Id a = Id { runId :: a }
  deriving Functor

view :: ToyLens a b -> a -> b
view fa2fb a = runId $ fa2fb (Id a)


main :: IO ()
main = do
  let value = H (G (F 10))

  print $ view (f2i.g2f.h2g) value
  putStrLn "type checks!"



