{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}

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
type ToyLens a b = forall f. (Functor f) => (f a -> f b) -> (a -> b)


data F = F Int
data G = G F
data H = H G

data Id a = Id { runId :: a }

instance Functor Id where
  fmap f (Id a) = Id (f a)

-- lensH2G :: ToyLens H G -- (f H -> f G) -> H -> G
-- lensH2G fa2fb = fa2fb Id
--
-- lensG2F :: ToyLens G F
-- lensG2F fa2fb a = runId $ fa2fb $ Id a


main :: IO ()
main = return ()
--  let value = H (G (F 10))
--  in print $ (lensH2G . lensG2F) value


