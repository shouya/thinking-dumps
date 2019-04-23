Toy Optics


We start with Yoneda lemma. Yoneda lemma describes the isomorphism between
a natural transformation and an object. We will give the natural transformation here a name.

> type Yo f a = (Functor f) => forall x. (a -> x) -> f x

Then we show Yo f a is isomorphic to f a.

> toYo :: Functor f => f a -> Yo f a
> toYo fa = \atox -> fmap atox fa

> fromYo :: Functor f => Yo f a -> f a
> fromYo y = y id

Yoneda lemma works for all functors, therefore we can pick Reader functor as f.

> type Reader a x = a -> x

We can show that Reader is indeed functorial on x:

> instance Functor (Reader a) where
>   fmap :: (a -> b) -> (z -> a) -> (z -> b)
>   fmap ab za = ab . za

Thus for Reader functor, we have:

  Yo (Reader b) a <-> Reader b a

The proof derives from Yoneda lemma directly:

> readerToYo :: (forall x. ((a -> x) -> (b -> x))) -> (b -> a)
> readerToYo axtobx b = axtobox id b

> readerFromYo :: (b -> a) -> (forall x. (a -> x) -> (b -> x))
> readerFromYo btoa = \atox b -> atox (btoa b)

Since Yoneda lemma works for all categories, and we know functors [C;D] also
form a category, in which functors are natural transformations between these
functor categories.

We first define the notation for natural transformation, which will make our
notation cleaner.

> type f ~> g = forall a. f a -> g a

Then we can state Yoneda Lemma on a higer order:

> type Yo1 g h = (Functor g) => forall f. (h ~> f) -> g f

> toYo1 :: ( g) => g h -> Yo g h
> toYo1 
