
newtype Fix f = Fx (f (Fix f))

cata :: Functor f => (a -> b -> b) -> f a -> b
cata =
