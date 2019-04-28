{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

--
-- Play around with adjunctions and monads
--

class (Functor l, Functor r) => Adjunction l r where
  ladj :: forall a b. (l a -> b) -> (a -> r b)
  radj :: forall a b. (a -> r b) -> (l a -> b)

  unit   :: forall a. a -> r (l a)
  counit :: forall a. l (r a) -> a

  unit   = ladj id
  counit = radj id
  ladj f = fmap f . unit
  radj f = counit . fmap f


newtype FComp f g x = FComp { unFComp :: f (g x) }

instance (Functor f, Functor g) => Functor (FComp f g) where
  fmap f = FComp . (fmap . fmap) f . unFComp

instance (Adjunction l r) => Applicative (FComp r l) where
  pure = FComp . unit

  -- (<*>) :: r (l (a -> b)) -> r (l a) -> r (l b)
  rlab <*> rla = FComp rlb
    where rlb = fmap counit $ unFComp $ fmap (\f -> unFComp $ fmap f rla) rlab


instance (Adjunction l r) => Monad (FComp r l) where
  -- (>>=) :: rl a -> (a -> rl b) -> rl b
  rla >>= arlb = FComp $ fmap counit $ unFComp $ fmap (unFComp . arlb) rla


main = putStrLn "type checks!"


