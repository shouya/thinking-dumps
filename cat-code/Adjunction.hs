{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveFunctor #-}


--
-- Play around with adjunctions and monads
--


-- Functor composition is a functor
newtype FComp f g x = FComp { unFComp :: f (g x) }

instance (Functor f, Functor g) => Functor (FComp f g) where
  fmap f = FComp . (fmap . fmap) f . unFComp


-- We define adjunction as follows
class (Functor l, Functor r) => Adjunction l r where
  ladj :: forall a b. (l a -> b) -> (a -> r b)
  radj :: forall a b. (a -> r b) -> (l a -> b)

  unit   :: forall a. a -> r (l a)
  counit :: forall a. l (r a) -> a

  unit   = ladj id
  counit = radj id
  ladj f = fmap f . unit
  radj f = counit . fmap f


-- An adjunction gives rise to an applicative
instance (Adjunction l r) => Applicative (FComp r l) where
  pure = FComp . unit

  -- (<*>) :: r (l (a -> b)) -> r (l a) -> r (l b)
  rlab <*> rla = FComp rlb
    where rlb = fmap counit $ unFComp $ fmap (\f -> unFComp $ fmap f rla) rlab


-- An adjuction gives rise to a monad
instance (Adjunction l r) => Monad (FComp r l) where
  -- (>>=) :: rl a -> (a -> rl b) -> rl b
  rla >>= arlb = FComp $ fmap counit $ unFComp $ fmap (unFComp . arlb) rla


-- An adjunction gives rise to a comonad
class Comonad w where
  extract :: w a -> a
  duplicate :: w a -> w (w a)

instance (Adjunction l r) => Comonad (FComp l r) where
  extract = counit . unFComp
  duplicate lra = fmap FComp $ FComp $ fmap unit $ unFComp lra


-- Typical example of an adjunction
--
--  (s, -)  -|  (s -> -)
--
instance Adjunction ((,) s) ((->) s) where
  ladj :: ((s, a) -> b) -> (a -> s -> b)
  ladj = flip . curry

  radj :: (a -> s -> b) -> ((s, a) -> b)
  radj = uncurry . flip


-- The adjunction gives rise to State Monad and Store Comonad
data State s a = State { runState :: s -> (s, a) }
  deriving Functor
data Store s a = Store s (s -> a)
  deriving Functor

-- few conversion functions
stateAdj :: State s a -> FComp ((->) s) ((,) s) a
stateAdj (State ssa) = FComp ssa
adjState :: FComp ((->) s) ((,) s) a -> State s a
adjState (FComp ssa) = State ssa

storeAdj :: Store s a -> FComp ((,) s) ((->) s) a
storeAdj (Store s sa) = FComp (s, sa)
adjStore :: FComp ((,) s) ((->) s) a -> Store s a
adjStore (FComp (s, sa)) = Store s sa

-- then we get the monad and comonad for free
instance Applicative (State s) where
  pure = adjState . pure
  f <*> a = adjState (stateAdj f <*> stateAdj a)

instance Monad (State s) where
  a >>= f = adjState (stateAdj a >>= (stateAdj . f))

instance Comonad (Store s) where
  extract = extract . storeAdj
  duplicate = adjStore . fmap adjStore . duplicate . storeAdj


main = putStrLn "type checks!"


