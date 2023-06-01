{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Arrows #-}

import Control.Category
import Control.Arrow
import Data.Function ((&))

import Prelude hiding (id, (.))

-- Exercise 1: Write Arrow instances for the following types
newtype Reader s i o = R ((s,i) -> o)
newtype Writer i o = W (i -> (String, o))

--- Solution:
instance Category (Reader s) where
  id :: Reader s i i
  id = R $ \(_s,i) -> i

  (.) :: Reader s b c -> Reader s a b -> Reader s a c
  (.) (R f) (R g) = R $ \(s,a) -> f (s, g (s,a))

instance Arrow (Reader s) where
  arr :: (i -> o) -> Reader s i o
  arr f = R $ \(_s,i) -> f i

  first :: Reader s i o -> Reader s (i, b) (o, b)
  first (R f) = R $ \(s,(i,b)) -> (f (s,i), b)

instance Category Writer where
  id :: Writer i i
  id = W $ \i -> ("", i)

  (.) :: Writer b c -> Writer a b -> Writer a c
  (.) (W f) (W g) = W $ \a -> let (s1, b) = g a
                                  (s2, c) = f b
                              in (s1 ++ s2, c)

instance Arrow Writer where
  arr :: (i -> o) -> Writer i o
  arr f = W $ \i -> ("", f i)

  first :: Writer i o -> Writer (i, b) (o, b)
  first (W f) = W $ \(i,b) -> let (s, o) = f i
                              in (s, (o, b))

-- Exercise 2: The following is almost an arrow type, what goes wrong?
newtype ListMap i o = LM ([i] -> [o])

-- Solution: we just try it!
instance Category ListMap where
  id :: ListMap i i
  id = LM id

  (.) :: ListMap b c -> ListMap a b -> ListMap a c
  (.) (LM f) (LM g) = LM $ f . g

instance Arrow ListMap where
  arr :: (i -> o) -> ListMap i o
  arr f = LM $ map f

  first :: ListMap i o -> ListMap (i, b) (o, b)
  first (LM f) = LM $ \xs ->
    let (is, os) = unzip xs
    --- note: there is no guarantee that `length (f is) == length is`.
    --- so the zip is not working. this is the problem.
    in zip (f is) os

-- Exercise 3: Define the following as an arrow type
data Stream a = Cons a (Stream a) deriving Functor
newtype StreamMap i o = SM (Stream i -> Stream o)

-- Solution:
runSM :: StreamMap i o -> Stream i -> Stream o
runSM (SM f) = f

instance Category StreamMap where
  id :: StreamMap i i
  id = SM id

  (.) :: StreamMap b c -> StreamMap a b -> StreamMap a c
  (.) (SM f) (SM g) = SM $ f . g

instance Arrow StreamMap where
  arr :: (i -> o) -> StreamMap i o
  arr f = SM $ fmap f

  first :: StreamMap i o -> StreamMap (i, b) (o, b)
  first (SM f) = SM $ lift f
    where
      lift :: (Stream i -> Stream o) -> Stream (i, b) -> Stream (o, b)
      lift f s = zipStream (f (runSM (arr fst) s)) ((runSM (arr snd) s))

      zipStream :: Stream a -> Stream b -> Stream (a, b)
      zipStream (Cons a as) (Cons b bs) = Cons (a, b) (zipStream as bs)

-- Exercise 4: Show that the following is a functor:
zipRf :: (Arrow y) => y a b -> (c -> c') -> y (a, c) (b, c')
zipRf f g = first f >>> (id *** arr g)

-- Solution:

{-
-- We first show zipRf preserves id by showing that
-- zipRf f id = first f

zipRf f id = first f >>> (id *** arr id)
           = first f >>> (id *** id)
           = first f >>> id
           = first f

-- We then show zipRf preserves composition by showing that
-- zipRf f (g >>> g') = zipRf f g >>> zipRf f g'

zipRf f g >>> zipRf f g' = first f >>> (id *** arr g) >>>
                           first f >>> (id *** arr g')

zipRf f (g >>> g') = first f >>> (id *** arr (g >>> g'))
                   = first f >>> (first id >>> second (arr (g >>> g'))
                   = first f >>> first id >>> second (arr g >>> arr g')
                   = first f >>> first id >>> second (arr g) >>> second (arr g')
                   = first f >>> (first id >>> second (arr g)) >>> second (arr g')
                   = first f >>> (id *** arr g) >>> second (arr g')
                   = zipRf f g >>> second (arr g')


Now we must prove zipRf f g' = second (arr g').

zipRf f g' = first f >>> (id *** arr g')
           = first f >>> (first id >>> second (arr g'))
           = first f >>> first id >>> second (arr g')
           = first (f >>> id) >>> second (arr g')
           = first f >>> second (arr g')

So no. this function is not a functor.

There is an extra `first f` in `zipRf f g >>> zipRf f g'`
comparing to `zipRf f (g >>> g')`.

Let me find a counter example to show it is not a functor.
-}

ex4CounterExample :: IO ()
ex4CounterExample = let f = arr (+1) :: Int -> Int
                        g = (+2)
                        g' = (+3)
                        lhs = zipRf f (g >>> g')
                        rhs = zipRf f g >>> zipRf f g'
                    in do
  print (lhs (10,10))
  print (rhs (10,10))

-- prints: (11,15) and (12,15)
-- so zipRf f (g >>> g') /= zipRf f g >>> zipRf f g'


-- implementing curryA and uncurryA

curryA :: Arrow y => y (a, b) c -> a -> y b c
curryA f a = mkPair a >>> f

mkPair :: (Arrow y) => a -> y b (a, b)
mkPair a = arr $ \b -> (a, b)

uncurryA :: forall y a b c. ArrowApply y => (a -> y b c) -> y (a, b) c
uncurryA f = (arr (\(a, b) -> (f a :: y b c, b :: b)) :: y (a, b) (y b c, b))
             >>> app

-- implementing the arrows: State, NonDet, MapTrans and Auto

-- State
newtype State s i o = State ((s, i) -> (s, o))
instance Category (State s) where
  id :: State s a a
  id = State id

  (.) :: State s b c -> State s a b -> State s a c
  (State g) . (State f) = State (g . f)

assoc :: (a, (b, c)) -> ((a, b), c)
assoc (a, (b, c)) = ((a, b), c)

unassoc :: ((a, b), c) -> (a, (b, c))
unassoc ((a, b), c) = (a, (b, c))

swap :: (a,b) -> (b,a)
swap (a,b) = (b,a)

instance Arrow (State s) where
  arr :: (i -> o) -> State s i o
  arr f = State $ fmap f

  first :: State s i o -> State s (i, d) (o, d)
  first (State f) = State $ unassoc . swap . fmap f . swap . assoc

-- NonDet
newtype NonDet i o = NonDet (i -> [o])

instance Category NonDet where
  id :: NonDet a a
  id = NonDet (\x -> [x])

  (.) :: NonDet b c -> NonDet a b -> NonDet a c
  (NonDet g) . (NonDet f) = NonDet $ concat . fmap g . f

instance Arrow NonDet where
  arr :: (i -> o) -> NonDet i o
  arr f = NonDet $ (\x -> [x]) . f

  first :: NonDet i o -> NonDet (i, d) (o, d)
  first (NonDet f) = NonDet $ \(i,d) -> map (,d) (f i)

-- MapTrans
newtype MapTrans s i o = MapTrans ((s -> i) -> (s -> o))

instance Category (MapTrans s) where
  id = MapTrans id

  (.) :: MapTrans s b c -> MapTrans s a b -> MapTrans s a c
  (MapTrans g) . (MapTrans f) = MapTrans $ g . f

instance Arrow (MapTrans s) where
  arr :: (i -> o) -> MapTrans s i o
  arr f = MapTrans $ fmap f

  first :: MapTrans s i o -> MapTrans s (i,d) (o,d)
  first (MapTrans f) = MapTrans $ zip . (f *** id) . unzip
    where unzip :: (s -> (i,d)) -> (s -> i, s -> d)
          unzip f = (fst . f, snd . f)

          zip :: (s -> o, s -> d) -> (s -> (o,d))
          zip (f, g) s = (f s, g s)

-- Auto
newtype Auto i o = Auto (i -> (o, Auto i o))

runAuto :: Auto i o -> [i] -> [o]
runAuto _ [] = []
runAuto (Auto f) (x:xs) = let (o, g) = f x in o : runAuto g xs

instance Category Auto where
  id = Auto $ \i -> (i, id)

  (.) :: Auto b c -> Auto a b -> Auto a c
  (Auto g) . (Auto f) = Auto $ \a -> let (b, ab) = f a
                                         (c, bc) = g b
                                     in (c, bc . ab)

instance Arrow Auto where
  arr :: (i -> o) -> Auto i o
  arr f = Auto $ \i -> (f i, arr f)

  first :: Auto i o -> Auto (i, d) (o, d)
  first (Auto f) = Auto $ \(i,d) -> let (o, io) = f i
                                    in ((o,d), first io)

-- Exercise 5: verify the ArrowApply axioms for pure functions
-- Solution:
--
-- composition:
{-
arr ((>>> h) *** id) >>> app = ((>>> h) *** id) >>> app
                             = app . ((h.) *** id)
                             = app . (\(f,a) -> ((h.f), a))
                             = (\(f,a) -> (h.f) a)
                             = (\(f,a) -> h (f a))

app >>> h                    = h . app
                             = h . (\(f,a) -> f a)
                             = (\(f,a) -> h (f a)

-}

-- reduction:
{-
arr (mkPair *** id) >>> app = (mkPair *** id) >>> app
                            = (\(a,b) -> (mkPair a, b)) >>> app
                            = (\(a,b) -> (\c -> (a,c), b)) >>> app
                            = (\(a,b) -> (a,b))
                            = id
                            = pure id
-}

-- extensionality:
{-
mkPair f >>> app = (\a -> (f, a)) >>> app
                 = (\a -> f a)
                 = f
-}


-- Exercise 6: The following instance has the correct type but fails at extensionality axiom. Show it.
{-
instance ArrowApply Auto where
  app = arr (\(Auto f, x) -> fst (f x))
-}

-- Solution:
{-
mkPair f >>> app = arr (\c -> (f, c)) >>> app
                 = arr (\c -> (f, c)) >>> arr (\(Auto g, x) -> fst (g x))
                 = arr ((\(Auto g, x) -> fst (g x) . (\c -> (f, c)))
                 = arr (\c -> let (Auto g, x) = (f, c) in fst (g x))
                 = arr (\c -> let Auto g = f in fst (g c))

Let Auto g = f.

mkPair f >>> app = arr (\c -> fst (g c))
                 = arr (fst . g)

How to show this thing does not equal to f?
-}

-- Implementation of ArrowApply on State and NonDet

instance ArrowApply (State s) where
  app :: State s (State s i o, i) o
  app = State $ \(s, (State f, i)) -> f (s, i)


instance ArrowApply NonDet where
  app :: NonDet (NonDet i o, i) o
  app = NonDet $ \(NonDet f, i) -> f i

-- Exercise 7: Implement the ArrowChoice instance for NonDet, State, and StreamMap
-- Solution:

-- recall
-- either :: (a -> c) -> (b -> c) -> Either a b -> c
singleton :: a -> [a]
singleton x = [x]

instance ArrowChoice NonDet where
  left :: NonDet i o -> NonDet (Either i d) (Either o d)
  left (NonDet f) = NonDet $ either (fmap Left . f) (pure . Right)

instance ArrowChoice (State s) where
  left :: State s i o -> State s (Either i d) (Either o d)
  left (State f) = State $ \(s,iOd) -> case iOd of
    Left i  -> fmap Left $ f (s,i)
    Right d -> (s, Right d)

interleaveS :: Stream a -> Stream a -> Stream a
interleaveS (Cons a as) ~(Cons b bs) = Cons a $ Cons b $ interleaveS as bs

repeatS :: a -> Stream a
repeatS a = Cons a (repeatS a)

takeS :: Int -> Stream a -> [a]
takeS 0 _ = []
takeS n (Cons a as) = a : takeS (n-1) as

instance ArrowChoice StreamMap where
  -- newtype StreamMap i o = SM (Stream i -> Stream o)
  -- this is the first idea that came to me...
  {-
  left :: forall i o d. StreamMap i o -> StreamMap (Either i d) (Either o d)
  left (SM f) = SM lf
    where lf :: Stream (Either i d) -> Stream (Either o d)
          lf s = let ~(is, ds) = unzipEither s
                 in interleaveS (fmap Left $ f is) (fmap Right ds)

          unzipEither :: Stream (Either i d) -> (Stream i, Stream d)
          unzipEither ~(Cons x s)  = let ~(is, ds) = unzipEither s
                                     in case x of
                                          Left i  -> (Cons i is, ds)
                                          Right d -> (is, Cons d ds)
  -}
  -- it would stuck when the input is made of only left.

  -- this one seems also legit
  {-
  left :: forall i o d. StreamMap i o -> StreamMap (Either i d) (Either o d)
  left (SM f) = SM lf
    where lf :: Stream (Either i d) -> Stream (Either o d)
          lf (Cons (Left i)  s) = interleaveS (f (repeatS i)) (lf s)
          lf (Cons (Right d) s) = Cons (Right d) (lf s)
  -}
  -- because of the interleaving, it doesn't pass the extension law either.
  -- Note: you need a stream of non-homogeneous elements to see the difference,
  -- e.g. from 1

  -- there is an alternative sensible implementation

  left :: forall i o d. StreamMap i o -> StreamMap (Either i d) (Either o d)
  left (SM f) = SM lf
    where lf :: Stream (Either i d) -> Stream (Either o d)
          lf (Cons (Left i)  s) = Cons (Left $ headS $ f (repeatS i)) (lf s)
          lf (Cons (Right d) s) = Cons (Right d) (lf s)

          headS (Cons x _) = x
  -- this one passes the extension law (because the law only concern
  -- linear mapping), it doesn't pass the unit law `arr Left >>> left f = f >>> pure Left` if f considers multiple elements in its input at once.

  {-
  By implementing these instances, I realize there are several places where a choice can be made:

  - first, what should be the input of f
    + we can feed it (repeat currElem)
    + we can feed it all Left elements
  - second, what to do with f's output
    + we can only take the first element and discard the rest
    + we can interleave it with the rest of mapping. but how to interleave is another aspect of consideration.
  -}

  {-
  Overall, I have yet to find one implementation that satisfies all
  laws. I'm not even sure if such implementation is possible.
  -}


{-
Here are some code I used to verify the law breaking. They're useless now but I
keep them here for future reference.

plus :: (a -> a') -> (b -> b') -> Either a b -> Either a' b'
plus f _ (Left a)  = Left (f a)
plus _ g (Right b) = Right (g b)

from :: Int -> Stream Int
from i = Cons i (from (i+1))

main :: IO ()
main = do
  print $ (takeS 10 $ runSM rhs s :: [Either Int Int])
  print $ (takeS 10 $ runSM lhs s :: [Either Int Int])
    where lhs = arr Left >>> left y
          rhs = y >>> arr Left
          f = (+2)
          s = from (1 :: Int)

          y :: StreamMap Int Int
          y = SM $ \s -> case s of
            (Cons 1 (Cons 2 x)) -> Cons 2 (Cons 1 x)
            x -> x
          y2 :: StreamMap Int Int
          y2 = SM $ \s -> case s of
            (Cons 3 (Cons 4 x)) -> Cons 1 (Cons 2 x)
            x -> x
-}

--- ArrowChoice instance for Auto
instance ArrowChoice Auto where
  -- newtype Auto i o = Auto (i -> (o, Auto i o))
  left :: forall i o d. Auto i o -> Auto (Either i d) (Either o d)
  left (Auto f) = Auto lf
    where lf :: Either i d -> (Either o d, Auto (Either i d) (Either o d))
          lf (Left i)  = let (o, g) = f i in (Left o, left g)
          lf (Right d) = (Right d, left (Auto f))

-- Exercise 8: show the equation fails for Auto and StreamMap:
-- (f ||| g) >>> h = (f >>> h) ||| (g >>> h)

-- Solution:
-- I don't have a working ArrowChoice implementation for StreamMap, so
-- I'll only show it for Auto.

ex8CounterExample :: IO ()
ex8CounterExample = do
  let f = id
      g = id
      h = Auto (\x -> (x+1, id))

  let lhs = (f ||| g) >>> h
  let rhs = (f >>> h) ||| (g >>> h)

  let input = [Left 1, Right 1]

  print (take 10 $ runAuto lhs input)
  print (take 10 $ runAuto rhs input)
  -- prints [2,2] vs [2,3]

  -- the reason it fails is because h runs twice in the RHS, but only
  -- once in the first.

-- Exercise 9: Given the following definition
newtype Exp y i o = Exp (y i (Either String o))
-- define the Arrow instance

-- Solution:
instance ArrowChoice y => Category (Exp y) where
  id = Exp $ id >>^ Right
  (Exp g) . (Exp f) = Exp $ f >>> right g >>^ collapse
    where
          collapse (Left x)          = Left  x
          collapse (Right (Left  x)) = Left  x
          collapse (Right (Right x)) = Right x

distr :: (Either a b, c) -> Either (a,c) (b,c)
distr (Left a,  c) = Left  (a, c)
distr (Right b, c) = Right (b, c)

instance ArrowChoice y => Arrow (Exp y) where
  arr :: (i -> o) -> Exp y i o
  arr f = Exp $ arr f >>^ Right

  first :: Exp y i o -> Exp y (i,d) (o,d)
  first (Exp f) = Exp $ first f >>^ distr >>> left (arr fst)
    where rearrange (Left e,  d) = Left  e
          rearrange (Right o, d) = Right (o, d)

-- Exercise 10: prove the functor axiom for `first`
-- Solution:

-- We need to show that
-- first (f >>> g) = first f >>> first g
-- Given distribution axiom:
-- first (left f) >>> arr distr = arr distr >>> left (first f)

{-
LHS = first (f >>> g)
    = Exp $ first (f >>> g) >>^ distr >>> left (arr fst)
    = Exp $ first f >>> first g >>^ distr >>> left (arr fst)
    = ???
RHS = first f >>> first g
    = Exp $ first f >>> right (first g) >>^ collapse
    = ???
-}

trace :: ((b,d) -> (c,d)) -> (b -> c)
trace f b = let (c, d) = f (b, d) in c

fix :: (a -> a) -> a
fix f = f (fix f)

-- ArrowLoop instances for State, MapTrans, Auto, StreamMap
instance ArrowLoop (State s) where
  -- recall that type State s i o = (s, i) -> (s, o)
  loop :: State s (i,d) (o,d) -> State s i o
  loop (State f) = State $ trace (assoc . f . unassoc)

zipMap :: (a -> b, a -> c) -> a -> (b, c)
zipMap (f, g) a = (f a, g a)

unzipMap :: (a -> (b, c)) -> (a -> b, a -> c)
unzipMap f = (fst . f, snd . f)

instance ArrowLoop (MapTrans s) where
  -- recall that type MapTrans i o = (s -> i) -> (s -> o)
  loop :: MapTrans s (i,d) (o,d) -> MapTrans s i o
  loop (MapTrans f) = MapTrans $ trace (unzipMap . f . zipMap)

instance ArrowLoop Auto where
  loop :: Auto (i,d) (o,d) -> Auto i o
  loop (Auto f) = Auto $ trace (foo . f)
    where foo :: ((o, d), Auto (i, d) (o, d)) -> ((o, Auto i o), d)
          foo ((o, d), Auto g) = ((o, loop (Auto g)), d)

-- Exercise 11: Define an ArrowLoop instance for StreamMap
-- Solution:

zipS :: (Stream a, Stream b) -> Stream (a, b)
zipS ~(Cons a as, Cons b bs) = Cons (a,b) (zipS (as,bs))

unzipS :: Stream (a,b) -> (Stream a, Stream b)
unzipS ~(Cons ~(a,b) abs) = let ~(as, bs) = unzipS abs
                            in (Cons a as, Cons b bs)

instance ArrowLoop StreamMap where
  -- recall that type StreamMap i o = Stream i -> Stream o
  loop :: StreamMap (i,d) (o,d) -> StreamMap i o
  loop (SM f) = SM $ trace (unzipS. f . zipS)

-- Exercise 12: Prove that loop (first f) = f
-- Solution:

-- We need to show that for any f, loop (first f) = f
{-
LHS = loop (first f)
    = loop (first f >>> id)
    = f >>> loop id
    = f >>> loop (pure id)
    = f >>> pure (trace id)
    = f >>> pure id
    = f >>> id
    = f
    = RHS
-}

-- genSym and arrow syntax
fetch :: State s () s
fetch = State $ \(s, ()) -> (s, s)

store :: State s s ()
store = State $ \(_, s) -> (s, ())

genSym :: State Int () Int
genSym = proc () -> do
  i <- fetch -< ()
  store -< i+1
  returnA -< i

-- Exercise 13: translate the definition of genSym from arrow syntax
-- Solution:

{-
genSym = proc () -> do
  i <- fetch -< ()
  store -< i+1
  returnA -< i
-}

genSym01 :: State Int () Int
genSym01 = ((proc () -> fetch -< ()) &&& returnA) >>>
           (proc (i, ()) -> do
              store -< i+1
              returnA -< i)

genSym02 :: State Int () Int
genSym02 = ((proc () -> fetch -< ()) &&& returnA) >>>
            (proc (i, ()) -> do
               _ <- store -< i+1
               returnA -< i)

genSym03 :: State Int () Int
genSym03 = ((proc () -> fetch -< ()) &&& returnA) >>>
           ((proc (i, ()) -> store -< i+1) &&& returnA) >>>
           ((proc (_, (i, ())) -> returnA -< i))

genSym04 :: State Int () Int
genSym04 = ((arr (\() -> ()) >>> fetch) &&& returnA) >>>
           ((proc (i, ()) -> store -< i+1) &&& returnA) >>>
           ((proc (_, (i, ())) -> returnA -< i))

genSym05 :: State Int () Int
genSym05 = ((arr (\() -> ()) >>> fetch) &&& returnA) >>>
           ((arr (\(i, ()) -> i+1) >>> store) &&& returnA) >>>
           ((proc (_, (i, ())) -> returnA -< i))

genSym06 :: State Int () Int
genSym06 = ((arr (\() -> ()) >>> fetch) &&& returnA) >>>
           ((arr (\(i, ()) -> i+1) >>> store) &&& returnA) >>>
           ((arr (\(_, (i, ())) -> i)) >>> returnA)

-- now it's fully de-sugared. Let me simplify.

genSym07 :: State Int () Int
genSym07 = ((arr id >>> fetch) &&& returnA) >>>
           ((arr (\(i, ()) -> i+1) >>> store) &&& returnA) >>>
           ((arr (\(_, (i, ())) -> i)) >>> returnA)

genSym08 :: State Int () Int
genSym08 = (fetch &&& returnA) >>>
           ((arr (\(i, ()) -> i+1) >>> store) &&& returnA) >>>
           ((arr (\(_, (i, ())) -> i)) >>> returnA)

genSym09 :: State Int () Int
genSym09 = fetch >>>
           ((arr (\i -> i+1) >>> store) &&& returnA) >>>
           ((arr (\(_, i) -> i)) >>> returnA)

genSym10 :: State Int () Int
genSym10 = fetch >>>
           ((arr (+1) >>> store) &&& id) >>>
           ((arr (\(_, i) -> i)) >>> returnA)

genSym11 :: State Int () Int
genSym11 = fetch >>>
           ((arr (+1) >>> store) &&& id) >>>
           (arr (\(_, i) -> i))

genSym12 :: State Int () Int
genSym12 = fetch >>> (((+1) ^>> store) &&& id) >>^ snd
