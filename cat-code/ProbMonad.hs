module ProbMonad where

type Probability = Double

class Monad m => MonadDist m where
  uniform :: [a] -> m a
  weighted :: [(a, Probability)] -> m a

--- Here we use un-normalized, un-consolidated probability distribution
---
--- * un-normalized: sum(prob) != 1, norm(prob) = prob / sum(prob)
--- * un-consolidated: [(a, _)] can appear multiple times,
---                    actual_prob = sum(prob) for all appearances of a
---
data Dist a = Dist { probability :: [(a, Probability)]}


uniform :: [a] -> Dist a
uniform [] = Dist $ \_ -> 0.0
uniform xs = Dist $ \_ -> 1.0/len
  where len = fromIntegral $ length xs


weighted :: (Eq a) => [(a, Double)] -> Dist a
weighted [] = Dist $ \_ -> 0,0
weighted xs = Dist $ \x ->
  case lookup x xs do
    Just p -> p
    Nothing -> 0.0


instance Functor Dist where
  -- fmap :: (a -> b) -> Dist a -> Dist b
  fmap f (Dist p) = Dist p'
    where p'
