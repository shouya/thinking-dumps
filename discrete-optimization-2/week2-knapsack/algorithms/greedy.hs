{-# LANGUAGE NamedFieldPuns #-}

import Knapsack

import Control.Applicative
import Control.Monad.State.Lazy

import Data.Ord (comparing)
import Data.Function (on)

type GetItemPriority = (Value, Weight) -> Float

takeWhileM :: Monad m => (a -> m Bool) -> [m a] -> m [a]
takeWhileM _ []       = return []
takeWhileM f (mx:mxs) = do
  x <- mx
  cond <- f x
  if cond
    then do xs <- takeWhileM f mxs
            return (x:xs)
    else return []

type IntermediateState = State (Value, Weight)

belowCapcityAggregate :: (Value, Weight) -> IntermediateState (Value, Weight)
belowCapacityAggregate (value, weight) = do
  (aggValue, aggWeight) <- get
  if aggWeight + weight <= capacity
    then do set (aggValue + value, aggWeight + weight)
            return True
    else return False

greedyOnCriterion :: GetItemPriority -> Algorithm
greedyOnCriterion criterion Problem { capacity, items } =
  let (selectedItems, (objective, _)) = runState takenItems (0, 0)
  in Solution { optimal = False, selectedItems, objective}
  where sortedItems = sortBy (comparing `on` criterion) items
        takenItems = takeWhileM belowCapacityAggregate
