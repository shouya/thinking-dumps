{-# LANGUAGE NamedFieldPuns #-}

import Knapsack

import Data.Foldable (maximumBy)
import Control.Applicative

import Data.List (sortBy)
import Data.Ord (comparing)
import Data.Function (on, (&))

-- let's cheat with Haskell's non-strictness :)
import Data.Array

type NumItems = Int

maxBy :: (a -> a -> Ordering) -> a -> a -> a
maxBy f a b = maximumBy f [b, a]

compareSolution :: (Weight, [Item]) -> (Weight, [Item]) -> Ordering
compareSolution = comparing fst

addItemToSolution :: Item -> (Weight, [Item]) -> (Weight, [Item])
addItemToSolution item (w, items) = (w + weight item, item : items)

lazyTable :: Weight -> [Item] -> Array (Weight, NumItems) (Weight, [Item])
lazyTable capacity items = arr
  where arr = array bounds [((c,n), itemAt c n) | c <- [0..capacity], n <- [0..numItems]]
        numItems = length items
        bounds = ((0,0), (capacity, numItems))
        itemAt cap 0 = (0, [])
        itemAt cap n = let nthItem = items !! (n - 1)
                           prevSolution = arr ! (cap, n - 1)
                           nthItemWeight = weight nthItem
                           weightRemovedSolution = arr ! (cap - nthItemWeight, n - 1)
                           newSolution = addItemToSolution nthItem weightRemovedSolution
                       in if nthItemWeight <= cap
                          then maxBy compareSolution prevSolution newSolution
                          else prevSolution

traversable ::

dynamicProgramming :: Algorithm
dynamicProgramming prob@Problem { capacity, givenItems } =
  solution prob selectedItems Optimal
  where selectedItems = snd $ lazyTable capacity givenItems ! (capacity, length givenItems)



main :: IO ()
main = solveBy dynamicProgramming
