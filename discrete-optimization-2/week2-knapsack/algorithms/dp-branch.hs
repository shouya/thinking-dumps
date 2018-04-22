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

-- now with branches!
type PartialSolution = (Weight, [[Item]])


selectMergeSolution :: PartialSolution -> PartialSolution -> PartialSolution
selectMergeSolution s1@(w1, xss1) s2@(w2, xss2)
  | w1 == w2 = (w1, xss1 ++ xss2)
  | otherwise = maximumBy (comparing fst) [s1, s2]

compareSolution :: PartialSolution -> PartialSolution -> Ordering
compareSolution = comparing fst

addItemToSolution :: Item -> PartialSolution -> PartialSolution
addItemToSolution item (w, items) = (w + weight item, map (item:) items)

lazyTable :: Weight -> [Item] -> Array (Weight, NumItems) PartialSolution
lazyTable capacity items = arr
  where arr = array bounds' [((c,n), itemAt c n) | c <- [0..capacity], n <- [0..numItems]]
        numItems = length items
        bounds' = ((0,0), (capacity, numItems))
        itemAt _cap 0 = (0, [[]])
        itemAt cap n = let nthItem = items !! (n - 1)
                           prevSolution = arr ! (cap, n - 1)
                           nthItemWeight = weight nthItem
                           weightRemovedSolution = arr ! (cap - nthItemWeight, n - 1)
                           newSolution = addItemToSolution nthItem weightRemovedSolution
                       in if nthItemWeight < cap
                          then selectMergeSolution prevSolution newSolution
                          else prevSolution


dynamicProgramming :: Algorithm
dynamicProgramming prob@Problem { capacity, givenItems } =
  solution prob selectedItems Optimal
  where selectedItems = (snd totalSolution) !! 0
        totalSolution = lazyTable capacity givenItems ! (capacity, length givenItems)



main :: IO ()
main = solveBy dynamicProgramming
