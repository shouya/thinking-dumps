{-# LANGUAGE NamedFieldPuns #-}

import Knapsack

import Control.Monad

import Data.Foldable (maximumBy, Foldable)
import Data.Ord (comparing)
import Data.Function (on, (&))


{-
data Solution = Solution { optimal :: Bool
                         , objective :: Int
                         , selectedItems :: [Int]
                         }

data Problem = Problem { capacity :: Weight
                       , items :: [(Value, Weight)]
                       }
-}



powerset :: [a] -> [[a]]
powerset xs = filterM (\x -> [True, False]) xs

brutal :: Algorithm
brutal prob@Problem { capacity, givenItems } =
  solution prob selectedItems Optimal
  where selectedItems = powerset givenItems
                        & filter feasible
                        & maximumBy (comparing overallValue)
        feasible items = sum (fmap weight items) < capacity
        overallValue items = sum (fmap value items)

main = solveBy brutal
