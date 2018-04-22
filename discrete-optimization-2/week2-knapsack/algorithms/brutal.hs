{-# LANGUAGE NamedFieldPuns #-}

import Knapsack

import Control.Monad

import Data.Foldable (maximumBy)
import Data.Ord (comparing)
import Data.Function ((&))



powerset :: [a] -> [[a]]
powerset xs = filterM (const [True, False]) xs

brutal :: Algorithm
brutal prob@Problem { capacity, givenItems } =
  solution prob selectedItems Optimal
  where selectedItems = powerset givenItems
                        & filter feasible
                        & maximumBy (comparing overallValue)
        feasible items = sum (fmap weight items) <= capacity
        overallValue items = sum (fmap value items)

main :: IO ()
main = solveBy brutal
