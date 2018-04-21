{-# LANGUAGE NamedFieldPuns #-}

import Knapsack

import Data.Foldable (maximumBy, Foldable)
import Data.Ord (comparing)
import Data.Function (on)

{-
data Solution = Solution { optimal :: Bool
                         , objective :: Int
                         , selectedItems :: [Int]
                         }

data Problem = Problem { capacity :: Weight
                       , items :: [(Value, Weight)]
                       }
-}

powersetIndices :: [a] -> [[Int]]
powersetIndices = (map . map) fst . powerset . zip [0..]
  where powerset :: [a] -> [[a]]
        powerset []     = [[]]
        powerset (x:xs) = (map (x:) powersetOfRest) ++ powersetOfRest
          where powersetOfRest = powerset xs

brutal :: Algorithm
brutal Problem { capacity, items } =
  Solution { optimal = True, selectedItems, objective}
  where allPossibilities = powersetIndices items
        totalWeight indices = sum $ map (\i -> value (items !! i)) indices
        totalValue indices  = sum $ map (\i -> weight (items !! i)) indices
        feasible indices = totalWeight indices <= capacity
        feasibleSolutions = filter feasible allPossibilities
        selectedItems = maximumBy (comparing `on` fst) feasibleSolutions
        objective = totalValue selectedItems


main = solveBy brutal
