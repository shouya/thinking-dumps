{-# LANGUAGE NamedFieldPuns #-}

import Knapsack

import Data.List (sortBy)
import Data.Ord (comparing)
import Data.Function ((&))

data ScoredItem = ScoredItem { siScore :: Float
                             , siItem  :: Item
                             }

type GreedyStrategy = Item -> ScoredItem

greedyOn :: GreedyStrategy -> Problem -> Solution
greedyOn tr prob@Problem { capacity, givenItems } =
  solution prob selectedItems NotOptimal
  where selectedItems = fmap tr givenItems
                        & sortBy (comparing siScore)
                        & fmap siItem
                        & takeItemUntilExceed capacity

takeItemUntilExceed :: Weight -> [Item] -> [Item]
takeItemUntilExceed = takeItemUntilExceed' 0
  where takeItemUntilExceed' _curr _cap []   = []
        takeItemUntilExceed' curr cap (x:xs) = if curr + weight x <= cap
                                               then x : (takeItemUntilExceed' (curr + weight x) cap xs)
                                               else []

minWeight :: GreedyStrategy
minWeight item = ScoredItem { siScore = fromIntegral $ -(weight item)
                            , siItem = item
                            }

maxValue :: GreedyStrategy
maxValue item = ScoredItem { siScore = fromIntegral $ value item
                           , siItem = item
                           }

bestVWRatio :: GreedyStrategy
bestVWRatio item = ScoredItem { siScore = fromIntegral (value item) / fromIntegral (weight item)
                              , siItem = item
                              }
main :: IO ()
main = solveBy $ greedyOn bestVWRatio
