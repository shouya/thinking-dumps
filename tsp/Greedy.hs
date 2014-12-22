module Greedy where

import TSPLib

import Data.List
import Data.Function


algGreedy :: TSPAlgorithm
algGreedy ns = choose allPairs []
  where allPairs = concat $ zipWith (\n ms -> map ((,) n) ms) ns (inits ns)


choose :: [Edge] -> [Edge] -> [Edge]
choose [] chosen = chosen
choose es chosen = if validEdge minEdge
                   then choose restEdges (minEdge : chosen)
                   else choose restEdges chosen
  where minEdge     = minimumBy (compare `on` edgeLength) es
        restEdges   = delete minEdge es
        validEdge (n,m) = not (hasCycle n m) &&
                          not (degree n > 2 || degree m > 2)
        degree n = length $ filter ((n /=) . fst) chosen ++
                            filter ((n /=) . snd) chosen
        hasCycle n m = tracePath es n == m
