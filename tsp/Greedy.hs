module Greedy where

import TSPLib

import Data.List
import Data.Tuple
import Data.Function

import Debug.Trace

algGreedy :: TSPAlgorithm
algGreedy ns = choose allPairs []
  where allPairs = concat $ zipWith (\n ms -> map ((,) n) ms) ns (inits ns)


choose :: [Edge] -> [Edge] -> [Edge]
choose [] chosen = chosen
choose es chosen = if edgeValid minEdge
                   then choose restEdges (minEdge : chosen)
                   else choose restEdges chosen
  where minEdge     = minimumBy (compare `on` edgeLength) es
        restEdges   = delete minEdge es
        edgeValid (n,m) = not (degree n >= 2 || degree m >= 2) &&
                          not (causeCycle n m)
        causeCycle n m  = m `elem` tracePath chosen n
        degree n        = length $
                          filter ((n ==) . fst) (chosen ++ map swap chosen)
