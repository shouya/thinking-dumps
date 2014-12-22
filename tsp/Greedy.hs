module Greedy where

import TSPLib

import Data.List
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
        edgeValid (n,m) = not (causeCycle n m) &&
                          not (degree n > 2 || degree m > 2)
        causeCycle n m  = trace ((show chosen) ++ (show n) ++ (show m)++(show (tracePath chosen n == m))) $ tracePath chosen n == m
        degree n        = length $
                          filter ((n /=) . fst) chosen ++
                          filter ((n /=) . snd) chosen
