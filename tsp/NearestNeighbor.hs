module NearestNeighbor (algNearestNeighbor) where

import TSPLib
import Data.Function
import Data.List


algNearestNeighbor :: TSPAlgorithm
algNearestNeighbor = wrapEnds . recur


recur :: TSPAlgorithm
recur []    = []
recur [a,b] = [(a,b)]
recur (n:ns) = result
  where minn = fst $
               minimumBy (compare `on` snd) $
               zip ns $
               map (distance n) ns
        result = (n, minn) : rest_paths
        rest_paths = recur (minn : delete minn ns)
