module NearestNeighbor where

import TSPLib
import Data.Function
import Data.List


algNearestNeighbor :: TSPAlgorithm
algNearestNeighbor [] = []
algNearestNeighbor [a,b] = [(a,b)]
algNearestNeighbor (n:ns) = result
  where minn = fst $
               minimumBy (compare `on` snd) $
               zip ns $
               map (distance n) ns
        result = (n, minn) : rest_paths
        rest_paths = algNearestNeighbor (minn : delete minn ns)
