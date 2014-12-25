module ConvexHull (algConvexHull) where

import TSPLib
import Data.List hiding (insert)
import Data.Function

algConvexHull :: TSPAlgorithm
algConvexHull ns = pathToEdges $ recur hull restNs
  where hull   = wrapPathEnds $ convexHull ns
        restNs = ns \\ hull

recur :: Path -> [Node] -> Path
recur p []     = p
recur p restNs = recur newP newRestNs
  where triplet   = select p restNs
        newRestNs = delete (snd triplet) restNs
        newP      = insert p triplet


select :: Path -> [Node] -> (Edge, Node)
select subtour restNs = triplet
  where edges    = pathToEdges subtour
        triplets = zip edges (map (`minK` restNs) edges)
        triplet  = minimumBy (compare `on` slope) triplets
        slope ((a,b), n) = (distance a n + distance b n) / distance a b

insert :: Path -> (Edge, Node) -> Path
insert p ((a,b), n) = insertBetween p a b n

minK :: Edge -> [Node] -> Node
minK edge = minimumBy (compare `on` delta edge)
  where delta (a,b) n = distance a n + distance b n - distance a b
