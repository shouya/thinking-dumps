module NearestInsertion where

import TSPLib
import Insertion

import Data.List hiding (insert)
import Data.Function



algNearestInsertion :: TSPAlgorithm
algNearestInsertion = insertionAlgorithm select insert


select :: Path -> [Node] -> Node
select subtour restNs = selectedNode
  where possibleEdges = [closest stN restNs | stN <- subtour]
        selectedEdge  = minimumBy (compare `on` edgeLength) possibleEdges
        selectedNode  = snd selectedEdge

insert :: Node -> Path -> Path
insert n p = resultP
  where edges      = pathToEdges p
        dist (a,b) = distance a n + distance n b - distance a b
        minEdge    = minimumBy (compare `on` dist) edges
        newEdges   = [(fst minEdge, n), (snd minEdge, n)]
        resultE    = replace minEdge newEdges edges
        resultP    = tracePath' resultE n



closest :: Node -> [Node] -> Edge
closest n ms = (n, minimumBy (compare `on` distance n) ms)
