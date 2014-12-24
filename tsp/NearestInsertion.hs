module NearestInsertion where

import TSPLib
import Insertion

import Data.List hiding (insert)
import Data.Function



algNearestInsertion :: TSPAlgorithm
algNearestInsertion = insertionAlgorithm select


select :: Path -> [Node] -> Node
select subtour restNs = selectedNode
  where possibleEdges = [closestEdgeTo stN restNs | stN <- subtour]
        selectedEdge  = minimumBy (compare `on` edgeLength) possibleEdges
        selectedNode  = snd selectedEdge
