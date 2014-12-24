module NearestInsertion (algNearestInsertion) where

import TSPLib
import Insertion

import Data.List hiding (insert)


algNearestInsertion :: TSPAlgorithm
algNearestInsertion = insertionAlgorithm select


select :: Path -> [Node] -> Node
select subtour restNs = selectedNode
  where possibleEdges = [nearestEdgeTo stN restNs | stN <- subtour]
        selectedEdge  = minimumBy compEdgeDist possibleEdges
        selectedNode  = snd selectedEdge
