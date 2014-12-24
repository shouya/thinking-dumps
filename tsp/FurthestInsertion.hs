module FurthestInsertion (algFurthestInsertion) where

import TSPLib
import Insertion

import Data.List hiding (insert)


algFurthestInsertion :: TSPAlgorithm
algFurthestInsertion = insertionAlgorithm select

select :: Path -> [Node] -> Node
select subtour restNs = selectedNode
  where possibleEdges = [furthestEdgeTo stN restNs | stN <- subtour]
        selectedEdge  = maximumBy compEdgeDist possibleEdges
        selectedNode  = snd selectedEdge


{-
  where possibleEdges = [nearestEdgeTo stN restNs | stN <- subtour]
        selectedEdge  = maximumBy compEdgeDist possibleEdges
        selectedNode  = snd selectedEdge
-}
