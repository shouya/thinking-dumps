module CheapestInsertion (algCheapestInsertion) where

import TSPLib
import Insertion

import Data.List hiding (insert)
import Data.Function


algCheapestInsertion :: TSPAlgorithm
algCheapestInsertion = insertionAlgorithm select

select :: Path -> [Node] -> Node
select subtour restNs = selectedNode
  where selectedNode = minimumBy (compare `on` flip cost subtour) restNs

cost :: Node -> Path -> Double
cost n p = edgeLength minEdge
  where edges      = pathToEdges p
        dist (a,b) = distance a n + distance n b - distance a b
        minEdge    = minimumBy (compare `on` dist) edges
