module NearestInsertion where

import TSPLib

import Data.List hiding (insert)
import Data.Tuple
import Data.Function


algNearestInsertion :: TSPAlgorithm
algNearestInsertion []     = []
algNearestInsertion (n:nodes) = pathToEdges $ recur' initPath nodes
  where initPath = [n, n]
        recur' path [] = path
        recur' path ns = let selectedNode = select initPath ns
                             newPath      = insert selectedNode path
                             newNs        = delete selectedNode ns
                         in recur' newPath newNs


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
        resultE    = takeWhile (/=minEdge) edges ++
                     [(fst minEdge, n), (snd minEdge, n)] ++
                     tail (dropWhile (/=minEdge) edges)
        resultP    = tracePath' resultE n



closest :: Node -> [Node] -> Edge
closest n ms = (n, minimumBy (compare `on` distance n) ms)
