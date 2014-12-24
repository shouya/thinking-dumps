module Insertion (
  Select,
  insertionAlgorithm
  ) where

import TSPLib

import Data.List hiding (insert)
import Data.Function

type Select = Path -> [Node] -> Node

insertionAlgorithm :: Select -> TSPAlgorithm
insertionAlgorithm _   []        = []
insertionAlgorithm sel (n:nodes) = pathToEdges $ recur' initPath nodes
  where initPath = [n, n]
        recur' path [] = path
        recur' path ns = let selectedNode = sel initPath ns
                             newPath      = insert selectedNode path
                             newNs        = delete selectedNode ns
                         in recur' newPath newNs


insert :: Node -> Path -> Path
insert n p = resultP
  where edges      = pathToEdges p
        dist (a,b) = distance a n + distance n b - distance a b
        minEdge    = minimumBy (compare `on` dist) edges
        newEdges   = [(fst minEdge, n), (snd minEdge, n)]
        resultE    = replace minEdge newEdges edges
        resultP    = tracePath' resultE n
