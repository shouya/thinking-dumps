module Insertion (insertionAlgorithm) where

import TSPLib

import Data.List hiding (insert)


type Select = Path -> [Node] -> Node
type Insert = Node -> Path -> Path

insertionAlgorithm :: Select -> Insert -> TSPAlgorithm
insertionAlgorithm _   _   []        = []
insertionAlgorithm sel ins (n:nodes) = pathToEdges $ recur' initPath nodes
  where initPath = [n, n]
        recur' path [] = path
        recur' path ns = let selectedNode = sel initPath ns
                             newPath      = ins selectedNode path
                             newNs        = delete selectedNode ns
                         in recur' newPath newNs
