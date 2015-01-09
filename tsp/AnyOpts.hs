module AnyOpt (opt) where


import TSPLib

import Data.List
import Data.Tuple
import Data.Function
import Control.Monad

import NearestNeighbor (algNearestNeighbor)
import FurthestInsertion (algFurthestInsertion)



-- this is actually an order 2 symmetric group with all
-- binary transpositions over n elements

optNodes :: Int -> [Node] -> [[Edge]]
optNodes 0 [] = [[]]
optNodes 0 _  = error "impossible case"
optNodes n ns = take (length edgesS `div` n) edgesS
  where edgesSS = [ map (selEdge:) $ optNodes (n-1) otherNodes
                  | selEdge <- trigCartProd ns
                  , let otherNodes = ns \\ [fst selEdge, snd selEdge]
                  ]
        edgesS  = join edgesSS

opt :: Int -> [Edge] -> [[Edge]]
opt n es = optNodes n allNodes
  where allNodes = liftM2 (++) (map fst) (map snd) es
