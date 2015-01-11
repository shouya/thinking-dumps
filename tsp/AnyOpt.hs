module AnyOpt (algAnyOpt) where


import TSPLib

import Data.List
import Data.Tuple
import Data.Function
import Data.Maybe
import Control.Monad
import Debug.Trace

import NearestNeighbor (algNearestNeighbor)


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

minOpt :: Int -> [Edge] -> [Edge] -> Maybe [Edge]
minOpt n route es = result
  where opts        = opt n es
        isConnected = filter (connected route es)
        shortEdges  = filter ((< origEsLen) . edgesLen)
        minEdges    = minimumBy (compare `on` edgesLen)
        result      = case (isConnected . shortEdges) opts of
                       [] -> Nothing
                       xs -> Just $ minEdges xs
        origEsLen   = edgesLen es
        edgesLen    = sum . map edgeLength



connected :: [Edge] -> [Edge] -> [Edge] -> Bool
connected route es ses = length route + 1 == length optedPath
  where optedEdges = substitute route es ses
        optedNode  = snd $ head es
        optedPath  = tracePath' optedEdges optedNode

substitute :: [Edge] -> [Edge] -> [Edge] -> [Edge]
substitute allEs exEs newEs = excludedEdges ++ newEs
  where excludedEdges = allEs \\ (exEs ++ map swap exEs)

nOpt :: Int -> [Edge] -> [Edge]
nOpt n route = case eps of
                []    -> route
                (x:_) -> nOpt n $ uncurry (substitute route) x
  where eps = [ (edgePair, substPair)
              | edgePair  <- combinations n route
              , substPair <- maybeToList $ minOpt n route edgePair
              ]

algAnyOpt :: Int -> TSPAlgorithm
algAnyOpt n ns = result
  where prilimiary = algNearestNeighbor ns
        result     = nOpt n prilimiary
