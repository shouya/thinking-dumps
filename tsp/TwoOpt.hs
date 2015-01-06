module TwoOpt (algTwoOpt) where

import TSPLib

import Data.List
import Data.Tuple
import Data.Function

import NearestNeighbor (algNearestNeighbor)
import FurthestInsertion (algFurthestInsertion)



algTwoOpt :: TSPAlgorithm
algTwoOpt ns = result
  where prilimiary = algFurthestInsertion ns
        -- prilimiary = algNearestNeighbor ns
        result = twoOpt prilimiary

type EdgePair = (Edge, Edge)
type TwoOptStrategy = EdgePair -> EdgePair

data OptSolution = OptSolution
                   { origEdges  :: EdgePair
                   , optedEdges :: EdgePair
                   , deltaLen   :: Double
                   }


allStrategies :: [TwoOptStrategy]
allStrategies = [stgy1, stgy2]
  where stgy1 ((n,n'), (m,m')) = ((n,m), (n',m'))
        stgy2 ((n,n'), (m,m')) = ((n,m'), (m,n'))


twoOpt :: [Edge] -> [Edge]
twoOpt es = if null eps then es else optSol es bestEps
  where bestEps = minimumBy (compare `on` deltaLen) eps
        eps = [sol |
               edgePair <- trigCartProd es,
               stgy     <- allStrategies,
               let optedEp = stgy edgePair
                   origLen = edgePairDistance edgePair
                   newLen  = edgePairDistance optedEp
                   delta   = newLen - origLen
                   sol     = OptSolution edgePair optedEp delta,
               delta < 0, -- the total length is decreasing
               stillConnected es sol]


edgePairDistance :: EdgePair -> Double
edgePairDistance (e1, e2) = edgeLength e1 + edgeLength e2

stillConnected :: [Edge] -> OptSolution -> Bool
stillConnected es sol = length es == length optedPath
  where optedPath = tracePath' (optSol es sol) optedNode
        optedNode = fst $ fst $ origEdges sol

optSol :: [Edge] -> OptSolution -> [Edge]
optSol es sol = opt es (origEdges sol) (optedEdges sol)

opt :: [Edge] -> EdgePair -> EdgePair -> [Edge]
opt es ep optedEp = newEs
  where opted = tupleToList optedEp
        newEs = (es \\ epEs ep) ++ opted
        epEs (e1,e2) = [e1, e2, swap e1, swap e2]
