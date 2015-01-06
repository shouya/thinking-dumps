module TwoOpt (algTwoOpt) where

import TSPLib

import Data.List
import Data.Tuple
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
                  { twoOptEdges    :: EdgePair
                  , twoOptStrategy :: TwoOptStrategy
                  }


allStrategies :: [TwoOptStrategy]
allStrategies = [stgy1, stgy2]
  where stgy1 ((n,n'), (m,m')) = ((n,m), (n',m'))
        stgy2 ((n,n'), (m,m')) = ((n,m'), (m,n'))


twoOpt :: [Edge] -> [Edge]
twoOpt es = case eps of
             []     -> es
             (ep:_) -> twoOpt $ optSol es ep
  where eps = [OptSolution edgePair stgy |
               edgePair <- trigCartProd es,
               stgy     <- allStrategies,
               lengthShorter edgePair stgy,
               stillConnected es edgePair stgy]

sumDistance :: EdgePair -> Double
sumDistance (e1, e2) = edgeLength e1 + edgeLength e2

lengthShorter :: EdgePair -> TwoOptStrategy -> Bool
lengthShorter ep stgy = newDist < oldDist
  where oldDist = sumDistance ep
        newDist = sumDistance $ stgy ep

stillConnected :: [Edge] -> EdgePair -> TwoOptStrategy -> Bool
stillConnected es ep stgy = length origPath == length optedPath
  where optedPath = tracePath' (opt es ep stgy) (fst $ head es)
        origPath  = tracePath' es               (fst $ head es)


optSol :: [Edge] -> OptSolution -> [Edge]
optSol es sol = opt es (twoOptEdges sol) (twoOptStrategy sol)

opt :: [Edge] -> EdgePair -> TwoOptStrategy -> [Edge]
opt es ep stgy = newEs
  where opted = tupleToList $ stgy ep
        newEs = (es \\ epEs ep) ++ opted
        epEs (e1,e2) = [e1, e2, swap e1, swap e2]
