
module TwoOpt (algTwoOpt) where

import TSPLib

import Data.List
import Data.Tuple
import NearestNeighbor (algNearestNeighbor)
import FurthestInsertion (algFurthestInsertion)



algTwoOpt :: TSPAlgorithm
algTwoOpt ns = result
  where  prilimiary = algFurthestInsertion ns
    -- prilimiary = algNearestNeighbor ns
         result = twoOpt prilimiary

type EdgePair = (Edge, Edge)


twoOpt :: [Edge] -> [Edge]
twoOpt es = case eps of
             []     -> es
             (ep:_) -> twoOpt $ opt es ep
  where eps = [edgePair |
               edgePair <- trigCartProd es,
               lengthShorter edgePair,
               stillConnected es edgePair]

lengthShorter :: EdgePair -> Bool
lengthShorter ((m,m'), (n,n')) = newDist < oldDist
  where oldDist = distance m m' + distance n n'
        newDist = distance m n' + distance n m'

stillConnected :: [Edge] -> EdgePair -> Bool
stillConnected es ep = length origPath == length optedPath
  where optedPath = tracePath' (opt es ep) (fst $ head es)
        origPath  = tracePath' es          (fst $ head es)


opt :: [Edge] -> EdgePair -> [Edge]
opt es (e1, e2) = newEs
  where opted (m,m') (n,n') = [(m, n'), (n, m')]
        newEs = (es \\ [e1, e2, swap e1, swap e2]) ++ opted e1 e2
