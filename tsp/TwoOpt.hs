module TwoOpt (algTwoOpt) where

import TSPLib

import Data.List
import Data.Tuple
import NearestNeighbor (algNearestNeighbor)
import FurthestInsertion (algFurthestInsertion)

import Debug.Trace
import Test.QuickCheck


algTwoOpt :: TSPAlgorithm
algTwoOpt ns = twoOpt prilimiary
  where prilimiary = algFurthestInsertion ns
        -- prilimiary = algNearestNeighbor ns

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
stillConnected es ep = True -- trace (show (length origPath) ++ show (length optedPath)) True
  where optedPath = tracePath' (opt es ep) (fst $ head es)
        origPath  = tracePath' es          (fst $ head es)


opt :: [Edge] -> EdgePair -> [Edge]
opt es (e1, e2) = trace (show (length newEs) ++ show (length es)) newEs
  where opted (m,m') (n,n') = [(m, n'), (n, m')]
        newEs = (es \\ [e1, e2, swap e1, swap e2]) ++ opted e1 e2
