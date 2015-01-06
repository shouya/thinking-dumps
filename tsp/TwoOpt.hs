module TwoOpt (algTwoOpt) where

import TSPLib

import Data.List
import NearestNeighbor (algNearestNeighbor)


algTwoOpt :: TSPAlgorithm
algTwoOpt ns = twoOpt prilimiary
  where prilimiary = algNearestNeighbor ns

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
stillConnected es ep@((m,_), (_,n')) = length optedPath == length es
  where optedPath = tracePath (delete (m,n') (opt es ep)) m


opt :: [Edge] -> EdgePair -> [Edge]
opt es (e1, e2) = (es \\ [e1, e2]) ++ opted e1 e2
  where opted (m,m') (n,n') = [(m, n'), (n, m')]
