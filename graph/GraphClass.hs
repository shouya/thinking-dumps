{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module GraphClass where

import Data.Monoid (mconcat)

class Eq n => Node n

-- https://www.haskell.org/ghc/docs/latest/html/users_guide/type-class-extensions.html#functional-dependencies
class Node n => Graph g n | n -> g where
  adjacentNodes :: g n -> n -> [n]

  edgesFor :: g n -> n -> [(n,n)]
  edgesFor g n = map ((,) n) $ adjacentNodes g n

class Graph g n => FiniteGraph g n where
  allNodes :: g n -> [n]
  allEdges :: g n -> [(n, n)]
  allEdges g = mconcat $ map (edgesFor g) (allNodes g)
