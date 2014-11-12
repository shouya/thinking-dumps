{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module GraphClass where

import Data.Monoid (mconcat)

class Eq n => Node n

-- https://www.haskell.org/ghc/docs/latest/html/users_guide/type-class-extensions.html#functional-dependencies
class Node n => Graph g n where
  adjacentNodes :: g -> n -> [n]

  edgesFor :: g -> n -> [(n,n)]
  edgesFor g n = map ((,) n) $ adjacentNodes g n

class Graph g n => FiniteGraph g n where
  allNodes :: g -> [n]
  allEdges :: g -> [(n, n)]
  allEdges g = mconcat $ map (edgesFor g) (allNodes g)
