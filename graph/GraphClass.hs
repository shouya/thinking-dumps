{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImpredicativeTypes #-}

module GraphClass where

import Data.Monoid (mconcat)
import Control.Monad (liftM2, liftM)
import Data.List (find)

class Eq n => Node n
type LEdge n e = ((n,n),e)

origin :: LEdge n e -> n
origin ((n,_), _) = n
target :: LEdge n e -> n
target ((_,n), _) = n
label  :: LEdge n e -> e
label  ((_,_), e) = e


-- https://www.haskell.org/ghc/docs/latest/html/users_guide/type-class-extensions.html#functional-dependencies
class Node n => Graph g n e | g n -> e where
  adjacentNodes :: g -> n -> [n]
  adjacentNodes g = map target . edgesFor g

  followEdge :: Eq e => g -> e -> n -> Maybe n
  followEdge g e = liftM target .
                   find ((e ==) . label) .
                   edgesFor g

  edgesFor :: g -> n -> [LEdge n e]


class Graph g n e => FiniteGraph g n e | g n -> e where
  allNodes :: g -> [n]
  allEdges :: g -> [LEdge n e]
  allEdges = mconcat . liftM2 map edgesFor allNodes
