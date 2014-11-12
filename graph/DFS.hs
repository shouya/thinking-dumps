{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module DFS where

import Prelude hiding (pred)
import Data.List ((\\), sort)

import GraphClass

class (Node n, Ord n) => DFSNode n
instance (Node n, Ord n) => DFSNode n


dfs :: (Graph g n, DFSNode n) => (n -> Bool) -> g -> n -> [n]
dfs pred graph begin = reverse $ dfs' [begin] [begin]
  where dfs' (x:xs) visited
          | pred x    = visited
          | otherwise =
            case unvisitedNodes x visited of
              []    -> dfs' xs       visited
              (v:_) -> dfs' (v:x:xs) (v:visited)
        dfs' [] visited = visited
        unvisitedNodes x visited =
          sort (adjacentNodes graph x \\ visited)


dfsTraverse :: (Graph g n, DFSNode n) => g -> n -> [n]
dfsTraverse graph begin = dfs (const False) graph begin

dfsSearch :: (Graph g n, DFSNode n) => g -> n -> n -> [n]
dfsSearch graph begin end = dfs (== end) graph begin
