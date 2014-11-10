{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module BFS where

import Prelude hiding (pred)
import Data.List ((\\), sort)

import GraphClass

class (Node n, Ord n) => BFSNode n
instance (Node n, Ord n) => BFSNode n

bfs :: (Graph g n, BFSNode n) => (n -> Bool) -> g n -> n -> [n]
bfs term graph begin = reverse $ bfs' [begin] []
  where bfs' [] visited = visited
        bfs' queue@(x:xs) visited
          | term x = visited
          | otherwise =
            let newNodes = (unvisitedNodes x visited \\ queue)
            in bfs' (xs ++ newNodes) (x:visited)
        unvisitedNodes x visited =
          sort $ (adjacentNodes graph x \\ visited)

bfsTraverse :: (Graph g n, BFSNode n) => g n -> n -> [n]
bfsTraverse graph begin = bfs (const False) graph begin

bfsSearch :: (Graph g n, BFSNode n) => g n -> n -> n -> [n]
bfsSearch graph begin end = bfs (== end) graph begin ++ [end]
