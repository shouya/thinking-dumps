module DFS where

import Prelude hiding (pred)
import Data.List ((\\), sort)
import GenericGraph


dfs :: (Ix a) => (a -> Bool) -> Graph a -> a -> [a]
dfs pred graph begin = reverse $ dfs' [begin] [begin]
  where dfs' (x:xs) visited
          | pred x    = result
          | otherwise =
            case unvisitedVertices x visited of
              []    -> dfs' xs       visited
              (v:_) -> dfs' (v:x:xs) (v:visited)
        dfs' [] visited = result
        unvisitedVertices x visited =
          sort (adjacentVertices graph x \\ visited)


dfsTraverse :: (Ix a) => Graph a -> a -> [a]
dfsTraverse graph begin = dfs (const False) graph begin

dfsSearch :: (Ix a) => Graph a -> a -> a -> [a]
dfsSearch graph begin end = dfs (== end) graph begin ++ [end]
