module BFS where

import Prelude hiding (pred)
import Data.List ((\\), sort)
import GenericGraph


bfs :: (Ix a, Show a) => (a -> Bool) -> Graph a -> a -> [a]
bfs pred graph begin = reverse $ bfs' [begin] []
  where bfs' [] visited = visited
        bfs' queue@(x:xs) visited
          | pred x = visited
          | otherwise =
            let newVertices = (unvisitedVertices x visited \\ queue)
            in bfs' (xs ++ newVertices) (x:visited)
        unvisitedVertices x visited =
          sort $ (adjacentVertices graph x \\ visited)

bfsTraverse :: (Ix a, Show a) => Graph a -> a -> [a]
bfsTraverse graph begin = bfs (const False) graph begin

bfsSearch :: (Ix a, Show a) => Graph a -> a -> a -> [a]
bfsSearch graph begin end = bfs (== end) graph begin ++ [end]
