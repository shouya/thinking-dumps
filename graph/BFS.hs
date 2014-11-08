module BFS where

import Prelude hiding (pred)
import Data.List ((\\), sort)
import GenericGraph

import Debug.Trace


bfs :: (Ix a, Show a) => (a -> Bool) -> Graph a -> a -> [a]
bfs pred graph begin = reverse $ bfs' [begin] []
  where bfs' [] visited = visited
        bfs' (x:xs) visited
          | pred x = visited
          | otherwise = bfs' (xs ++ unvisitedVertices x visited xs) (x:visited)
        unvisitedVertices x visited queue =
          sort $ ((adjacentVertices graph x \\ visited) \\ queue)

bfsTraverse :: (Ix a, Show a) => Graph a -> a -> [a]
bfsTraverse graph begin = bfs (const False) graph begin

bfsSearch :: (Ix a, Show a) => Graph a -> a -> a -> [a]
bfsSearch graph begin end = bfs (== end) graph begin ++ [end]
