module DFS where

import Prelude hiding (pred)
import Data.List ((\\), sort)
import Data.Array ((!))
import Data.Graph hiding (dfs)


dfs :: (Vertex -> Bool) -> Graph -> Vertex -> [Vertex]
dfs pred graph begin = reverse $ dfs' [begin] [begin]
  where dfs' (x:xs) visited
          | pred x    = visited
          | otherwise =
            case pickUnvisited x visited of
              (v:_) -> dfs' (v:x:xs) (v:visited)
              []    -> dfs' xs       visited
        dfs' [] visited = visited
        pickUnvisited x visited = sort (graph ! x \\ visited)


dfsTraverse :: Graph -> Vertex -> [Vertex]
dfsTraverse graph begin = dfs (const False) graph begin

dfsSearch :: Graph -> Vertex -> Vertex -> [Vertex]
dfsSearch graph begin end = dfs (== end) graph begin
