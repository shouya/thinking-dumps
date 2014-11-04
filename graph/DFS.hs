module DFS where

import Data.List ((\\), sort)
import Data.Array ((!))
import Data.Graph

dfsTraverse :: Graph -> Vertex -> [Vertex]
dfsTraverse graph begin = reverse $ dfs' [begin] [begin]
  where dfs' (x:xs) visited =
          case pickUnvisited x visited of
            (v:_) -> dfs' (v:x:xs) (v:visited)
            []    -> dfs' xs visited
        dfs' [] visited    = visited
        pickUnvisited x visited = sort (graph ! x \\ visited)


dfsSearch :: Graph -> Vertex -> Vertex -> [Vertex]
dfsSearch graph begin end = reverse $ dfs' [begin] [begin]
  where dfs' (x:xs) visited
          | x == end  = visited
          | otherwise =
            case pickUnvisited x visited of
              (v:_) -> dfs' (v:x:xs) (v:visited)
              []    -> dfs' xs       visited
        dfs' [] visited = visited
        pickUnvisited x visited = sort (graph ! x \\ visited)
