module DFS where

import Data.List ((\\), sort)
import Data.Array ((!))
import Data.Maybe (listToMaybe)
import Data.Graph

dfsTraverse :: Graph -> Vertex -> [Vertex]
dfsTraverse graph start = dfs' [start] [start]
  where dfs' (x:xs) visited =
          case pickUnvisited x visited of
            Just v  -> dfs' (v:x:xs) (v:visited)
            Nothing -> dfs' xs visited
        dfs' [] visited    = reverse visited
        pickUnvisited x visited = listToMaybe $ sort (graph ! x \\ visited)
