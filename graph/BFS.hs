{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module BFS where

import Prelude hiding (pred)

import Data.List (sortBy)
import Data.Function (on)

import GraphClass

class (Node n, Ord n) => BFSNode n
instance (Node n, Ord n) => BFSNode n


bfs :: (Graph g n e, BFSNode n) => (n -> Bool) -> g -> n -> Either [n] [e]
bfs term graph begin = result >>= return . reverse
  where result = if term begin
                 then Right []
                 else bfs' [(begin, [])] []
        bfs' [] vs = Left vs
        bfs' (q:qs) vs
          | term (node q) = Right (path q)
          | otherwise =
            let vs' = node q : vs
                qs' = qs ++ (sortBy (compare `on` node) newQueueElems)
                newQueueElems = map pathify unvisitedEdges
                unvisitedEdges = filter (not . queued)  $
                                 filter (not . visited) $
                                 edgesFor graph (node q)
                visited x = (target x) `elem` vs'
                queued  x = (target x) `elem` (map node qs)
                pathify e = (target e, label e : path q)
            in bfs' qs' vs'
          where (node, path) = (fst, snd)


bfsTraverse :: (Graph g n e, BFSNode n) => g -> n -> [n]
bfsTraverse graph begin =
  case bfs (const False) graph begin of
    Left xs -> reverse xs
    Right _ -> error "impossible"


bfsSearch :: (Graph g n e, BFSNode n) => g -> n -> n -> Maybe [e]
bfsSearch graph begin end =
  case bfs (== end) graph begin of
    Left _   -> Nothing
    Right xs -> Just xs
