{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module BFS where

import Prelude hiding (pred)
import Data.List ((\\), sort)
import Data.Function (on)

import GraphClass

class (Node n, Ord n) => BFSNode n
instance (Node n, Ord n) => BFSNode n

bfs :: (Graph g n e, BFSNode n) => (n -> Bool) -> g -> n -> Maybe [e]
bfs term graph begin = reverse $ label result
  where result = if term begin then Just [] else bfs'
        bfs' [] (v:vs)
          | term (target $ edge v) = Just (path v)
          | _                      = Nothing
        bfs' queue@(q:qs) (v:vs)
          | term (target $ edge q) = Just (path v)
          | _  = bfs' (qs ++ unvisitedEdges q (v:vs)) (q:v:vs)
        unvisitedEdges q vs = map appendPath $
                              filter (not . isVisited vs) $
                              adjacentNodes q
        edgesFrom q = edgesFor (target $ edge q)
        isVisited vs n = map (matches n) vs
        matches = ((==) `on` (target . edge))
        appendPath =
        edge = fst
        path = snd










  bfs' [] [] []
  where bfs' [] visited =
        bfs' queue@(x:xs) visited
          | term x = result
          | otherwise =
            let newNodes = (unvisitedNodes x visited \\ queue)
            in bfs' (xs ++ newNodes) (x:visited)
        unvisitedNodes x visited =
          edgesFor x
        unvisitedNodes x visited =
          sort $ (adjacentNodes graph x \\ visited)

bfsTraverse :: (Graph g n, BFSNode n) => g -> n -> [n]
bfsTraverse graph begin = bfs (const False) graph begin

bfsSearch :: (Graph g n, BFSNode n) => g -> n -> n -> [n]
bfsSearch graph begin end = bfs (== end) graph begin ++ [end]
