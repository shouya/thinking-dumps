module NearestMerger (algNearestMerger) where

import TSPLib
import Data.List hiding (insert)
import Data.Function

algNearestMerger :: TSPAlgorithm
algNearestMerger ns = pathToEdges ns


select :: [Path] -> ((Node, Node), (Path, Path))
select ps = minimumBy (compEdgeDist `on` fst)
            [((n,m), (ns, ms)) |
             ns <- ps,
             n  <- ns,
             ms <- ps,
             ms /= ns,
             m  <- ms]


insert :: [Path] -> ((Node, Node), (Path, Path)) -> [Path]
insert []       _      = []
insert (p:q:rs) a@((n,m), (p',q'))
  | p == p' && q == q' = undefined
  | otherwise          = p : insert (q:rs) a

connect :: (Path, Path) -> (Node, Node) -> Path
connect (p, q) (n, m) =
  let (p1,p2) = p `splitOn` n
      (q1,q2) = q `splitOn` r
  in undefined


splitOn :: Path -> Edge -> Path
splitOn (p:q:rs) (n,m)
  | p == n && q == m = rs
  | p == m && q == n = rs
  | otherwise        = splitOn ((q:rs) ++ [p]) (n,m)
splitOn


splitOn :: Path -> Node -> ((Path, Path), [Edge])
splitOn []    _ = ([], [])
splitOn (n:p) n'
  | n == n'     = (([], p),
  | otherwise   = let ((l,r), e) = splitOn p n'
                  in  ((n' : l, r), e)
