module NearestMerger (algNearestMerger) where

import TSPLib
import Data.List hiding (insert)
import Data.Function

algNearestMerger :: TSPAlgorithm
algNearestMerger ns = pathToEdges $ recur init
  where init      = map return ns :: [Path]
        recur [x] = x
        recur ps  = let sel   = select ps
                        newPs = insert ps sel
                    in recur newPs


select :: [Path] -> ((Node, Node), (Path, Path))
select ps = minimumBy (compEdgeDist `on` fst)
            [((n,m), (ns, ms)) |
             (ns, ms) <- trigCartProd ps,
             n  <- ns,
             m  <- ms]

insert :: [Path] -> ((Node, Node), (Path, Path)) -> [Path]
insert [] _ = []
insert ps ((n,m),(p,q)) = merged : restPaths
  where restPaths = ps \\ [p,q]
        merged    = merge (p,q) (n,m)


merge :: (Path, Path) -> (Node, Node) -> Path
merge (p, q) (i, j) = resultP
  where delta (k,l) = distance i k + distance j l -
                      distance i j - distance k l
        candidates  = [(k,l) | k <- p, k /= i, l <- q, l /= j]
        (k',l')     = minimumBy (compare `on` delta) candidates
        (p',q')     = (splitOn (tail p) (i,k'), splitOn (tail q) (j,l'))
        resultP     = p' ++ q'


splitOn :: Path -> Edge -> Path
splitOn []       _   = []
splitOn [x]      _   = [x]
splitOn (p:q:rs) (n,m)
  | p == n && q == m = rs
  | p == m && q == n = rs
  | otherwise        = splitOn ((q:rs) ++ [p]) (n,m)
