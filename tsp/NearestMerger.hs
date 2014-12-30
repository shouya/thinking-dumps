module NearestMerger (algNearestMerger) where

import TSPLib
import Data.List hiding (insert)
import Data.Function

import Test.QuickCheck
import Debug.Trace

algNearestMerger :: TSPAlgorithm
algNearestMerger ns = pathToEdges $ roundPath $ recur init'
  where init'     = map (:[]) ns
        recur [x] = x
        recur ps  = let sel   = select ps
                        newPs = insert ps sel
                    in recur newPs


select :: [Path] -> ((Node, Node), (Path, Path))
select ps = minimumBy (compEdgeDist `on` fst)
            [((n,m), (ns, ms)) |
             (ns, ms) <- trigCartProd ps,
             n <- ns,
             m <- ms]

insert :: [Path] -> ((Node, Node), (Path, Path)) -> [Path]
insert [] _ = error "wtf?"
insert ps ((n,m),(p,q)) = merged : restPaths
  where restPaths = ps \\ [p,q]
        merged    = merge (p,q) (n,m)


merge :: (Path, Path) -> (Node, Node) -> Path
merge ([p],[q]) (_,_) = mergeSingletons p q
merge ([p], qs) (_,n) = mergeOne qs n p
merge (ps, [q]) (m,_) = mergeOne ps m q
merge (ps, qs)  (m,n) = mergeFull (ps,qs) (m,n)


mergeSingletons :: Node -> Node -> Path
mergeSingletons n m = [n, m]

mergeOne :: Path -> Node -> Node -> Path
mergeOne p n m = stripPath $ insertBetween (roundPath p) n n' m
  where neighbors = tupleToList $ getNeighbors p n
        n'        = minimumBy (compare `on` distance m) neighbors


mergeFull :: (Path, Path) -> (Node, Node) -> Path
mergeFull (p, q) (i, j) = resultP
  where delta (k,l) = distance i j + distance k l -
                      distance i k - distance j l
        tToL (a,b)  = [a,b]
        (iNB, jNB)  = (tToL $ getNeighbors p i,
                       tToL $ getNeighbors q j)
        candidates  = [(k,l)
                      | k <- iNB
                      , l <- jNB
                      ]
        (k',l')     = minimumBy (compare `on` delta) candidates
        (p',q')     = (roundPath p, roundPath q)
        resultP     = mergePaths p' q' (i,k') (j,l')


main :: IO ()
main = do
--  quickCheck (splitOn [(1,2),(2,3),(3,4)] (1,2) == [3])
  let n1 = (1,1)
      n2 = (2,2)
      p1 = [n1]
      p2 = [n2]
      pths = [p1,p2]
      sel  = ((n1,n2),(p1,p2))
  quickCheck (select pths == sel)
  quickCheck (insert pths sel == [[n1,n2]] ||
              insert pths sel == [[n2,n1]])
