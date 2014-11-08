module DFSTest where

import DFS
import GenericGraph hiding (edges, bounds)
import Control.Monad (liftM2)
import Test.QuickCheck



{-
exampleGraph:

  +-1--2--3--4
  +-+   \    |
         ----5

-}

edges :: [Edge Int]
edges = [(1,2), (2,3), (2,5), (3,4), (4,5)]

bounds :: Bounds Int
bounds = liftM2 (,) (foldl1 min) (foldl1 max) $
         (map fst edges) ++ (map snd edges)

exampleGraph :: Graph Int
exampleGraph = buildG bounds (edges ++ rev edges)
  where rev      = map (\(a,b) -> (b,a))


prop_SearchEqvTraverse :: Property
prop_SearchEqvTraverse =
  forAll inBounds $ \beg ->
  forAll inBounds $ \end ->
  let sResult = dfsSearch exampleGraph beg end
      tResult = dfsTraverse exampleGraph beg
  in sResult == (takeWhile (/=end) tResult) ++ [end]
  where inBounds = choose bounds


main :: IO ()
main = do quickCheck (dfsTraverse exampleGraph 1 == [1..5])
          quickCheck (dfsTraverse exampleGraph 2 == [2,1,3,4,5])
          quickCheck (dfsTraverse exampleGraph 3 == [3,2,1,5,4])
          quickCheck prop_SearchEqvTraverse
