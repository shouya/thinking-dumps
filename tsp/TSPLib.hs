module TSPLib (
  Node,
  Edge,
  Path,
  TSPAlgorithm,
  distance,
  xRange,
  yRange,
  pathLength,
  edgeLength,
  pathToEdges,
  tracePath,
  tracePath',
  replace,
  compEdgeDist,
  nearestEdgeTo,
  furthestEdgeTo,
  findEnds,
  wrapEnds,
  wrapPathEnds,
  tupleFromIntegral,
  convexHull,
  insertBetween,
  trigCartProd,
  parseString,
  parseStdin,
  parseFile,
  outputForGraph
  ) where

import Data.Functor
import Data.Function
import Data.List
import Control.Arrow ((>>>), (&&&), (***), second)

import Data.Tuple

-- node
type Node = (Int, Int)
type Edge = (Node, Node)
type Path = [Node]

distance :: Node -> Node -> Double
distance (x1,y1) (x2,y2) = sqrt (fromIntegral $ (x2-x1)*(x2-x1) + (y2-y1)*(y2-y1))

xRange  :: [Node] -> (Int, Int)
xRange = (foldl1' min &&& foldl1' max) . map fst
yRange :: [Node] -> (Int, Int)
yRange = (foldl1' min &&& foldl1' max) . map snd


type TSPAlgorithm = [Node] -> [Edge]


pathLength :: Path -> Double
pathLength xs = foldl1' (+) $ zipWith distance (init xs) (tail xs)

edgeLength :: Edge -> Double
edgeLength = uncurry distance

pathToEdges :: Path -> [Edge]
pathToEdges xs = zip (init xs) (tail xs)

tracePath :: [Edge] -> Node -> Path
tracePath [] n = [n]
tracePath es n = case length edges of
                  0 -> [n]
                  1 -> let followingE = head edges
                           nextN      = snd followingE
                           restEdges  = es \\ [followingE, swap followingE]
                       in n : tracePath restEdges nextN
                  _ -> error "more than one choice"
  where edges = filter ((==n) . fst) (es ++ map swap es)


-- this version of trace path follow
tracePath' :: [Edge] -> Node -> Path
tracePath' [] n = [n]
tracePath' es n = case length edges of
                   0 -> [n]
                   _ -> let followingE = head edges
                            nextN      = snd followingE
                            restEdges  = es \\ [followingE, swap followingE]
                        in n : tracePath restEdges nextN
  where edges = filter ((==n) . fst) (es ++ map swap es)


replace :: (Eq a) => a -> [a] -> [a] -> [a]
replace x sub xs = newXs
  where index         = elemIndex x xs
        makeHole i    =  second tail . splitAt i
        connect (a,b) = a ++ sub ++ b
        newXs         = maybe xs (connect . flip makeHole xs) index


compEdgeDist :: Edge -> Edge -> Ordering
compEdgeDist = compare `on` edgeLength

nearestEdgeTo :: Node -> [Node] -> Edge
nearestEdgeTo n ms = (n, minimumBy (compare `on` distance n) ms)

furthestEdgeTo :: Node -> [Node] -> Edge
furthestEdgeTo n ms = (n, maximumBy (compare `on` distance n) ms)

findEnds :: [Edge] -> (Node, Node)
findEnds es = (head &&& last) $ map head $ filter (odd . length) ns'
  where ns  = map fst es ++ map snd es
        ns' = group $ sort ns

wrapEnds :: [Edge] -> [Edge]
wrapEnds [] = []
wrapEnds es = findEnds es : es

wrapPathEnds :: Path -> Path
wrapPathEnds []     = []
wrapPathEnds (x:xs) = (x:xs) ++ [x]

tupleFromIntegral :: (Num c, Num d, Integral a, Integral b) =>
                     (a, b) -> (c, d)
tupleFromIntegral = fromIntegral *** fromIntegral


convexHull :: [Node] -> [Node]
convexHull []  = []
convexHull [x] = [x]
convexHull ns  = lower ++ upper
  where sorted = sort ns
        lower  = chain sorted
        upper  = chain (reverse sorted)
        chain  = go []
        go (a:b:rs) (x:xs) = if ccw b a x
                             then go (b:rs)     (x:xs)
                             else go (x:a:b:rs) xs
        go rs       (x:xs) = go (x:rs) xs
        go rs       []     = reverse $ tail rs
        ccw (x1,y1) (x2,y2) (x3,y3) = (x2-x1)*(y3-y1) - (y2-y1)*(x3-x1) <= 0

insertBetween :: Path -> Node -> Node -> Node -> Path
insertBetween []       _ _ _ = []
insertBetween [a]      _ _ _ = [a]
insertBetween (a:b:xs) p q n
  | a == p && b == q = a : n : b : xs
  | otherwise        = a : insertBetween (b:xs) p q n


combinations :: Int -> [a] -> [[a]]
combinations 0 _  = [[]]
combinations n xs = [ y:ys | y:xs' <- tails xs
                           , ys <- combinations (n-1) xs']

trigCartProd :: [a] -> [(a,a)]
trigCartProd = map (head &&& last) . combinations 2

parseString :: String -> [Node]
parseString =
  lines >>>
  filter (not . ("#" `isPrefixOf`)) >>>
  filter (not . null) >>>
  map words >>>
  map (map read) >>>
  filter (\x -> length x == 2) >>>
  map (\[a,b] -> (a,b))


parseStdin :: IO [Node]
parseStdin = parseString <$> getContents

parseFile :: FilePath -> IO [Node]
parseFile path = parseString <$> readFile path


outputForGraph :: [Node] -> [Edge] -> IO ()
outputForGraph ns es = do
  putStrLn $ show (length ns) ++ " " ++ show (length es)
  mapM_ (putStrLn . showNode) ns
  mapM_ (putStrLn . showEdge) es
  where showNode (a,b) = show a ++ " " ++ show b
        showEdge ((a,b),(c,d)) = show a ++ " " ++ show b ++ " " ++
                                 show c ++ " " ++ show d

main :: IO ()
main = parseStdin >>= flip outputForGraph []
