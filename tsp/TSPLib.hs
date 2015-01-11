{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE FlexibleInstances #-}

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
  tracePath1,
  tracePath1',
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
  combinations,
  trigCartProd,
  PathRing,
  pathToRing,
  ringToPath,
  ringInsertBefore,
  getRingNeighbors,
  getNeighbors,
  mergeRings,
  mergePaths,
  rotateRingTo,
  reverseRing,
  roundPath,
  stripPath,
  tupleToList,
  deleteEdge,
  traceEdges,
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

import Debug.Trace

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
pathToEdges [] = []
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

tracePath1 :: [Edge] -> Path
tracePath1 es = tracePath es (fst $ head es)


-- this version of trace path follow
tracePath' :: [Edge] -> Node -> Path
tracePath' [] n = [n]
tracePath' es n = case length edges of
                   0 -> [n]
                   _ -> let followingE = head edges
                            nextN      = snd followingE
                            restEdges  = es \\ [followingE, swap followingE]
                        in n : tracePath' restEdges nextN
  where edges = filter ((==n) . fst) (es ++ map swap es)

tracePath1' :: [Edge] -> Path
tracePath1' es = tracePath' es (fst $ head es)


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
  | (a == p && b == q) ||
    (a == q && b == p) =  a : n : b : xs
  | otherwise          =  a : insertBetween (b:xs) p q n


combinations :: Int -> [a] -> [[a]]
combinations 0 _  = [[]]
combinations n xs = [ y:ys | y:xs' <- tails xs
                           , ys <- combinations (n-1) xs']

trigCartProd :: [a] -> [(a,a)]
trigCartProd = map (head &&& last) . combinations 2


data PathRing = PathRing {
  prLength :: Int,
  prPath   :: Path
  }

pathToRing :: Path -> PathRing
pathToRing p = PathRing { prLength = length p, prPath = cycle p }

ringToPath :: PathRing -> Path
ringToPath PathRing {..} = take prLength prPath

getRingNeighbors :: PathRing -> Node -> (Node, Node)
getRingNeighbors PathRing {..} n = foo prPath
  where foo (a:b:c:ns) = if n == b then (a,c) else foo (b:c:ns)
        foo _          = error "invalid input"

getNeighbors :: Path -> Node -> (Node, Node)
getNeighbors p n = foo $ concat $ replicate 2 p
  where foo (a:b:c:xs) = if b == n then (a,c) else foo (b:c:xs)


ringInsertBefore :: PathRing -> Node -> [Node] -> PathRing
ringInsertBefore PathRing {..} n ns = PathRing { prLength = newPrLength
                                               , prPath   = newPrPath
                                               }
  where newPrLength = prLength + length ns
        newPrPath   = foo prPath
        foo (a:as)  = if a == n
                      then cycle $ ns ++ [a] ++ take (prLength - 1) as
                      else foo as
        foo _       = error "invalid input"

reverseRing :: PathRing -> PathRing
reverseRing = pathToRing . reverse . ringToPath

rotateRingTo :: PathRing -> Node -> PathRing
rotateRingTo PathRing {..} n = PathRing { prLength = prLength
                                        , prPath   = dropWhile (/= n) prPath
                                        }

mergeRings :: PathRing -> PathRing -> (Node, Node) -> (Node, Node) -> PathRing
mergeRings pr qr pe qe = newPr
  where newPr     = ringInsertBefore pr (fst pe) (ringToPath rotatedQr)
        rotatedQr = reverseRing $ rotateRingTo qr (snd qe)

deleteEdge :: [Edge] -> Edge -> [Edge]
deleteEdge [] _ = []
deleteEdge ((a,b):xs) (c,d)
  | a == c && b == d = xs
  | a == d && b == c = xs
  | otherwise        = (a,b) : deleteEdge xs (c,d)


stripPath :: Path -> Path
stripPath [] = []
stripPath (x:xs) = if last xs == x then xs else x:xs

mergePaths :: Path -> Path -> Edge -> Edge -> Path
mergePaths p1 p2 e1 e2 = rsltP
  where p1'   = deleteEdge (pathToEdges p1) e1
        p2'   = deleteEdge (pathToEdges p2) e2
        newEs = [(fst e1, fst e2), (snd e1, snd e2)]
        rslt  = newEs ++ p1' ++ p2'
        rsltP = stripPath $ tracePath' rslt (fst e1)


roundPath :: Path -> Path
roundPath []     = error "wrong path input"
roundPath (x:xs) = (x:xs) ++ [x]

tupleToList :: (a,a) -> [a]
tupleToList (a,b) = [a,b]

dumpEdges :: [Edge] -> String
dumpEdges es = intercalate "\n" (map showEdge es) ++ "\n"
  where showEdge ((a,b), (c,d)) = show a ++ " " ++ show b ++ " " ++
                                  show c ++ " " ++ show d

dumpNodes :: [Node] -> String
dumpNodes ns = intercalate "\n" (map showNode ns) ++ "\n"
  where showNode (a,b) = show a ++ " " ++ show b

extractNodes :: [Edge] -> [Node]
extractNodes = concatMap tupleToList

traceEdges :: [Edge] -> [Edge]
traceEdges es = trace content es
  where prefix  = show (length nodes) ++ " " ++ show (length es) ++ "\n"
        suffix  = "\n"
        content = prefix ++ dumpNodes nodes ++ dumpEdges es ++ suffix
        nodes   = nub $ extractNodes es

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
