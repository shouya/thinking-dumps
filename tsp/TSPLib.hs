module TSPLib (
  Node,
  Edge,
  distance,
  xRange,
  yRange,
  parseString,
  parseStdin,
  parseFile,
  outputForGraph
  ) where

import Data.Functor
import Data.List
import Control.Monad
import Control.Applicative ((<*>), (<$>))
import Control.Arrow ((>>>), (&&&))


-- node
type Node = (Int, Int)
type Edge = (Node, Node)

distance :: Node -> Node -> Double
distance (x1,y1) (x2,y2) = sqrt (fromIntegral $ (x2-x1)*(x2-x1) + (y2-y1)*(y2-y1))

xRange  :: [Node] -> (Int, Int)
xRange = map fst >>> (foldl1' min &&& foldl1' max)
yRange :: [Node] -> (Int, Int)
yRange = map fst >>> (foldl1' min &&& foldl1' max)


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
