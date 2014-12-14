module TSPLib where

import Data.Functor
import Data.List
import Control.Monad
import Control.Arrow ((>>>))


-- node
type Node = (Int, Int)
type Edge = (Node, Node)

distance :: Node -> Node -> Double
distance (x1,y1) (x2,y2) = sqrt (fromIntegral $ (x2-x1)*(x2-x1) + (y2-y1)*(y2-y1))



parseString :: String -> [Node]
parseString =
  lines >>>
  filter (not . ("#" `isPrefixOf`)) >>>
  filter (not . null) >>>
  map words >>>
  map (map read) >>>
  filter (\x -> length x /= 2) >>>
  map (\[a,b] -> (a,b))


parseStdin :: IO [Node]
parseStdin = parseString <$> getContents

parseFile :: FilePath -> IO [Node]
parseFile path = parseString <$> readFile path
