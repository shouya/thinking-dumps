module TestAlgorithm where

import TSPLib
import TSPGraph

import NearestNeighbor

import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as M
import System.Environment


defaultAlg :: String
defaultAlg = "NearestNeighbor"

algorithms :: Map String TSPAlgorithm
algorithms = M.fromList
             [("NearestNeighbor", algNearestNeighbor)
             ]

main :: IO ()
main = do
  args  <- getArgs
  nodes <- parseStdin
  let alg = case args of
        []  -> fromMaybe (error "failed") $ M.lookup defaultAlg algorithms
        [x] -> fromMaybe (error $ show x ++ " algorithm not found") $
               M.lookup x algorithms
      edges = playAlg alg nodes
    in do print $ sum $ map (uncurry distance) edges
          present nodes edges


playAlg :: TSPAlgorithm -> [Node] -> [Edge]
playAlg = id

present :: [Node] -> [Edge] -> IO ()
present = presentUI
