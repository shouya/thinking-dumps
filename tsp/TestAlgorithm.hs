module TestAlgorithm where

import TSPLib
import TSPGraph

import NearestNeighbor

import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as M
import System.Environment


defaultAlg :: String
defaultAlg = "nearest_neighbor"

algorithms :: Map String TSPAlgorithm
algorithms = M.fromList
             [("nearest_neighbor", algNearestNeighbor)
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
    in present nodes edges


playAlg :: TSPAlgorithm -> [Node] -> [Edge]
playAlg = id

present :: [Node] -> [Edge] -> IO ()
present = presentUI
