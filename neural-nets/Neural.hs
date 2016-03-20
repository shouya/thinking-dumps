import System.Random
import Data.Vector


data Network = Network
  { layers :: [Int]
  , biases :: [Vector Float]
  , weights :: [Vector (Vector Float)]
  }



createNetwork :: [Int] -> IO Network
createNetwork lyrs = do

  Network { layers = lyrs
          , biases = (tail lyrs)
          }
