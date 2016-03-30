{-# LANGUAGE RecordWildCards #-}

import Numeric.LinearAlgebra
import Control.Monad (replicateM,sequence)
import Data.Functor ((<$>))
import Data.Random.Normal (normalIO)

type Weights = Vector R
type Bias = R
type NeuronValue = R
type LayerWeights = Matrix R
type LayerBiases = Vector R
type LayerNeuronValues = Vector R

data Network = Network
  { layers :: [Int]
  , biases :: [LayerBiases]
  , weights :: [LayerWeights]
  }


createNetwork :: [Int] -> IO Network
createNetwork lyrs = do
  bs <- sequence [normalVec n | n <- tail lyrs]
  ws <- sequence $ zipWith normalMat (init lyrs) (tail lyrs)
  return $ Network { layers = lyrs
                   , biases = bs
                   , weights = ws
                   }


testNetwork :: Network -> Vector R -> Vector R
testNetwork (Network {..}) input = output
  where output = zipWith3 weights
        vals :: [Vector R]
        vals = [vector $ replicate n 0 | n <- layers]


signalPassLayer :: LayerWeights ->
                   LayerBiases ->
                   LayerNeuronValues ->
                   LayerNeuronValues
signalPassLayer ws bs inputs = ws #> inputs + bs


signalPassNeuron :: Weights -> Bias -> LayerNeuronValues -> NeuronValue
signalPassNeuron ws b inputs = (ws <.> inputs) + b

layers = l : signalPassLayer layers


main :: IO ()
main = do
  return ()


-- random vector
normalVec :: Int -> IO (Vector R)
normalVec n = vector <$> replicateM n normalIO

normalMat :: Int -> Int -> IO (Matrix R)
normalMat m n = (m >< n) <$> replicateM (n*m) normalIO
