import qualified Data.Vector as V
import Data.Vector (Vector)
import Control.Monad (replicateM,sequence)
import Data.Functor ((<$>))
import System.Random (randomIO)


data Network = Network
  { layers :: [Int]
  , biases :: [Vector Float]
  , weights :: [Vector (Vector Float)]
  }



createNetwork :: [Int] -> IO Network
createNetwork lyrs = do
  bs <- sequence [randomVector l | l <- tail lyrs]
  ws <- sequence $ zipWith randomVector2 (init lyrs) (tail lyrs)
  return $ Network { layers = lyrs
                   , biases = bs
                   , weights = ws
                   }


main :: IO ()
main = do
  return ()


-- random vector
randomVector :: Int -> IO (Vector Float)
randomVector n = V.fromList <$> replicateM n randomIO

randomVector2 :: Int -> Int -> IO (Vector (Vector Float))
randomVector2 m n = V.fromList <$> replicateM m (randomVector n)
