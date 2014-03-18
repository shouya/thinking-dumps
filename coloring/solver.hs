import System.IO
import System.Environment
import Data.List
import Data.Array
import Data.Function
import Data.Monoid
import Control.Applicative
import Control.Monad
import Control.Monad.Writer
import Control.Category

main :: IO ()
main = load >>= \txt ->
       output (parse txt >>= solve)

load :: IO String
load = do
  getArgs >>= \args ->
      case args of
        []  -> getContents
        [f] -> withFile f ReadMode $ \h -> hGetContents h

type Node  = Integer
type Color = Integer
data Input  = Input { numNodes  :: Integer
                    , nodeEdges :: Array Node (Node, [Node])
                    }
data Solution = Solution { numColors  :: Integer
                         , nodeColors :: [Color]
                         }

parse :: String -> Writer [String] Input
parse x = undefined

solve :: Input -> Writer [String] Solution
solve x = undefined

output :: Writer [String] Solution -> IO ()
output x = undefined
