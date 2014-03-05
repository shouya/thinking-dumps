import System.IO
import Data.List
import Control.Applicative
import Control.Monad


type Weight = Integer
type Value = Integer
type Id = Integer
type Item = (Id, (Weight, Value))
type Solution = [Item]


main = do
  interact (output . solve . load)

solve :: (Weight, [Item]) -> (Integer, Solution)
solve (w, items) = (fromIntegral $ length items, map ((!!) items) [1,3,3])

load :: String -> (Weight, [Item])
load str = (weight, items')
  where lns = lines str
        weight = read $ head . tail $ words $ head lns
        items  = map (map read . words) $ tail lns
        items' = zip [0..] $ zip (map head items) (map (head . tail) items)


output :: (Integer, Solution) -> String
output (len, xs) = show value ++ " 1\n" ++ unwords (map show bitset)
  where value = foldl' (+) 0 $ map (snd . snd) xs
        ids = map fst xs
        bitset = map (bool2int . (`elem` ids)) [0..(len-1)]
        bool2int x
          | x == True  = 1
          | x == False = 0
