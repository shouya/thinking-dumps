import System.IO
import Data.List
import Data.Function
import Control.Applicative
import Control.Monad


type Weight = Integer
type Value = Integer
type Id = Integer
type Item = (Id, (Weight, Value))
type Solution = [Item]


itemvalue :: Item -> Value
itemvalue = snd . snd
itemweight :: Item -> Weight
itemweight = fst . snd
itemid :: Item -> Id
itemid = fst


main = do
  interact (output . solve . load)

solve :: (Weight, [Item]) -> (Integer, Solution)
solve (w, items) = (len, result)
  where algorithm = greedyDensity
        len = fromIntegral $ length items
        result = algorithm w items

load :: String -> (Weight, [Item])
load str = (weight, items')
  where lns = lines str
        weight = read $ head . tail $ words $ head lns
        items  = map (map read . words) $ tail lns
        items' = zip [0..] $ zip (map head items) (map (head . tail) items)


output :: (Integer, Solution) -> String
output (len, xs) = show value ++ " 1\n" ++ unwords (map show bitset)
  where value = foldl1 (+) $ map itemvalue xs
        ids = map itemid xs
        bitset = map (bool2int . (`elem` ids)) [0..(len-1)]
        bool2int x
          | x == True  = 1
          | x == False = 0




---------------- Main Part ----------------

{-
   Solution 1: greedy
-}
greedy :: (Item -> Item -> Ordering) -> Weight -> [Item] -> Solution
greedy f w items = takeItem w items []
  where
    sortedItem = sortBy f items
    takeItem _     []     carry = carry
    takeItem wleft (i:is) carry =
      if itemweight i < wleft
      then takeItem (wleft - (itemweight i)) is (i:carry)
      else takeItem wleft is carry


greedyValue = greedy $ flip (compare `on` itemvalue)
greedyNumber = greedy (compare `on` itemweight)
greedyDensity = greedy $ flip $ (compare `on` \x ->
                                  (fromIntegral $ itemvalue x) /
                                  (fromIntegral $ itemweight x))
