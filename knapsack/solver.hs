import System.IO
import Data.List
import Data.Function
import Data.Monoid
import Control.Applicative
import Control.Monad
import Control.Monad.Writer

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
--  interact (output . solve . load)
--  interact (show . (fst . runWriter . solve) . load)
  getContents >>= execution . runWriter . solve . load
  where execution = debugProgram

debugProgram :: ((Integer, Solution), [String]) -> IO ()
debugProgram result = do
  putStrLn "Calculated result"
  putStrLn $ output $ fst result

  putStrLn "----------\nItems taken"
  putStrLn $ showItems $ reverse $ snd $ fst result

  putStrLn "----------\nLogs"
  putStrLn $ showLog log
  where log = snd result

formalProgram :: ((Integer, Solution), [String]) -> IO ()
formalProgram result = do
  putStrLn $ output $ fst result


solve :: (Weight, [Item]) -> Writer [String] (Integer, Solution)
solve (w, items) = writer ((len, fst result), snd result)
  where algorithm = greedyDensity                --- change algorithm here
        len = fromIntegral $ length items
        result = runWriter $ algorithm w items

load :: String -> (Weight, [Item])
load str = (weight, items')
  where lns = lines str
        weight = read $ head . tail $ words $ head lns
        items  = map (map read . words) $ tail lns
        items' = zip [0..] $ zip (map (head . tail) items) (map head items)


output :: (Integer, Solution) -> String
output (len, xs) = show value ++ " 1\n" ++ unwords (map show bitset)
  where value = foldl1 (+) $ map itemvalue xs
        ids = map itemid xs
        bitset = map (bool2int . (`elem` ids)) [0..(len-1)]
        bool2int x
          | x == True  = 1
          | x == False = 0

showLog :: [String] -> String
showLog = concat . intersperse "\n"

showItem x =
  (show $ itemid x) ++
  ": w " ++ (show $ itemweight x) ++
  ", v " ++ (show $ itemvalue x)
showItems = concat . intersperse "\n" . map showItem

---------------- Main Part ----------------

{-
   Solution 1: greedy
-}
greedy :: (Item -> Item -> Ordering) -> Weight -> [Item] ->
          Writer [String] Solution
greedy f w items = do
  tell $ [showItems sortedItem]
  return $ takeItem w sortedItem []
  where
    sortedItem = sortBy f items
    takeItem _     []     carry = carry
    takeItem wleft (i:is) carry =
      if itemweight i <= wleft
      then takeItem (wleft - (itemweight i)) is (i:carry)
      else takeItem wleft is carry


greedyValue = greedy $ flip (compare `on` itemvalue)
greedyNumber = greedy (compare `on` itemweight)
greedyDensity = greedy $ flip $ (compare `on` \x ->
                                  (fromIntegral $ itemvalue x) /
                                  (fromIntegral $ itemweight x))


{-
    Solution 2: dynamic programming
-}

type ValueList = [Value]

dp :: [Item] -> Writer [String] Solution
dp items = writer [] $ foldl dpstep (replicate (length items) 0) items

dpstep :: ValueList -> Item -> ValueList
dpstep xs i =
  map newval xs'
  where wi = itemweight i
        vi = itemvalue i
        xs' = zip [0..] xs
        newval (idx,x) =
          if idx < wi then x
          else max x (vi + xs !! (fromIntegral (idx - wi)))
