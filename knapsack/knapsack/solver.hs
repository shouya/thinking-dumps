import System.IO
import System.Environment
import Data.List
import Data.Array
import Data.Function
import Data.Monoid
import Control.Applicative
import Control.Monad
import Control.Monad.Writer


type Array' = Array Integer
alo = fst . bounds
ahi = snd . bounds

foldra :: (a -> b -> b) -> b -> Array' a -> b
foldra f z0 ar = go (alo ar)
  where go i
          | i > ahi ar = z0
          | otherwise = f (ar ! i) (go (i + 1))

foldla :: (b -> a -> b) -> b -> Array' a -> b
foldla f z0 ar = go z0 (alo ar)
  where go z i
          | i > ahi ar = z
          | otherwise = go (f z (ar ! i)) (i + 1)

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

emptyitem :: Item
emptyitem = (0,(0,0))

main = do
--  interact (output . solve . load)
--  interact (show . (fst . runWriter . solve) . load)
  inputfile <- getArgs >>= return . head
  withFile inputfile ReadMode $
    (\f -> hGetContents f >>= execution . runWriter . solve . load)
  where execution = formalProgram

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
  where algorithm = dp                --- change algorithm here
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

type ValueList = Array' Value

dp :: Weight -> [Item] -> Writer [String] Solution
dp w items = do
--  tell $ [foldl showtable "" table]
  return $ reverse result
  where firstcol = listArray (0,w) $ genericReplicate (w + 1) 0
        table = calctable firstcol (emptyitem:items)
        zippedtbl = zip (emptyitem:items) table
        foldrX = (([], w), last zippedtbl)
        result = fst $ fst $ foldr dptrace foldrX zippedtbl

showtable :: String -> ValueList -> String
showtable l x = l ++ "\n" ++ concat (intersperse " " [show (x ! i) | i <- [0..ahi x]])

dptrace :: (Item,ValueList) -> (([Item], Integer), (Item, ValueList)) ->
           (([Item], Integer), (Item, ValueList))
dptrace (iy,ys) ((result, w), (ix,xs))
  | xs ! w == ys ! w   = ((result, w), (iy,ys))
  | otherwise          = ((ix:result, w - itemweight ix), (iy,ys))


{-
calctable :: ValueList ->
             [Item] ->    -- items to be taken
             [Item] ->    -- item list
calctable _  _   []     = []
calctable xs (i:is) = if itemtaken then i:following else following
  where following = calctable newval is
        newval = listArray (0,ahi xs) [helper i (xs!i) | i <- [0..ahi xs]]
-}

calctable :: ValueList -> [Item] -> [ValueList]
calctable _ []      = []
calctable xs (i:is) = newval:(calctable newval is)
  where (wi,vi) = (itemweight i, itemvalue i)
        newval = listArray (0,ahi xs) [helper i (xs!i) | i <- [0..ahi xs]]
        helper idx x
          | idx < wi = x
          | otherwise = max x (vi + xs ! (idx - wi))

{-

-}
