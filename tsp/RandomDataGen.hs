{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module RandomDataGen where

import TSPLib

import Control.Arrow
import System.Random
import System.Environment

instance Random Node where
  randomR (lo,hi) g = let (x, g')  = randomR (fst lo, fst hi) g
                          (y, g'') = randomR (snd lo, snd hi) g'
                      in ((x,y), g'')
  random g = let (x, g')  = random g
                 (y, g'') = random g'
             in ((x,y), g'')


generateNode :: (RandomGen g) => Node -> g -> (Node, g)
generateNode rng = randomR ((0,0),rng)

genRandomNodes :: (RandomGen g) => (Int, Int) -> Int -> g -> ([Node], g)
genRandomNodes rng 1 g = first return $ generateNode rng g
genRandomNodes rng n g = (node : tail', g'')
  where nodes = iterate (generateNode rng . snd) (generateNode rng g')
        (node, g'') = head $ filter ((`notElem` tail') . fst) nodes
        (tail', g') = genRandomNodes rng (n - 1) g


nodeToStr :: Node -> String
nodeToStr (x,y) = show x ++ " " ++ show y


main :: IO ()
main = do
  args <- getArgs
  gen  <- newStdGen
  let [xrng, yrng, num] = map read args
      nodes = genRandomNodes (xrng, yrng) num gen
    in mapM_ (putStrLn . nodeToStr) (fst nodes)
