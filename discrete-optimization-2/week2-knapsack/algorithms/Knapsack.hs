{-# LANGUAGE NamedFieldPuns #-}

module Knapsack where

import Control.Monad (forM_)

import Data.Array.IArray (elems)
import Data.Array.ST hiding (index)

import System.Environment (getArgs)

type Weight = Int
type Value = Int
type WeightCapacity = Weight

data Optimal = Optimal
             | NotOptimal
  deriving (Eq, Ord)

instance Show Optimal where
  show Optimal = "1"
  show NotOptimal = "0"

data Item = Item { index  :: Int
                 , value  :: Value
                 , weight :: Weight
                 }
  deriving (Show, Eq, Ord)

data Solution = Solution { optimal :: Optimal
                         , objective :: Int
                         , selectedItems :: [Item]
                         , numTotalItems :: Int
                         }
  deriving (Show, Eq, Ord)


solution :: Problem -> [Item] -> Optimal -> Solution
solution Problem { givenItems } selectedItems optimal =
  Solution { optimal, objective, selectedItems, numTotalItems }
  where objective = sum $ fmap value selectedItems
        numTotalItems = length givenItems

data Problem = Problem { capacity :: Weight
                       , givenItems :: [Item]
                       }

type Algorithm = Problem -> Solution


parseProblem :: String -> Problem
parseProblem contents =
  let input = map words $ lines $ contents
      meta = head input
      inputs = tail input
      capacity = read (meta !! 1)
      items = map (\[v,w] -> (v,w)) $ (map . map) read inputs
      groupIntoItem index (value, weight) = Item { index, value, weight }
      givenItems = zipWith groupIntoItem [0..] items
  in Problem { capacity, givenItems }

generateSolution :: Solution -> String
generateSolution Solution { optimal, objective, selectedItems, numTotalItems } = do
  unlines $ [unwords meta, unwords $ map show $ elems $ indexArray]
    where meta = [show objective, show optimal]
          indexArray = runSTUArray $ do
            array <- newArray (0, numTotalItems - 1) 0
            forM_ selectedItems $ \Item { index } -> do
              writeArray array index (1 :: Int)
            return array


solveBy :: Algorithm -> IO ()
solveBy alg = do
  args <- getArgs
  contents <- if null args then getContents else readFile (args !! 0)
  putStr $ generateSolution . alg . parseProblem $ contents
