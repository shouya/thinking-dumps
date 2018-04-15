{-# LANGUAGE NamedFieldPuns #-}

module Knapsack where

import System.Environment

type Weight = Int
type Value = Int
type WeightCapacity = Int

data Solution = Solution { optimal :: Bool
                         , objective :: Int
                         , selectedItems :: [Int]
                         }

data Problem = Problem { capacity :: Weight
                       , items :: [(Value, Weight)]
                       }

type Algorithm = Problem -> Solution


parseProblem :: String -> Problem
parseProblem contents =
  let input = map words $ lines $ contents
      meta = head input
      inputs = tail input
      capacity = read (meta !! 1)
      items = map (\[v,w] -> (v,w)) $ (map . map) read inputs
  in Problem { capacity, items }

generateSolution :: Solution -> String
generateSolution Solution { optimal, objective, selectedItems } = do
  unlines $ [unwords meta, unwords $ map show selectedItems]
    where meta = [show objective, if optimal then "1" else "0"]

solve :: Algorithm -> IO ()
solve alg = do
  args <- getArgs
  contents <- if null args then getContents else readFile (args !! 0)
  putStrLn $ generateSolution . alg . parseProblem $ contents
