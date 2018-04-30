{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

import Knapsack

import System.Process
import System.IO.Temp
import Data.List
import Text.Printf

zincFile = "builtin.mzn"

minizincAlg :: Problem -> IO String
minizincAlg prob@Problem { capacity, givenItems } = do
  inputFileName <- generateInputFile prob
  -- putStrLn $ unwords ["mzn-cbc", zincFile, inputFileName]
  zincOutput <- readProcess "mzn-cbc" [zincFile, inputFileName] ""
  transformOutput zincOutput


generateInputFile :: Problem -> IO FilePath
generateInputFile Problem { capacity, givenItems } = do
  let weights = intercalate "," $ map (show . weight) givenItems
      values = intercalate "," $ map (show . value) givenItems
      contents = unlines [ printf "n = %d;" (length givenItems)
                         , printf "k = %d;" capacity
                         , printf "ws = [%s];" weights
                         , printf "vs = [%s];" values
                         ]
  writeSystemTempFile "knapsack.dzn" contents


transformOutput :: String -> IO String
transformOutput output = return (unlines $ take 2 $ lines output)


main :: IO ()
main = ioSolveBy minizincAlg
