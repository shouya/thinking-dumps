import Data.List
import Text.Printf

showQueens :: [Int] -> Int -> String
showQueens xs size = intercalate "\n" $ map foo xs
  where foo i = replicate i '.' ++
                "O" ++
                replicate (size - i - 1) '.'


queens :: Int -> [[Int]]
queens size = queenCols size
  where queenCols 0 = [[]]
        queenCols n = let xss = queenCols (n - 1)
                      in [x:xs
                         |x <- [0..size]
                         ,xs <- xss
                         ,rowCheck x xs
                         ,diagCheck x xs]
        rowCheck  x xs = x `notElem` xs
        diagCheck x xs = and $ zipWith notConf (map (subtract x) xs) [1..]
        notConf n m   = n /= -m && n /= m

main :: IO ()
main = mapM_ printQueen (queens size)
  where size = 8
        printQueen q = do
          putStrLn ""
          printf "%s\n" (show q)
          putStrLn $ showQueens q size
