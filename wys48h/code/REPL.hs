
module REPL where

import System.IO
import System.Environment

import Control.Monad (liftM)

import Evaluator
import Error
import Parser


flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout


readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

evalString :: String -> IO String
evalString expr = return $ extractValue $
                  trapError (liftM show $ evalCode expr)

evalAndPrint :: String -> IO ()
evalAndPrint expr = evalString expr >>= putStrLn

until_ :: Monad m => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ pred prompt action = do
  result <- prompt
  if pred result
    then return ()
    else action result >> until_ pred prompt action

runRepl :: IO ()
runRepl = until_ (== "quit") (readPrompt "> ") evalAndPrint

main :: IO ()
main = do args <- getArgs
          case length args of
            0 -> runRepl
            1 -> evalAndPrint (head args)
            otherwise -> putStrLn "program takes 0 or 1 argument."
