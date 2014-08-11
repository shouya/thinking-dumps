
module REPL where

import System.IO
import System.Environment

import Control.Monad (liftM, join)

import Evaluator
import Error
import Parser


flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout


readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

evalString :: Env -> String -> IO String
evalString env expr = runIOThrows $ (evalCode env expr >>= return . show)

evalAndPrint :: Env -> String -> IO ()
evalAndPrint env expr = join $ liftM putStrLn $ evalString env expr


until_ :: Monad m => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ pred prompt action = do
  result <- prompt
  if pred result
    then return ()
    else action result >> until_ pred prompt action

runRepl :: IO ()
runRepl = primitiveEnv >>= until_ (== "quit") (readPrompt "> ") . evalAndPrint

main :: IO ()
main = do args <- getArgs
          case length args of
            0 -> runRepl
            1 -> primitiveEnv >>= flip evalAndPrint (head args)
            otherwise -> putStrLn "program takes 0 or 1 argument."
