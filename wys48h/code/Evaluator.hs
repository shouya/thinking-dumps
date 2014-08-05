
import Parser

import System.Environment (getArgs)
import Control.Monad (liftM)

instance Show LispVal where
  show (String xs) = show xs
  show (Identifier x) = x
  show (Number x) = show x
  show (Float x) = show x
  show (Character x) = "#\\" ++ [x]
  show (Rational p q) = show p ++ "/" ++ show q
  show (Complex r i) = show r ++ (if i < 0 then "-" else "+") ++
                       show (abs i) ++ "i"
  show (Bool True) = "#t"
  show (Bool False) = "#f"
  show (List xs) =  "(" ++ unwordsList xs ++ ")"
  show (DottedList xs t) = "(" ++ unwordsList xs ++ " . " ++ show t ++ ")"

unwordsList :: [LispVal] -> String
unwordsList = unwords . map show






eval :: LispVal -> LispVal
eval val@(String _) = val
eval val@(Number _) = val
eval val@(Bool _) = val
eval (List [Identifier "quote", val]) = val












testShow :: String -> IO ()
testShow code = putStrLn $ case parseLispVal code of
    Left err -> "error: " ++ show err
    Right x  -> "showing: " ++ show x

testEval :: String -> IO ()
testEval code = putStrLn $ case parseLispVal code of
    Left err -> "error parsing: " ++ show err
    Right x  -> "eval result: " ++ show (eval x)

main :: IO ()
main = getArgs >>= testShow . head
