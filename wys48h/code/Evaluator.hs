module Evaluator where

import Parser
import Primitive
import Error

import System.Environment (getArgs)
import Control.Monad (liftM)





eval :: LispVal -> ThrowError LispVal
eval val@(String {}) = return val
eval val@(Number {}) = return val
eval val@(Float {}) = return val
eval val@(Rational {}) = return val
eval val@(Complex {}) = return val
eval val@(Bool {}) = return val

eval (List [Identifier "quote", val]) = return val
eval (List [Identifier "if", cond, cons, alt]) =
  eval cond >>= \result -> case result of
    (Bool b) -> eval (if b then cons else alt)
    x        -> throwError $ TypeMismatch "boolean" x  -- Exercise 4/1


eval (List (Identifier func : args)) = mapM eval args >>= apply func
eval x = throwError $ BadSpecialForm "Unrecognized Special Form" x


apply :: String -> [LispVal] -> ThrowError LispVal
apply func args = case lookup func primitives of
  Just f  -> f args
  Nothing -> throwError $ NotFunction "Unrecognized primitive function" func




evalCode :: String -> ThrowError LispVal
evalCode code = case parseLispVal code of
  Left err  -> throwError $ Parser err
  Right val -> eval val


testShow :: String -> IO ()
testShow code = putStrLn $ case parseLispVal code of
    Left err -> "error: " ++ show err
    Right x  -> "showing: " ++ show x

testEval :: String -> IO ()
testEval code = putStrLn $ case evalCode code of
    Left err -> "error: " ++ show err
    Right x  -> "eval result: " ++ show x

main :: IO ()
main = getArgs >>= testEval . head
