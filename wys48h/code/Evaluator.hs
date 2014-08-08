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
    Bool True  -> eval cons
    Bool False -> eval alt
    x        -> throwError $ TypeMismatch "boolean" x  -- Exercise 4/1

{- ex 4/3 -}
eval (List [Identifier "cond"]) = throwError $ Default "Missing clauses (cond)"
eval (List (Identifier "cond" : xs)) = evalCondClauses xs

{-
eval
eval (List ((Identifier "cond"):x:xs)) =
-}

eval (List ((Identifier "progn"):xs)) = evalProgn xs


eval (List (Identifier func : args)) = mapM eval args >>= apply func
eval x = throwError $ BadSpecialForm "Unrecognized Special Form" x



apply :: String -> [LispVal] -> ThrowError LispVal
apply func args = case lookup func primitives of
  Just f  -> f args
  Nothing -> throwError $ NotFunction "Unrecognized primitive function" func


evalProgn :: [LispVal] -> ThrowError LispVal
evalProgn = foldl (\c x -> c >> eval x) (return $ List [])

evalCondClauses :: [LispVal] -> ThrowError LispVal
evalCondClauses [] = return $ List []
evalCondClauses (List (Identifier "else" : Identifier "=>" : [x]):_) = eval x
evalCondClauses (List (Identifier "else" : xs):_) = evalProgn xs
evalCondClauses (List (cond : Identifier "=>" : [x]) : rest) =
  eval cond >>= \result -> case result of
    Bool True  -> eval x
    Bool False -> evalCondClauses rest
    x          -> throwError $ TypeMismatch "boolean" x

evalCondClauses (List (cond : xs) : rest) =
  eval cond >>= \result -> case result of
    Bool True  -> evalProgn xs
    Bool False -> evalCondClauses rest
    x          -> throwError $ TypeMismatch "boolean" x
evalCondClauses x = throwError $ BadSpecialForm "Unrecognized Special Form"
                                                (List x)

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
