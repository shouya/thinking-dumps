module Evaluator (eval
                 ,apply
                 ,evalCode) where

import Parser
import Primitive
import Error

import System.Environment (getArgs)
import Control.Monad (liftM)
import Control.Monad.State.Lazy
import Data.IORef


type Env = IORef [(String, IORef LispVal)]


nullEnv :: IO Env
nullEnv = newIORef []

eval :: Env -> LispVal -> IOThrowError LispVal
eval _ val@(String {}) = return val
eval _ val@(Number {}) = return val
eval _ val@(Float {}) = return val
eval _ val@(Rational {}) = return val
eval _ val@(Complex {}) = return val
eval _ val@(Bool {}) = return val

eval _ (List [Identifier "quote", val]) = return val
eval e (List [Identifier "if", cond, cons, alt]) =
  eval e cond >>= \result -> case result of
    Bool True  -> eval e cons
    Bool False -> eval e alt
    x        -> throwError $ TypeMismatch "boolean" x  -- Exercise 4/1

{- ex 4/3 -}
eval _ (List [Identifier "cond"]) = throwError $ Default "Missing clauses (cond)"
eval e (List (Identifier "cond" : xs)) = evalCondClauses e xs
{- ex 4/3 -}
eval _ (List [Identifier "case", _]) =
  throwError $ Default "Missing clauses (case)"
eval _ (List [Identifier "case"]) = throwError $ Default "Missing clauses (case)"
eval e (List (Identifier "case" : x : cs)) = do val <- eval e x
                                                evalCaseClauses e val cs

{-
eval
eval (List ((Identifier "cond"):x:xs)) =
-}

eval e (List ((Identifier "progn"):xs)) = evalProgn e xs


eval e (List (Identifier func : args)) =
  mapM (eval e) args >>= liftThrows . apply func
eval _ x = throwError $ BadSpecialForm "Unrecognized Special Form" x



apply :: String -> [LispVal] -> ThrowError LispVal
apply func args = case lookup func primitives of
  Just f  -> f args
  Nothing -> throwError $ NotFunction "Unrecognized primitive function" func


evalProgn :: Env -> [LispVal] -> IOThrowError LispVal
evalProgn e = foldl (\c x -> c >> eval e x) (return $ List [])

{- ex 4/3 -}
evalCondClauses :: Env -> [LispVal] -> IOThrowError LispVal
evalCondClauses _ [] = return $ List []
evalCondClauses e (List (Identifier "else" : Identifier "=>" : [x]):_) =
  eval e x
evalCondClauses e (List (Identifier "else" : xs):_) = evalProgn e xs
evalCondClauses e (List (cond : Identifier "=>" : [x]) : rest) =
  eval e cond >>= \result -> case result of
    Bool True  -> eval e x
    Bool False -> evalCondClauses e rest
    x          -> throwError $ TypeMismatch "boolean" x
evalCondClauses e (List (cond : xs) : rest) =
  eval e cond >>= \result -> case result of
    Bool True  -> evalProgn e xs
    Bool False -> evalCondClauses e rest
    x          -> throwError $ TypeMismatch "boolean" x
evalCondClauses _ x = throwError $ BadSpecialForm "Unrecognized Special Form"
                                                (List x)
{- ex 4/3 -}
evalCaseClauses :: Env -> LispVal -> [LispVal] -> IOThrowError LispVal
evalCaseClauses _ x [] = return $ List []
evalCaseClauses e x (List (Identifier "else" : xs) : _) = evalProgn e xs
evalCaseClauses e x (List (List xs : cons) : rest)      = do
  result <- matched x xs
  if result then evalProgn e cons else evalCaseClauses e x rest
  where matched val vals = liftM or (sequence $ map (eqv val) vals)
        eqv v1 v2 = do rst <- evalEqv v1 v2 `catchError`
                              const (return $ Bool False)
                       case rst of Bool a -> return a
                                   _      -> return False
        evalEqv a b = eval e (List [Identifier "eqv?", a, b])




evalCode :: Env -> String -> IOThrowError LispVal
evalCode e code = case parseLispVal code of
  Left err  -> throwError $ Parser err
  Right val -> eval e val


testShow :: String -> IO ()
testShow code = putStrLn $ case parseLispVal code of
    Left err -> "error: " ++ show err
    Right x  -> "showing: " ++ show x

testEval :: String -> IO ()
testEval code = do
  env <- nullEnv
  (evalCode env code >>= \val -> return ("eval result: " ++ show val))
    `catchError` (\err -> "error: " ++ show err)

main :: IO ()
main = getArgs >>= testEval . head
