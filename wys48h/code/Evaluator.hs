module Evaluator (eval
                 ,apply
                 ,evalCode
                 ,nullEnv
                 ,primitiveEnv
                 ,Env
                 ) where

import Parser
import Primitive
import Error
import Internal

import System.Environment (getArgs)
import Control.Monad (liftM,liftM2,foldM)
import Control.Monad.IO.Class (liftIO)
import Data.IORef



-- TODO: Add primitive functions
nullEnv :: IO Env
nullEnv = newIORef []


primitiveEnv :: IO Env
primitiveEnv = nullEnv >>= flip (foldM (superUncurry addBinding))
                                (map pack primitives)
  where pack (var, fun) = (var, PrimitiveFunc fun)
        superUncurry f a (b,c) = f a b c


isBound :: Env -> String -> IO Bool
isBound e v = readIORef e >>= return . maybe False (const True) . lookup v

getVar :: Env -> String -> IOThrowError LispVal
getVar e var = do env <- liftIO $ readIORef e
                  maybe (throwError $ UnboundVar "getting" var)
                        (liftIO . readIORef)
                        (lookup var env)

defineVar :: Env -> String -> LispVal -> IOThrowError LispVal
defineVar e var val = do
  defined <- liftIO $ isBound e var
  if defined
    then setVar e var val >> return ()
    else liftIO $ do refVal <- newIORef val
                     modifyIORef' e ((var,refVal):)
  return val


modifyVar :: Env -> String -> (LispVal -> LispVal) -> IOThrowError ()
modifyVar e var f = do
  env <- liftIO $ readIORef e
  maybe (throwError $ UnboundVar "setting" var)
    (liftIO . flip modifyIORef' f)
    (lookup var env)
  return ()

setVar :: Env -> String -> LispVal -> IOThrowError LispVal
setVar e var val = modifyVar e var (const val) >> return val

addBinding :: Env -> String -> LispVal -> IO Env
addBinding env var val = liftM2 (:) (liftM ((,) var) (newIORef val))
                                    (readIORef env) >>= newIORef


eval :: Env -> LispVal -> IOThrowError LispVal
eval _ val@(String {}) = return val
eval _ val@(Number {}) = return val
eval _ val@(Float {}) = return val
eval _ val@(Rational {}) = return val
eval _ val@(Complex {}) = return val
eval _ val@(Bool {}) = return val
eval e (Identifier var) = getVar e var

eval _ (List [Identifier "quote", val]) = return val
eval e (List [Identifier "if", cond, cons, alt]) =
  eval e cond >>= \result -> case result of
    Bool True  -> eval e cons
    Bool False -> eval e alt
    x        -> throwError $ TypeMismatch "boolean" x  -- Exercise 4/1


eval env (List [Identifier "set!", Identifier var, form]) =
  eval env form >>= setVar env var
eval env (List [Identifier "define", Identifier var, form]) =
  eval env form >>= defineVar env var

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


eval e (List (Identifier "lambda" : List args : body)) =
  return $ Func { params = map (\(Identifier a) -> a) args
                , vararg = Nothing
                , body = body
                , closure = e }
eval e (List (Identifier "lambda" : DottedList args va : body)) =
  return $ Func { params = map (\(Identifier a) -> a) args
                , vararg = let (Identifier a) = va in Just a
                , body = body
                , closure = e }



eval e (List (func : args)) = do
  f <- eval e func
  a <- mapM (eval e) args
  apply f a

eval _ x = throwError $ BadSpecialForm "Unrecognized Special Form" x


apply :: LispVal -> [LispVal] -> IOThrowError LispVal
apply (PrimitiveFunc func) args = liftThrows $ func args
apply (Func p v b c) args = do
  let (a1,a2) = splitAt (length p) args
  if length a2 > 0 && v == Nothing
    then throwError $ NumArgs (fromIntegral $ length p) args
    else do env <- liftIO $ do pa <- sequence $ zipWith consPair p a1
                               pa' <- maybe (return pa) (consVarArg pa a2) v
                               env <- readIORef c
                               newIORef (pa' ++ env)
            evalProgn env b
  where consPair p' a' = do a'' <- newIORef a'
                            return (p', a'')
        consVarArg pa a v' = do a' <- newIORef $ List a
                                return $ (v', a') : pa



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
testEval code = do env <- nullEnv
                   rst <- runExceptT $ evalCode env code
                   putStrLn $ "eval result: " ++ show rst
                `catchError` (\err -> putStrLn $ "error: " ++ show err)


main :: IO ()
main = getArgs >>= testEval . head
