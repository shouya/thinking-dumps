
module Error (LispError(..)
             ,ThrowError
             ,IOThrowError
             ,extractValue
             ,trapError
             ,throwError
             ,liftThrows
             ,catchError
             ,runExceptT
             ,runIOThrows) where

import Control.Monad.Except

import Parser


data LispError = NumArgs Integer [LispVal]
               | TypeMismatch String LispVal
               | Parser ParseError
               | BadSpecialForm String LispVal
               | NotFunction String String
               | UnboundVar String String
               | Default String

instance Show LispError where
  show (UnboundVar message varname)  = message ++ ": " ++ varname
  show (BadSpecialForm message form) = message ++ ": " ++ show form
  show (NotFunction message func)    = message ++ ": " ++ show func
  show (NumArgs expected found)      = "Expected " ++ show expected ++
                                       " args; found values " ++
                                       unwords (map show found)
  show (TypeMismatch expected found) = "Invalid type: expected " ++
                                       expected ++
                                       ", found " ++ show found
  show (Parser parseErr)             = "Parse error at " ++ show parseErr

{- Deprecated for Control.Monad.Except

instance Error LispError where
  noMsg = Default "An error has occured"
  strMsg = Default
-}

type ThrowError = Either LispError
type IOThrowError = ExceptT LispError IO


liftThrows :: ThrowError a -> IOThrowError a
liftThrows (Left a)  = throwError a
liftThrows (Right a) = return a


runIOThrows :: IOThrowError String -> IO String
runIOThrows action = runExceptT (trapError action) >>= return . extractValue


-- trapError :: (Monad m) => m String -> m String
trapError action = action `catchError` (return . show)

extractValue :: ThrowError a -> a
extractValue (Right val) = val
