
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

import Internal
import Parser


runIOThrows :: IOThrowError String -> IO String
runIOThrows action = runExceptT (trapError action) >>= return . extractValue


-- trapError :: (Monad m) => m String -> m String
trapError action = action `catchError` (return . show)

extractValue :: ThrowError a -> a
extractValue (Right val) = val
