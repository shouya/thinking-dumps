
module Error where

import Control.Monad.Error

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
                                       unwordsList found
  show (TypeMismatch expected found) = "Invalid type: expected " ++
                                       expected ++
                                       ", found " ++ show found
  show (Parser parseErr)             = "Parse error at " ++ show parseErr

instance Error LispError where
  noMsg = Default "An error has occured"
  strMsg = Default

type ThrowError = Either LispError

trapError action = action `catchError` (return . show)
