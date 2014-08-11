module Internal where

import Text.ParserCombinators.Parsec (ParseError)
import Data.IORef (IORef,newIORef,readIORef)

import Control.Monad.Except (throwError,ExceptT)
import Control.Monad.IO.Class (liftIO)
import System.IO (Handle)

data LispVal = Identifier String
             | List [LispVal]
             | DottedList [LispVal] LispVal
             | Number Integer
             | Float Double    -- Exercise 6
             | Rational Integer Integer -- Exercise 7
             | Complex Double Double    -- Exercise 7
             | Character Char  -- Exercise 5
             | String String
             | Bool Bool
             | PrimitiveFunc ([LispVal] -> ThrowError LispVal)
             | IOFunc ([LispVal] -> IOThrowError LispVal)
             | Port Handle
             | Func { params :: [String]
                    , vararg :: Maybe String
                    , body :: [LispVal]
                    , closure :: Env }

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
  show (PrimitiveFunc _) = "<primitive procedure>"
  show (Func p v _ _) = "(lambda (" ++ args p v ++ ") ...)"
    where args p (Just x) = unwords p ++ " . " ++ x
          args p Nothing  = unwords p
  show (IOFunc _) = "<IO primitive procedure>"
  show (Port _)   = "<IO port>"



unwordsList :: [LispVal] -> String
unwordsList = unwords . map show


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



type Env = IORef [(String, IORef LispVal)]
