
import Control.Applicative ((*>), (<*))
import Control.Monad

import Text.ParserCombinators.Parsec hiding (spaces)
import System.Environment

import Data.Char (isDigit)
import Data.Maybe (fromJust)
import Numeric (readHex, readOct, readFloat)

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
             deriving Show

symbol :: Parser Char
symbol = oneOf "!#$%&|*+-/:<=>?@^_~"

spaces :: Parser ()
spaces = skipMany1 space


{- Exercise 3 -}
escapingTable = [('"', '"')
                ,('\'', '\'')
                ,('n', '\n')
                ,('t', '\t')
                ,('r', '\r')
                ,('\\', '\\')
                ]
charNameTable = [("space", ' ')
                ,("newline", '\n')
                ,("tab", '\t')
                ]

parseString :: Parser LispVal
-- parseString = liftM String (char '"' *> many (noneOf "\"") <* char '"')

{- Exercise 2 -}
parseString = liftM String (char '"' *> many foo <* char '"')
  where foo =  try bar
           <|> char '\\'
           <|> (noneOf "\"")
        bar = do char '\\'
                 x <- oneOf (map fst escapingTable)
                 return $ fromJust $ lookup x escapingTable


nameToChar :: String -> Char
nameToChar xs = case lookup xs charNameTable of
  Just c  -> c
  Nothing -> error $ "No character names '" ++ xs ++ "' found!"

parseIdentifier :: Parser LispVal
parseIdentifier = do
  first  <- (symbol <|> letter)
  (x:xs) <- many (symbol <|> alphaNum <|> char '\\') -- '\\' is for char syntax
  return $ if first == '#' then
               case x of
                 't' -> Bool True
                 'f' -> Bool False
                 'o' -> (Number . fst . head . readOct) xs    -- Exercise 4
                 'h' -> (Number . fst . head . readHex) xs    -- Exercise 4
                 '\\'-> Character $ if length xs == 1         -- Exercise 5
                                    then head xs else nameToChar xs
                 _   -> error "invalid syntax"
               {- TODO: unify this with parseNumber -}
           else if x == '-' && all isDigit xs then (Number . negate . read) xs
                else Identifier (first : x : xs)


parseInteger :: Parser Integer
parseInteger = liftM read (many1 digit)

parseNumber :: Parser LispVal
parseNumber = liftM Number parseInteger

{- Exercise 6 -}
{- TODO: Sign -}
parseFloat :: Parser LispVal
parseFloat = liftM (Float . fst . head) (decForm <|> expForm)
  where decForm = do ipart <- parseNumStr
                     char '.'
                     fpart <- parseNumStr
                     optional $ char 'F'
                     return $ readFloat (ipart ++ "." ++ fpart)
        expForm = do bpart <- parseNumStr
                     oneOf "eE"
                     epart <- parseNumStr
                     optional $ char 'F'
                     return $ readFloat (bpart ++ "e" ++ epart)
        parseNumStr = many1 digit

{- Exercise 7 -}
{- TODO: parse neg rat like: `-1/2` -}
parseRational :: Parser LispVal
parseRational = do
  den <- parseInteger
  char '/'
  num <- parseInteger
  let x = gcd den num
      d = den `div` x
      n = num `div` x
  return $ if n == 1
           then Number d
           else Rational d n
{- Exercise 7 -}
{- TODO: Omit Sign, because will be implied in parseNumber and parseFloat -}
parseComplex :: Parser LispVal
parseComplex = do
  signr <- option '+' (char '+' <|> char '-')
  real' <- try parseFloat <|> parseNumber
  signi <- char '+' <|> char '-'
  imag' <- option (Float 1) (try parseFloat <|> parseNumber)
  char 'i'
  let real = case real' of Float x -> x; Number x -> fromIntegral x
      imag = case imag' of Float x -> x; Number x -> fromIntegral x
  return $ Complex (if signr == '-' then -real else real)
                   (if signi == '-' then -imag else imag)


{- Exercise 1.1/1.2 -}
{-
parseNumber :: Parser LispVal
parseNumber = many1 digit >>= return . Number . read
parseNumber = do s <- many1 digit
                 return $ Number $ read s
-}



parseExpr :: Parser LispVal
parseExpr =  parseString
         <|> try parseIdentifier
         <|> try parseComplex
         <|> try parseFloat
         <|> try parseRational
         <|> try parseNumber




readExpr :: String -> String
readExpr input = case parse (parseExpr <* eof) "lisp" input of
  Left err -> "No match: " ++ show err
  Right x  -> "Found value: " ++ show x


main :: IO ()
main = do
  args <- getArgs
  putStrLn (readExpr (args !! 0))
