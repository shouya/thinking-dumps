module Parser (LispVal(..)
              ,parseLispVal
              ) where


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
  rest <- many (symbol <|> alphaNum <|> char '\\') -- '\\' is for char syntax
  let (x:xs) = rest
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
           else Identifier (first : rest)

parseSign :: Parser Char
parseSign = option '+' $ (char '-' <|> char '+')

signify :: (Num a) => Char -> a -> a
signify '-' a = (-a)
signify '+' a = a
signify _ _ = error "invalid sign"


parseIntegerNumber :: Parser LispVal
parseIntegerNumber = do i <- parseInteger
                        optional $ char 'L'
                        return $ Number i

parseInteger :: Parser Integer
parseInteger = do sign <- parseSign
                  int <- parseUnsignedInteger
                  return $ signify sign int

parseUnsignedInteger :: Parser Integer
parseUnsignedInteger = liftM read $ many1 digit


{- Exercise 6 -}
parseFloatNumber :: Parser LispVal
parseFloatNumber = do f <- parseFloat
                      optional $ char 'F'
                      return $ Float f


parseFloat :: Parser Double
parseFloat = do sign <- parseSign
                num  <- parseUnsignedFloat
                return $ signify sign num

parseUnsignedFloat :: Parser Double
parseUnsignedFloat = (try parseExponential <|> parseDecimal)



parseDecimal :: Parser Double
parseDecimal = do ipart <- parseNumStr
                  char '.'
                  fpart <- parseNumStr
                  return $ fst $ head $ readFloat (ipart ++ "." ++ fpart)
  where parseNumStr = many1 digit


parseExponential :: Parser Double
parseExponential = do bpart <- (try parseDecimal <|>
                                liftM fromIntegral parseInteger)
                      oneOf "eE"
                      epart <- liftM fromIntegral parseInteger
                      return (bpart * 10 ** epart)


{- Exercise 7 -}
parseRationalNumber :: Parser LispVal
parseRationalNumber = do
  den <- parseInteger
  char '/'
  num <- parseInteger
  let x = gcd den num
      d = den `div` x
      n = num `div` x
      d' = if n < 0 then -d else d
      n' = if n < 0 then -n else n
  return $ if n == 1
           then Number d'
           else Rational d' n'

{- Exercise 7 -}
parseComplexNumber :: Parser LispVal
parseComplexNumber = do
  real <- try parseFloat <|> (liftM fromIntegral $ try parseInteger)
  signi<- char '+' <|> char '-'
  imag <- option 1 (try parseUnsignedFloat <|>
                    liftM fromIntegral parseUnsignedInteger)
  char 'i'
  return $ Complex real (signify signi imag)


{- Modified implementation of this function -}
parseNumber :: Parser LispVal
parseNumber =  try parseComplexNumber
           <|> try parseFloatNumber
           <|> try parseRationalNumber
           <|> try parseIntegerNumber


{- Exercise 1.1/1.2 -}
{-
parseNumber :: Parser LispVal
parseNumber = many1 digit >>= return . Number . read
parseNumber = do s <- many1 digit
                 return $ Number $ read s
-}



parseExpr :: Parser LispVal
parseExpr =  parseString
         <|> try parseNumber
         <|> try parseIdentifier
         <|> try parseQuoted
         <|> char '(' *> (try parseList <|> parseDottedList) <* char ')'



parseList :: Parser LispVal
parseList = liftM List $ sepBy parseExpr spaces

parseDottedList :: Parser LispVal
parseDottedList = do
  head <- endBy parseExpr spaces
  tail <- char '.' >> spaces >> parseExpr
  return $ DottedList head tail

parseQuoted :: Parser LispVal
parseQuoted = do
      char '\''
      x <- parseExpr
      return $ List [Identifier "quote", x]


readExpr :: String -> String
readExpr input = case parse (parseExpr <* eof) "lisp" input of
  Left err -> "No match: " ++ show err
  Right _  -> "Found value."


parseLispVal :: String -> Either ParseError LispVal
parseLispVal = parse (parseExpr <* eof) "input"


main :: IO ()
main = getArgs >>= putStrLn . readExpr . head
