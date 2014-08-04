
import Control.Applicative ((*>), (<*))
import Control.Monad

import Text.ParserCombinators.Parsec hiding (spaces)
import System.Environment

import Data.Char (isDigit)

data LispVal = Identifier String
             | List [LispVal]
             | DottedList [LispVal] LispVal
             | Number Integer
             | String String
             | Bool Bool


symbol :: Parser Char
symbol = oneOf "!#$%&|*+-/:<=>?@^_~"

spaces :: Parser ()
spaces = skipMany1 space

escaping_table = [('"', '"')
                 ,('\'', '\'')
                 ,('n', '\n')
                 ,('t', '\t')
                 ,('r', '\r')
                 ,('\\', '\\')
                 ]

parseString :: Parser LispVal
-- parseString = liftM String (char '"' *> many (noneOf "\"") <* char '"')
{- Exercise 2 -}
parseString = liftM String (char '"' *> many foo <* char '"')
  where foo =  (char '\\' >> char '"' >> return '"')
           <|> (noneOf "\"")


parseIdentifier :: Parser LispVal
parseIdentifier = do
  first <- (symbol <|> letter)
  rest  <- many (symbol <|> alphaNum)
  let atom = first : rest
  return $ case atom of
    "#t" -> Bool True
    "#f" -> Bool False
    ('-':xs) -> if all isDigit xs
                then (Number . negate . read) xs
                else Identifier atom
    _    -> Identifier atom


parseNumber :: Parser LispVal
parseNumber = liftM (Number . read) (many1 digit)


{- Exercise 1.1/1.2 -}
{-
parseNumber :: Parser LispVal
parseNumber = many1 digit >>= return . Number . read
parseNumber = do s <- many1 digit
                 return $ Number $ read s
-}

parseExpr :: Parser LispVal
parseExpr = parseString
         <|> parseIdentifier
         <|> parseNumber



readExpr :: String -> String
readExpr input = case parse (parseExpr) "lisp" input of
  Left err -> "No match: " ++ show err
  Right _ -> "Found value"


main :: IO ()
main = do
  args <- getArgs
  putStrLn (readExpr (args !! 0))
