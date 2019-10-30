{-# LANGUAGE ApplicativeDo #-}

module Parser where

-- Implementation of an Applicative Parser

import Data.Char
import Control.Applicative (some, many, empty, (<*>), (<$>), (<|>), Alternative)
import Control.Monad (forM_)

data Parser a = Parser { runParser :: String -> [(a, String)] }


instance Functor Parser where
  -- fmap :: (a -> b) -> (Parser a -> Parser b)
  fmap f (Parser p) = Parser (\s -> [(f a, s') | (a,s') <- p s])

instance Applicative Parser where
  -- pure :: a -> Parser a
  -- <*> :: Parser (a -> b) -> Parser a -> Parser b
  pure x = Parser $ \s -> [(x, s)]
  (Parser pf) <*> (Parser p) = Parser $ \s -> [(f a, s'') | (f, s') <- pf s, (a, s'') <- p s']

instance Alternative Parser where
  -- empty :: Parser a
  -- <|> :: Parser a -> Parser a -> Parser a
  empty = Parser $ \_s -> []
  p1 <|> p2 = Parser $ \s ->
    case runParser p1 s of
      [] -> runParser p2 s
      xs -> xs

satisfy :: (Char -> Bool) -> Parser Char
satisfy f = Parser $ \s -> case s of
  [] -> []
  (c:s') -> if f c then [(c,s')] else []

char :: Char -> Parser Char
char c = satisfy (==c)

-----------------------------------------------
--
--
-- Demo: use the parser above to parse a simplified version of
-- this problem: https://www.codewars.com/kata/molecule-to-atoms
--
--

moleculeParser :: Parser [(String, Int)]
moleculeParser = seqn

bracket :: Parser a -> Parser a
bracket p = pickMiddle <$> char '(' <*> p <*> char ')' <|>
            pickMiddle <$> char '[' <*> p <*> char ']'
  where pickMiddle :: a -> b -> c -> b
        pickMiddle a b c = b

atom :: Parser String
atom = do
  c <- satisfy isUpper
  return [c]

group :: Parser [(String, Int)]
group = fmap singleton (withCount atom) <|> fmap multiply (withCount (bracket seqn))
  where singleton :: a -> [a]
        singleton x = [x]
        multiply :: ([(String, Int)], Int) -> [(String, Int)]
        multiply (xs, factor) = [(a,c * factor) | (a,c) <- xs]

withCount :: Parser a -> Parser (a, Int)
withCount p = do
  a <- p
  n <- satisfy (isDigit) <|> pure '1'
  return (a, read [n])

seqn :: Parser [(String, Int)]
seqn = fmap concat (some group)

parseMolecule :: String -> [(String, Int)]
parseMolecule s =
  let Parser p = moleculeParser
  in case p s of
    [(result,"")] -> result
    _ -> error "failed"


main = forM_ ["H2O", "(H2O2)3", "K4[ON(SO3)2]2"] $ \mol ->
  putStrLn $ mol ++ ":\t" ++ (show $ parseMolecule mol)

