
import Text.ParserCombinators.Parsec
import Control.Applicative ((*>), (<*), (<$>))

-- import System.Environment

-- Expr
data Expr = Var  String
          | App  Expr Expr
          | Lamb String Expr

instance Show Expr where
  show (Var s) = s
  show (App a b) = f a ++ " " ++ g b
    where f e = case e of
            Lamb _ _ -> "(" ++ show e ++ ")"
            _        -> show e
          g e = case e of
            Var _ -> show e
            _     -> "(" ++ show e ++ ")"
  show (Lamb v e) = "\\" ++ v ++ "." ++ show e

-- parser
parseIdentifier :: Parser String
parseIdentifier = do h <- (letter <|> char '_')
                     t <- many (alphaNum <|> char '_')
                     return (h : t)

parseVar :: Parser Expr
parseVar = parseIdentifier >>= return . Var
parseApp :: Parser Expr
parseApp = chainl1 parseExpr (space >> spaces <$> App)

parseLamb :: Parser Expr
parseLamb = do char '\\' *> spaces
               v <- parseIdentifier
               spaces *> char '.' *> spaces
               e <- parseExpr
               return $ Lamb v e
parseParen :: Parser Expr
parseParen = char '(' *> spaces
             *> parseExpr <*
             spaces <* char ')'

parseExpr :: Parser Expr
parseExpr =
      parseVar
  <|> parseApp
  <|> parseParen
  <|> parseLamb
