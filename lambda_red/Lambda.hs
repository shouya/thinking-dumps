
import Control.Monad
import Text.ParserCombinators.Parsec
import qualified Text.Parsec.Token as Tok
import Text.Parsec.Language (emptyDef)

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


expr :: Parser Expr
expr =     (parens expr)
       <|> do { a <- expr; b <- expr; return (App a b) }
       <|> do { lamb; v <- ident; dot; e <- expr; return (Lamb v e) }
       <|> (liftM Var ident)
  where
    lexer = Tok.makeTokenParser emptyDef
    parens = Tok.parens lexer
    ident = Tok.identifier lexer
    dot = Tok.symbol lexer "." >> return ()
    lamb = Tok.symbol lexer "\\" >> return ()
