import qualified Data.Set as S
import Data.Function (on)

import Control.Monad
import Control.Applicative ((<*))

import Text.ParserCombinators.Parsec
import qualified Text.Parsec.Token as Tok
import Text.Parsec.Language (emptyDef)

-- import System.Environment

-- type
type Identifier = String
data Expr = Var  Identifier
          | App  Expr Expr
          | Lamb Identifier Expr

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
expr = chainl1 expr' (return App)
  where
    expr' = parens expr
       <|> do { lamb; v <- ident; dot; e <- expr; return (Lamb v e) }
       <|> liftM Var ident
    lexer = Tok.makeTokenParser emptyDef
    parens = Tok.parens lexer
    ident = Tok.identifier lexer
    dot = Tok.symbol lexer "." >> return ()
    lamb = Tok.symbol lexer "\\" >> return ()

program :: Parser Expr
program = expr <* eof


parseExpr :: String -> Expr
parseExpr xs = case parse program "" xs of
  Left a  -> error $ show a
  Right b -> b

-- reduction
reduce :: Expr -> Expr
reduce v@(Var _) = v
reduce v@(Lamb _ _) = v
reduce (App a b) = apply (reduce a) (reduce b)


apply :: Expr -> Expr -> Expr
apply (Lamb v e) e2 = subst e v e2
apply o@(App a b) e2 = apply (reduce o) e2
apply _ _ = error "cannot apply on plain variable"


subst :: Expr -> Identifier -> Expr -> Expr
subst o@(Var v) i e = if v == i then e else o
subst o@(Lamb v e) i e2 = if v == i then o else Lamb v (subst e i e2)
subst (App a b) i e2 = (App `on` (flip (flip subst i) e2)) a b


freeVar :: Expr -> S.Set Identifier
freeVar (Var x) = S.singleton x
freeVar (Lamb v e) = S.delete v $ freeVar e
freeVar (App a b) = (S.union `on` freeVar) a b
