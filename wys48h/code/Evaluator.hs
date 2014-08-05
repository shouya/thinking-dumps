
import Parser

instance Show LispVal where
  show (String xs) = show xs
  show (Identifier x) = x
  show (Number x) = show x
  show (Float x) = show x
  show (Rational p q) = show p ++ "/" ++ show q
  show (Complex r i) = show r ++ (if i < 0 then "-" else "+") ++
                       show (abs i) ++ "i"
  show (Bool True) = "#t"
  show (Bool False) = "#f"
