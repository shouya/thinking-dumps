{-# LANGUAGE TemplateHaskell #-}

module Primitive (primitives) where

import PrimitiveTH
import Parser


primitives :: [(String, [LispVal] -> LispVal)]
primitives = [ -- Arithmetic functions
              ("+", numericBinop (+))
             ,("-", numericBinop (-))
             ,("*", numericBinop (*))
             ,("/", numericBinop div)
             ,("mod", numericBinop mod)
             ,("quotient", numericBinop quot)
             ,("remainder", numericBinop rem)

              -- Type test functions
             ,("boolean?", $(predicateOp 'Bool))
             ,("symbol?", $(predicateOp 'Identifier))
             ,("string?", $(predicateOp 'String))
             ,("number?", $(predicateOp 'Number))
             ,("rational?", $(predicateOp 'Rational))
             ,("float?", $(predicateOp 'Float))
             ,("complex?", $(predicateOp 'Complex))
             ]




numericBinop :: (Integer -> Integer -> Integer) -> [LispVal] -> LispVal
numericBinop op params = Number $ foldl1 op $ map unpackNum params

unpackNum :: LispVal -> Integer
unpackNum (Number n) = n
unpackNum (String n) = let parsed = reads n :: [(Integer, String)] in
  if null parsed
  then 0
  else fst $ parsed !! 0
unpackNum (List [n]) = unpackNum n
unpackNum _ = 0


-- predicateOp :: (LispVal -> Bool) -> [LispVal] -> LispVal
-- predicateOp f xs = Bool $ f (head xs)


booleanp (Bool _) = True
booleanp _        = False
symbolp (Identifier _) = True
symbolp _              = False
stringp (String _) = True
stringp _          = False
numberp (Number _) = True
numberp _          = False
rationalp (Rational _ _) = True
rationalp _              = False
floatp (Float _) = True
floatp _         = False
complexp (Complex _ _) = True
complexp _             = False
