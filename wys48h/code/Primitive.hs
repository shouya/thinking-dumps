{-# LANGUAGE TemplateHaskell #-}

module Primitive (primitives) where

import PrimitiveTH (predicateOp)
import Parser


primitives :: [(String, [LispVal] -> ThrowError LispVal)]
primitives = [ -- Arithmetic functions
              ("+", numericBinop (+))
             ,("-", numericBinop (-))
             ,("*", numericBinop (*))
             ,("/", numericBinop div)
             ,("mod", numericBinop mod)
             ,("quotient", numericBinop quot)
             ,("remainder", numericBinop rem)

              -- Boolean operations
             ,("=", numBoolBinop (==))
             ,("<", numBoolBinop (<))
             ,(">", numBoolBinop (>))
             ,("/=", numBoolBinop (/=))
             ,(">=", numBoolBinop (>=))
             ,("<=", numBoolBinop (<=))
             ,("&&", boolBoolBinop (&&))
             ,("||", boolBoolBinop (||))
             ,("string=?", strBoolBinop (==))
             ,("string<?", strBoolBinop (<))
             ,("string>?", strBoolBinop (>))
             ,("string<=?", strBoolBinop (<=))
             ,("string>=?", strBoolBinop (>=))

              -- Type test functions, as Exercise 3/1 (ex!)
             ,("boolean?", $(predicateOp 'Bool))
             ,("symbol?", $(predicateOp 'Identifier))
             ,("string?", $(predicateOp 'String))
             ,("number?", $(predicateOp 'Number))
             ,("rational?", $(predicateOp 'Rational))
             ,("float?", $(predicateOp 'Float))
             ,("complex?", $(predicateOp 'Complex))

              -- Exercise 3/3
             ,("symbol->string", (\x -> let [Identifier a] = x in String a))
             ,("string->symbol", (\x -> let [String a] = x in Identifier a))
             ]



car :: [LispVal] -> ThrowsError LispVal
car [List (x : xs)]         = return x
car [DottedList (x : xs) _] = return x
car [badArg]                = throwError $ TypeMismatch "pair" badArg
car badArgList              = throwError $ NumArgs 1 badArgList

cdr :: [LispVal] -> ThrowsError LispVal
cdr [List (x : xs)]         = return $ List xs
cdr [DottedList [_] x]      = return x
cdr [DottedList (_ : xs) x] = return $ DottedList xs x
cdr [badArg]                = throwError $ TypeMismatch "pair" badArg
cdr badArgList              = throwError $ NumArgs 1 badArgList

cons :: [LispVal] -> ThrowsError LispVal
cons [x, List []]         = return $ List [x]
cons [x, DottedList xs s] = return $ DottedList (x:xs) s
cons [x, y]               = return $ DottedList [x] y
cons badArgList           = throwError $ NumArgs 2 badArgList


eqv :: [LispVal] -> ThrowsError LispVal
eqv [(Bool arg1), (Bool arg2)]             = return $ Bool $ arg1 == arg2
eqv [(Number arg1), (Number arg2)]         = return $ Bool $ arg1 == arg2
eqv [(String arg1), (String arg2)]         = return $
eqv [(Atom arg1), (Atom arg2)]             = return $ Bool $ arg1 == arg2
eqv [(DottedList xs x), (DottedList ys y)] = eqv [List $ xs ++ [x],
                                                  List $ ys ++ [y]]
eqv [(List xs), (List ys)] = return $ Bool $ ((==) `on` length) xs ys &&
                                             (all $ zipWith eqvPair xs xs)
  where eqvPair (x1, x2) = case eqv [x1, x2] of Left err -> False
                                                Right (Bool val) -> val
eqv [_, _]                                 = return $ Bool False
eqv badArgList = throwError $ NumArgs 2 badArgList



numericBinop :: (Integer -> Integer -> Integer) -> [LispVal] -> LispVal
numericBinop op params
  | length params > 2 = mapM unpackNum params >>= return . Number . foldl1 op
  | otherwise         = throwError $ NumArgs 2 params

boolBinop :: (LispVal -> ThrowsError a) ->
             (a -> a -> Bool) ->
             [LispVal] ->
             ThrowsError LispVal
boolBinop unpacker op args
  | length args /= 2 = throwError $ NumArgs 2 args
  | otherwise = mapM unpacker args >>= \[a,b] -> return Bool $ a `op` b


numBoolBinop  = boolBinop unpackNum
strBoolBinop  = boolBinop unpackStr
boolBoolBinop = boolBinop unpackBool


unpackStr :: LispVal -> ThrowsError String
unpackStr (String s) = return s
unpackStr x          = throwError $ TypeMismatch "string" x

unpackBool :: LispVal -> ThrowsError Bool
unpackBool (Bool b)  = return b
unpackBool x         = throwError $ TypeMismatch "boolean" x






unpackNum :: LispVal -> ThrowError Integer
unpackNum (Number n) = return n
{- Exercise 3/2: comment this two cases -}
{-
unpackNum (String n) = let parsed = reads n :: [(Integer, String)] in
  if null parsed
  then 0
  else fst $ parsed !! 0
unpackNum (List [n]) = unpackNum n
-}
unpackNum = throwError . TypeMismatch "number"
