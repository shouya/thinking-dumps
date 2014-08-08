{-# LANGUAGE TemplateHaskell,
             ExistentialQuantification,
             RankNTypes,
             ImpredicativeTypes #-}

module Primitive (primitives) where

import PrimitiveTH (predicateOp)
import Error
import Parser

import Data.Function (on)
import Control.Monad (liftM)

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
             ,("char=?", charBoolBinop (==))
             ,("char<?", charBoolBinop (<))
             ,("char>?", charBoolBinop (>))
             ,("char<=?", charBoolBinop (<=))
             ,("char>=?", charBoolBinop (>=))

              -- Basic pair manipulation
             ,("car",  car)
             ,("cdr",  cdr)
             ,("cons", cons)

              -- Equality test operations
             ,("eq?",    eqv)
             ,("eqv?",   eqv)
             ,("equal?", equal)

              -- Type test functions, as Exercise 3/1 (ex!)
              {- TODO: detect wrong num of args error -}
             ,("boolean?", $(predicateOp 'Bool))
             ,("symbol?", $(predicateOp 'Identifier))
             ,("string?", $(predicateOp 'String))
             ,("number?", $(predicateOp 'Number))
             ,("rational?", $(predicateOp 'Rational))
             ,("float?", $(predicateOp 'Float))
             ,("complex?", $(predicateOp 'Complex))

              -- Exercise 3/3
             ,("symbol->string", sym2str)
             ,("string->symbol", str2sym)
             ]



car :: [LispVal] -> ThrowError LispVal
car [List (x : xs)]         = return x
car [DottedList (x : xs) _] = return x
car [badArg]                = throwError $ TypeMismatch "pair" badArg
car badArgList              = throwError $ NumArgs 1 badArgList

cdr :: [LispVal] -> ThrowError LispVal
cdr [List (x : xs)]         = return $ List xs
cdr [DottedList [_] x]      = return x
cdr [DottedList (_ : xs) x] = return $ DottedList xs x
cdr [badArg]                = throwError $ TypeMismatch "pair" badArg
cdr badArgList              = throwError $ NumArgs 1 badArgList

cons :: [LispVal] -> ThrowError LispVal
cons [x, List []]         = return $ List [x]
cons [x, DottedList xs s] = return $ DottedList (x:xs) s
cons [x, y]               = return $ DottedList [x] y
cons badArgList           = throwError $ NumArgs 2 badArgList

eqv :: [LispVal] -> ThrowError LispVal
eqv [Identifier a, Identifier b]           = return $ Bool $ a == b
eqv [Bool a, Bool b]                       = return $ Bool $ a == b
eqv [Number a, Number b]                   = return $ Bool $ a == b
eqv [List [], List []]                     = return $ Bool True
eqv [List _, List _]                       = return $ Bool False
eqv args@[Character _, Character _]        = charBoolBinop (==) args
eqv [_, _]                                 = return $ Bool False
eqv x                                      = throwError $ NumArgs 2 x

equal :: [LispVal] -> ThrowError LispVal
equal [String a, String b]               = return $ Bool $ a == b
equal [DottedList xs x, DottedList ys y] = equal [List (x:xs), List (y:ys)]
equal [List xs, List ys] = return $ Bool $ ((==) `on` length) xs ys &&
                                           and (zipWith equalPair xs ys)
  where equalPair x1 x2 = case equal [x1, x2] of Left err -> False
                                                 Right (Bool val) -> val
equal [a,b]  = eqv [a,b]
equal x      = throwError $ NumArgs 2 x

{- Assuming wrongly that Scheme is weak-typed,
   this guide does not implement the R5RS eq/eqv/equal.

   While I have written them strictly following the standard instead.
   For the weak-typed `equal?` function, I named it 'eqweak'(eqweak?).
-}

data Unpacker = forall a. (Eq a) => Unpacker (LispVal -> ThrowError a)

unpackEquals :: LispVal -> LispVal -> Unpacker -> Bool
unpackEquals x y (Unpacker unpack) = case do a <- unpack x
                                             b <- unpack y
                                             return $ a == b
                                          `catchError` const (return False)
                                     of Left a  -> undefined -- impossible
                                        Right a -> a
{- This function doesn't really work
   as expect because the unpack functions
   are strict.

   Iu devas aldoni funkcioj kiel 'needStr'/'needNum'   ('_';)
-}

eqweak :: [LispVal] -> ThrowError LispVal
{- ex 4/2 -}
eqweak [List xs, List ys] = return $ Bool $ ((==) `on` length) xs ys &&
                                            and (zipWith eqwPair xs ys)
  where eqwPair x y = case eqweak [x, y] of Left _ -> False
                                            Right (Bool v) -> v
{- ex 4/2 -}
eqweak [DottedList xs x, DottedList ys y] = eqweak [List (x:xs)
                                                   ,List (y:ys)] -- ex 4/2
eqweak [a,b]   = return $ Bool $ any (unpackEquals a b) unpackers

unpackers :: [Unpacker]
unpackers = [Unpacker unpackStr
            ,Unpacker unpackBool
            ,Unpacker unpackNum
            ,Unpacker unpackChar
            ]

numericBinop :: (Integer -> Integer -> Integer) ->
                [LispVal] ->
                ThrowError LispVal
numericBinop op params
  | length params >= 2 = liftM (Number . foldl1 op) $ mapM unpackNum params
  | otherwise          = throwError $ NumArgs 2 params

boolBinop :: (LispVal -> ThrowError a) ->
             (a -> a -> Bool) ->
             [LispVal] ->
             ThrowError LispVal
boolBinop unpacker op args
  | length args /= 2 = throwError $ NumArgs 2 args
  | otherwise = case args of
    [_,_] -> mapM unpacker args >>= \[a,b] -> return $ Bool $ a `op` b
    xs    -> throwError $ NumArgs 2 xs


numBoolBinop  = boolBinop unpackNum
strBoolBinop  = boolBinop unpackStr
boolBoolBinop = boolBinop unpackBool
charBoolBinop = boolBinop unpackChar

unpackStr :: LispVal -> ThrowError String
unpackStr (String s) = return s
unpackStr x          = throwError $ TypeMismatch "string" x

unpackBool :: LispVal -> ThrowError Bool
unpackBool (Bool b)  = return b
unpackBool x         = throwError $ TypeMismatch "boolean" x

unpackChar :: LispVal -> ThrowError Char
unpackChar (Character c)  = return c
unpackChar x              = throwError $ TypeMismatch "character" x


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
unpackNum x = throwError $ TypeMismatch "number" x


str2sym :: [LispVal] -> ThrowError LispVal
str2sym [String x] = return $ Identifier x
str2sym [a]        = throwError $ TypeMismatch "string" a
str2sym xs         = throwError $ NumArgs 2 xs

sym2str :: [LispVal] -> ThrowError LispVal
sym2str [Identifier x] = return $ String x
sym2str [a]        = throwError $ TypeMismatch "symbol" a
sym2str xs         = throwError $ NumArgs 2 xs
