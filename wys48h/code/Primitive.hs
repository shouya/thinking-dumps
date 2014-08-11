{-# LANGUAGE TemplateHaskell,
             ExistentialQuantification,
             RankNTypes,
             ImpredicativeTypes #-}

module Primitive (primitives
                 ,ioprimitives) where

import PrimitiveTH (predicateOp)
import Error
import Parser

import Data.Function (on)
import Control.Monad (liftM,join)
import Data.Char (toLower)

import System.IO
import Control.Monad.IO.Class (liftIO)



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

              -- String functions (ex 4/4)
             ,("make-string", makeString)
             ,("string", stringConstructor)
             ,("string-length", stringLength)
             ,("string-ref", stringRef)
             -- ,("string-set!", stringSet)       -- not able to implement yet
             ,("string-ci=?", strBoolBinop (\a b -> (map toLower a) ==
                                                    (map toLower b)))

             ,("substring", substring)
             ,("string-append", stringAppend)
             ,("string->list", string2list)
             ,("list->string", list2string)
             -- ,("string-copy", stringCopy)
             -- ,("string-fill!", stringFill)

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


ioprimitives :: [(String, [LispVal] -> IOThrowError LispVal)]
ioprimitives = [
--    ("apply", applyProc)
    ("open-input-file", makePort ReadMode)
  , ("open-output-file", makePort WriteMode)
  , ("close-input-port", closePort)
  , ("close-output-port", closePort)
  , ("read", readProc)
  , ("write", writeProc)
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

{- ex 4/4 : begin -}
str2sym :: [LispVal] -> ThrowError LispVal
str2sym [String x] = return $ Identifier x
str2sym [a]        = throwError $ TypeMismatch "string" a
str2sym xs         = throwError $ NumArgs 2 xs

sym2str :: [LispVal] -> ThrowError LispVal
sym2str [Identifier x] = return $ String x
sym2str [a]        = throwError $ TypeMismatch "symbol" a
sym2str xs         = throwError $ NumArgs 2 xs


makeString [Number n] = return $ String (replicate (fromIntegral n) ' ')
makeString [Number n, Character c] = return $
                                     String (replicate (fromIntegral n) c)
makeString [Number _,x] = throwError $ TypeMismatch "character" x
makeString [x,_]        = throwError $ TypeMismatch "number" x
makeString [x]          = throwError $ TypeMismatch "number" x
makeString xs           = throwError $ NumArgs 1 xs

stringConstructor xs
  | all isChar xs = (return $ String $ map (\(Character c) -> c) xs)
  | otherwise     = throwError $ BadSpecialForm "list of characters" (List xs)
  where isChar x = case x of (Character _) -> True; _ -> False

stringLength [String str] = return $ Number $ fromIntegral $ length str
stringLength [x]          = throwError $ TypeMismatch "string" x
stringLength xs           = throwError $ NumArgs 1 xs

stringRef [String str, Number idx] = return $
                                     Character (str !! (fromIntegral idx))
stringRef [String _, x]   = throwError $ TypeMismatch "number" x
stringRef [x, _]          = throwError $ TypeMismatch "string" x
stringRef xs              = throwError $ NumArgs 2 xs

substring args@[String str, Number s, Number e]
  | e <= (fromIntegral $ length str) && s <= e && 0 <= s  =
    return $ String $ drop (fromIntegral s) $ take (fromIntegral (e-s)) str
  | otherwise = throwError $
                BadSpecialForm "0 <= s <= e <= len(str)" (List args)
substring [String _, Number _, x] = throwError $ TypeMismatch "number" x
substring [String _, x, _]        = throwError $ TypeMismatch "number" x
substring [x, _, _]               = throwError $ TypeMismatch "string" x
substring xs = throwError $ NumArgs 3 xs

stringAppend xs
  | all isString xs = return $ String $ join $ map extractString xs
  | otherwise       = throwError $ BadSpecialForm "list of strings" (List xs)
  where isString x = case x of (String _) -> True; _ -> False
        extractString x = case x of (String x) -> x

string2list [String str] = return $ List $ map Character str
string2list [x]          = throwError $ TypeMismatch "string" x
string2list xs           = throwError $ NumArgs 1 xs

list2string [List xs]
  | all isChar xs = stringConstructor xs
  | otherwise     = throwError $ BadSpecialForm "list of characters" (List xs)
  where isChar x = case x of (Character _) -> True; _ -> False
list2string [x]   = throwError $ TypeMismatch "list" x
list2string xs    = throwError $ NumArgs 1 xs
{- ex 4/4 : end -}



makePort :: IOMode -> [LispVal] -> IOThrowError LispVal
makePort mode [String filename] = liftM Port $ liftIO $ openFile filename mode

closePort :: [LispVal] -> IOThrowError LispVal
closePort [Port p] = liftIO $ hClose p >> (return $ Bool True)
closePort _        = return $ Bool False

readProc :: [LispVal] -> IOThrowError LispVal
readProc []       = readProc [Port stdin]
readProc [Port p] = liftIO (hGetLine p >>= return . String)

writeProc :: [LispVal] -> IOThrowError LispVal
writeProc [o] = writeProc [o, Port stdout]
writeProc [o, Port p] = liftIO (hPrint p o >> return (List []))
