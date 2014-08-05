{-# LANGUAGE TemplateHaskell #-}

module PrimitiveTH (predicateOp) where

import Parser

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

predicateOp :: Name -> ExpQ
predicateOp nam = do
  nn <- newName "p"
  lamE [varP nn] $ caseE (appE [| head |] (varE nn)) [
    match (recP nam []) (normalB [| Bool True  |]) [],
    match wildP         (normalB [| Bool False |]) []
    ]
