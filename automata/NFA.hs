{-# LANGUAGE GADTs #-}
module NFA where

import State
import Input

type NFATransFunc s i = s -> i -> [s]

data NFA s i where
  NFA :: (State s, Input i) => s -> [s] -> (NFATransFunc s i) -> NFA s i
