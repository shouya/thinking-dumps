{-# LANGUAGE TypeSynonymInstances #-}
import State
import Input
import ExampleLib

import DFA
import RE

type MyState = Integer
instance State MyState where
  allStates = [1,2,3]
  failState = Nothing

instance IntState MyState where
  stateNo n = n

tbl :: [(MyState,BinaryInput,MyState)]
tbl = [(1,O,2),(2,O,3),(3,O,1),
       (1,I,3),(2,I,1),(3,I,2)]

myDFA = DFA (2 :: MyState) [3] (transTableToFunc tbl)
