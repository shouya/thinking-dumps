
import DFA
import RE

import State
import ExampleLib

data Q1State = A | B | C | D | X deriving Eq
instance State Q1State where
  allStates = [A,B,C,D,X]
  failState = Just X
instance IntState Q1State where
  stateNo A = 1
  stateNo B = 2
  stateNo C = 3
  stateNo D = 4
  stateNo X = 5


q1DFA = DFA A [D] (transTableToFunc foo)
  where foo = [(A,O,B)
              ,(A,I,C)
              ,(B,I,D)
              ,(C,O,D)
              ,(D,I,B)
              ,(D,O,A)]

q1Ans = kPath 1 4 4 q1DFA
