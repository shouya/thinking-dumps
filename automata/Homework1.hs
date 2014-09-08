{- Homework Week 1 -}

import DFA
import ExampleLib
import State

{- Q1:
  Which of the following string is accepted by this DFA.
-}


i1 = [I,O,I,I,O,O,O]
i2 = [I,O,O,O,I]
i3 = [I,O,I,I,O,I,I]
i4 = [I,I,O,O,I,I,I]

data Q1State = A | B | C | D | X deriving Eq
instance State Q1State where
  allStates = [A,B,C,D,X]
  failState = Just X

q1DFA = DFA A [D] (transTableToFunc foo)
  where foo = [(A,O,B)
              ,(A,I,C)
              ,(B,I,D)
              ,(C,O,D)
              ,(D,I,B)
              ,(D,O,A)]

q1Ans = map (acceptInput q1DFA) [i1,i2,i3,i4]
