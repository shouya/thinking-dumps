import DFA
import Input
import State

import ExampleLib

-- Example Input

-- Example State
data MyState = A | B | C | D | E deriving (Eq,Show)
instance State MyState where
  allStates = [A, B, C, D, E]
  failState = Just E


myDFA :: DFA MyState BinaryInput
myDFA = DFA A [D] myDelta where
  myDelta A I = B
  myDelta A O = C
  myDelta B I = D
  myDelta B O = C
  myDelta C I = D
  myDelta _ _    = E
