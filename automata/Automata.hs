{-# LANGUAGE GADTs #-}

import qualified Data.Set as S

class State a where
  startState :: a
  acceptStates :: S.Set a
  failState :: a

class Input i where
  epsilon :: i


data DFA s i where
  DFA :: (State s, Input i) => (s -> i -> s) -> DFA s i

data NFA s i where
  NFA :: (State s, Input i) => (s -> i -> S.Set s) -> NFA s i



evalDFA :: DFA s i -> [i] -> s
evalDFA (DFA d) xs = foldl d startState xs


-- Example Input
data MyInput = Zero | One | Epsilon deriving Show
instance Input MyInput where
  epsilon = Epsilon

-- Example State
data MyState = A | B | C | D | E | F deriving Show
instance State MyState where
  startState = A
  acceptStates = S.singleton F
  failState = F


myDFA :: DFA MyState MyInput
myDFA = DFA myDelta where
  myDelta A One  = B
  myDelta A Zero = C
  myDelta B One  = D
  myDelta B Zero = C
  myDelta C One  = D
  myDelta _ _    = F
