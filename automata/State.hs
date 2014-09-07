module State where

class State a where
  allStates :: [a]
  failState :: Maybe a

class (State a) => IntState a where
  stateNo :: a -> Integer
