module State where

class State a where
  allStates :: [a]
  failState :: Maybe a


class (State a) => IntState a where
-- starting from zero, consecutive
  stateNo :: a -> Integer

noToState :: (IntState a) => Integer -> a
noToState n = case lookup n $ zip (map stateNo allsts) allsts of
  Just st -> st
  Nothing -> error ("not found " ++ show n)
  where allsts = allStates
