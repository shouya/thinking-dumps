module Input where

import Data.List

class Input a where
  allInputs :: [a]

star :: (Input a) => [[a]]
star = subsequences allInputs
