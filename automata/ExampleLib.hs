module ExampleLib where

import Input

data BinaryInput = O | I deriving (Eq,Ord,Bounded)
type BI = BinaryInput

instance Show BinaryInput where
  show O = "0"
  show I = "1"

instance Input BinaryInput where
  allInputs = [O, I]


type MyIntState = Integer
