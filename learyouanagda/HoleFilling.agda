module HoleFilling where

data Bool : Set where
  false : Bool
  true  : Bool

_∧_ : Bool → Bool → Bool
false ∧ b = false
true ∧ b  = b
