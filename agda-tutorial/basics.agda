data Bool : Set where
  true  : Bool
  false : Bool


not : Bool → Bool
not true = false
not false = true


data ℕ : Set where
  O : ℕ
  S : ℕ → ℕ


_+_ : ℕ → ℕ → ℕ
O   + a = a
S a + b = S (a + b)

_*_ : ℕ → ℕ → ℕ
O   * a = O
S a * b = a + (a * b)
