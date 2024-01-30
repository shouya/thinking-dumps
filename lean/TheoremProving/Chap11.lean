example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in (b * _) => rw [Nat.mul_comm]
example (a b c : Nat) : (a * 1) * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    . rw [Nat.mul_one]
    . rw [Nat.mul_comm]
