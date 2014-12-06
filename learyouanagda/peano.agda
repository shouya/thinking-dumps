module peano where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ

zero + n     = n
(suc n) + n′ = suc (n + n′)


data _even : ℕ → Set where
  ZERO : zero even
  STEP : ∀ x → x even → (suc (suc x)) even


-- To prove four is even
proof₁ : suc (suc (suc (suc zero))) even
proof₁ = STEP (suc (suc zero)) (STEP zero ZERO)

proof₂′ : (A : Set) → A → A
proof₂′ _ a = a

proof₂ : ℕ → ℕ
proof₂ = proof₂′ ℕ
