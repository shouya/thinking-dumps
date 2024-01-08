variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  . intro h; apply And.intro
    . intro x; exact (h x).left
    . intro x; exact (h x).right
  . intro h; intro x
    exact ⟨h.left x, h.right x⟩

--- functional proof
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
  (fun h => ⟨fun x => (h x).left, fun x => (h x).right⟩)
  (fun h x => ⟨h.left x, h.right x⟩)


example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun hpq hp x => hpq x (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun hp'q x => match hp'q with
    | Or.inl hp => Or.inl (hp x)
    | Or.inr hq => Or.inr (hq x)

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _x : α, r) ↔ r) :=
  fun t : α => Iff.intro (fun p => p t) (fun h _ => h)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  match Classical.em r with
  | Or.inl hr  => Iff.intro (λ _ => Or.inr hr)
                            (λ _ _x => Or.inr hr)
  | Or.inr hnr =>
    Iff.intro
    (λ h => Or.inl (λ x => Or.elim (h x) id (absurd · hnr)))
    (λ h x => Or.inl ((Or.elim h id (absurd · hnr)) x))

-- syntax: (a · b) desugars to fun x => a x b
-- https://github.com/leanprover/lean4/blob/master/doc/lean3changes.md#sugar-for-simple-functions

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := Iff.intro
  (fun h r x => h x r)
  (fun h x r => h r x)

namespace Russell -- avoid polluting the namespace
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  match Classical.em (shaves barber barber) with
  | Or.inl hβ => absurd hβ ((h barber).mp hβ)
  | Or.inr hnβ => absurd ((h barber).mpr hnβ) hnβ
end Russell

def even (n : Nat) : Prop := ∃ k, n = 2 * k
theorem some_num_is_even : ∃ n, even n := ⟨2, ⟨1, rfl⟩⟩

def prime (n : Nat) : Prop := ¬∃ p q,
  (p ≠ 1) ∧
  (q ≠ 1) ∧
  (p ≠ n) ∧
  (q ≠ n) ∧
  (n = p * q)

-- there is no upper limit on the value of a prime
def infinitely_many_primes : Prop := ¬∃ n, ∀ p, prime p -> n > p

def Fermat_prime (n : Nat) : Prop := prime (2 ^ (2 ^ n))

def infinitely_many_Fermat_primes : Prop :=
  ¬∃ n, ∀ p, Fermat_prime p -> n > p

def goldbach_conjecture : Prop :=
  ∀ n, n > 2 → even n → ∃ p q, prime p ∧ prime q ∧ n = p + q

def Goldbach's_weak_conjecture : Prop :=
  ∀ n, n > 5 → ¬(even n) → ∃ p q r,
  prime p ∧ prime q ∧ prime r ∧ n = p + q + r

def Fermat's_last_theorem : Prop :=
  ∀ n, n > 3 → ¬∃ (a b c : Nat), a ^ n + b ^ n = c ^ n
