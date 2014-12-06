module IPL where


data _∧_ (P : Set) (Q : Set) : Set where
  ∧-intro : P → Q → (P ∧ Q)


proof₁ : {P Q : Set} → (P ∧ Q) → P
proof₁ (∧-intro p q) = p

proof₂ : {P Q : Set} → (P ∧ Q) → Q
proof₂ (∧-intro p q) = q


_⇔_ : (P : Set) → (Q : Set) → Set
a ⇔ b = (a → b) ∧ (b → a)


∧-comm′ : (P Q : Set) → (P ∧ Q) → (Q ∧ P)
∧-comm′ _ _ (∧-intro p q) = ∧-intro q p

∧-comm : (P Q : Set) → (P ∧ Q) ⇔ (Q ∧ P)
∧-comm P Q = ∧-intro (∧-comm′ P Q) (∧-comm′ Q P)


∧-comm1′ : {P Q : Set} → (P ∧ Q) → (Q ∧ P)
∧-comm1′ (∧-intro p q) = ∧-intro q p

∧-comm1 : {P Q : Set} → (P ∧ Q) ⇔ (Q ∧ P)
∧-comm1 = ∧-intro ∧-comm1′ ∧-comm1′
