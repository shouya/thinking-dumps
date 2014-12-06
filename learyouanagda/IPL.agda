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



data _∨_ (P Q : Set) : Set where
   ∨-intro₁ : P → P ∨ Q
   ∨-intro₂ : Q → P ∨ Q


∨-elim : {A B C : Set} → (A → C) → (B → C) → (A ∨ B) → C
∨-elim ac bc (∨-intro₁ a) = ac a
∨-elim ac bc (∨-intro₂ b) = bc b


∨-comm′ : {A B : Set} → (A ∨ B) → (B ∨ A)
∨-comm′ (∨-intro₁ a) = ∨-intro₂ a
∨-comm′ (∨-intro₂ b) = ∨-intro₁ b

∨-comm : {A B : Set} → (A ∨ B) ⇔ (B ∨ A)
∨-comm = ∧-intro ∨-comm′ ∨-comm′

