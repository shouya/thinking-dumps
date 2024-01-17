import Std.Logic

example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (any_goals (apply And.intro)); all_goals repeat (first | apply Or.inl; assumption | apply Or.inr; assumption | apply Or.inr)

-- redoing chapter 3 using tactics
variable (p q r : Prop)

example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  apply And.symm
  apply And.symm

example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro <;> intro ⟨a, b⟩ <;> constructor <;> assumption

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro <;> intro h <;> cases h <;> rename_i h <;>
    first | exact Or.inl h | exact Or.inr h

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro <;> intro <;> simp [*]

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro <;> intro h <;>
  cases h <;> rename_i h; any_goals (cases h <;> rename_i h)
  all_goals simp [h]

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro <;> intro h
  . simp [h]
  . cases h <;> simp [*]

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro <;> intro h
  . cases h <;> simp [*]
  . cases h; rename_i hl hr; cases hl <;> cases hr <;> simp [*]

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . intro f ⟨p, q⟩; exact f p q
  . intro f p q; exact f ⟨p, q⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  . intro f; apply And.intro
    . intro p; exact f (Or.inl p)
    . intro q; exact f (Or.inr q)
  . intro ⟨pr, qr⟩ pq
    apply Or.elim pq pr qr

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  . intro f; apply And.intro
    . intro p; exact f (Or.inl p)
    . intro q; exact f (Or.inr q)
  . intro f; intro g; cases g
    . apply f.left; assumption
    . apply f.right; assumption

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intros a b; cases a <;> cases b <;> contradiction

example : ¬(p ∧ ¬p) := by simp

example : p ∧ ¬q → ¬(p → q) := by simp
example : ¬p → (p → q) := by intros; contradiction
example : (¬p ∨ q) → (p → q) := by
  intros h hp; cases h <;> first | contradiction | assumption

example : p ∨ False ↔ p := by
  apply Iff.intro
  . intro
    | Or.inl p => exact p
    | Or.inr f => exact f.elim
  . apply Or.inl

example : p ∧ False ↔ False := by
  apply Iff.intro
  . intro h; exact h.right.elim
  . intro h; exact h.elim

example : (p → q) → (¬q → ¬p) := by
  intros h nq p; have q := h p; contradiction

example : ¬(p ↔ ¬p) := by
  intro ⟨p'np, np'p⟩
  have hnp : ¬p := fun hp => p'np hp hp
  have hp : p := np'p hnp
  contradiction


open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro p'qr
  by_cases hp : p
  . apply Or.elim (p'qr hp)
    . intro q; apply Or.inl; intro; assumption
    . intro r; apply Or.inr; intro; assumption
  . apply Or.inl
    intro p
    contradiction -- p vs np

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro np'q
  by_cases hp : p
  . apply Or.inr; intro hq
    exact np'q ⟨hp, hq⟩
  . apply Or.inl; assumption

example : ¬(p → q) → p ∧ ¬q := by
  intros np'q
  by_cases hp : p
  . simp [hp]
    intro hq; apply absurd _ np'q; simp [hq]
  . apply absurd _ np'q; simp [hp]

example : (p → q) → (¬p ∨ q) := by
  intros pq; by_cases hp : p <;> simp [*]

example : (¬q → ¬p) → (p → q) := by
  intros nq'np hp
  by_cases hq : q <;> any_goals simp [*]
  simp [*] at nq'np

example : p ∨ ¬p := by
  by_cases hp : p <;> simp [hp]

example : (((p → q) → p) → p) := by
  by_cases hp : p <;> simp [hp]
  -- magical!
