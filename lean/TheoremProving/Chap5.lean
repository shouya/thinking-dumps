----- Chapter 3 ---------
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


------ Chapter 4 ----------
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  . intro h; apply And.intro
    . intro x; exact (h x).left
    . intro x; exact (h x).right
  . intro h; intro x
    exact ⟨h.left x, h.right x⟩

--- functional proof
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro <;> intros <;> simp [*]

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intros; simp [*]

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intros h; cases h <;> simp [*]

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _x : α, r) ↔ r) := by
  intros a; apply Iff.intro
  . intro f; exact f a
  . intros r _; assumption

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  by_cases hr : r <;> simp [hr]

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro <;> intros <;> simp [*]

namespace Russell -- avoid polluting the namespace
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  by_cases hx : shaves barber barber
  . have ⟨h1, _h2⟩ := h barber
    have hx' := h1 hx
    contradiction
  . have ⟨_h1, h2⟩ := h barber
    have hx' := h2 hx
    contradiction

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _x : α, r) → r := by intro ⟨_x, r⟩; assumption
example (a : α) : r → (∃ _x : α, r) := by intro r; exact ⟨a, r⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  . intro ⟨x, ⟨px, r⟩⟩; exact ⟨⟨x, px⟩, r⟩
  . intro ⟨⟨x, px⟩, r⟩; exact ⟨x, ⟨px, r⟩⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  . intro ⟨x, pq⟩; cases pq
    . apply Or.inl; constructor <;> assumption
    . apply Or.inr; constructor <;> assumption
  . intro pq; match pq with
    | Or.inl ⟨x, px⟩ => exact ⟨x, Or.inl px⟩
    | Or.inr ⟨x, qx⟩ => exact ⟨x, Or.inr qx⟩

theorem not_exist_nonred_apple_iff_all_apples_red
  : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by simp only [not_exists, not_not]
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by simp only [not_exists, not_not]
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by simp only [not_forall, not_not]
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by simp only [not_exists]
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by simp only [not_forall]
example : (∀ x, (p x → r)) ↔ ((∃ x, p x) → r) := by simp only [forall_exists_index]

example (a : α) : (∃ x, (p x → r)) ↔ ((∀ x, p x) → r) := by
  apply Iff.intro
  . intro ⟨x, pxr⟩ hpx; simp [*]
  . intro h; by_cases hpx : ∀ x, p x
    . simp [*] at *; constructor <;> first | simp | assumption
    . have ⟨x, np⟩ := not_forall.mp hpx; clear hpx
      exact ⟨x, fun px => absurd px np⟩

example (a : α) : (∃ x, (r → p x)) ↔ (r → (∃ x, p x)) := by
  apply Iff.intro
  . intros; simp [*] at *; assumption
  . intro h; by_cases hr : r
    . simp [*] at *
    . simp [*] at *; constructor <;> assumption
