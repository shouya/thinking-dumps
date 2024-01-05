import Std.Logic

variable (p q r : Prop)

-- commutativity of ∧ and ∨
-- first attempt: functional elim and intro
example : p ∧ q ↔ q ∧ p := Iff.intro
  (fun h : p ∧ q => And.intro h.right h.left)
  (fun h : q ∧ p => And.intro (And.right h) (And.left h))

-- second attempt: using std theorem
example : p ∧ q ↔ q ∧ p := Iff.intro (Iff.mp And.comm) (Iff.mpr And.comm)
-- second.1 attempt: cheating
example : p ∧ q ↔ q ∧ p := And.comm

-- third attempt: using proof mode
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  apply And.symm
  apply And.symm

-- fourth attempt: using structured proof terms
example : p ∧ q ↔ q ∧ p := Iff.intro
  (fun h : p ∧ q =>
    have hp : p := h.left
    have hq : q := h.right
    show q ∧ p from And.intro hq hp)
  (fun h : q ∧ p =>
    have hq : q := h.left
    have hp : p := h.right
    show p ∧ q from And.intro hp hq)

example : p ∨ q ↔ q ∨ p := Iff.intro
  (fun o => Or.elim o Or.inr Or.inl)
  (fun o => Or.elim o Or.inr Or.inl)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  have forward (h : (p ∧ q) ∧ r) : p ∧ (q ∧ r) :=
    have hp : p := h.left.left
    have hq : q := h.left.right
    have hr : r := h.right
    show p ∧ (q ∧ r) from ⟨hp, ⟨hq, hr⟩⟩
  have backward (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r :=
    have hp : p := h.left
    have hq : q := h.right.left
    have hr : r := h.right.right
    show (p ∧ q) ∧ r from ⟨⟨hp, hq⟩, hr⟩
  Iff.intro forward backward

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  have forward (h : (p ∨ q) ∨ r) : p ∨ (q ∨ r) := match h with
    | Or.inl (Or.inl hp) => Or.inl hp
    | Or.inl (Or.inr hq) => Or.inr (Or.inl hq)
    | Or.inr hr => Or.inr (Or.inr hr)
  have backward (h : p ∨ (q ∨ r)) : (p ∨ q) ∨ r := match h with
    | Or.inl hp => Or.inl (Or.inl hp)
    | Or.inr (Or.inl hq) => Or.inl (Or.inr hq)
    | Or.inr (Or.inr hr) => Or.inr hr
  Iff.intro forward backward

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  have forward (h : (p ∧ (q ∨ r))) : (p ∧ q) ∨ (p ∧ r) :=
    have hp : p := h.left
    match h.right with
      | Or.inl hq => Or.inl ⟨hp, hq⟩
      | Or.inr hr => Or.inr ⟨hp, hr⟩
  have backward (h : (p ∧ q) ∨ (p ∧ r)) : (p ∧ (q ∨ r)) :=
    match h with
      | Or.inl ⟨hp, hq⟩ => ⟨hp, Or.inl hq⟩
      | Or.inr ⟨hp, hr⟩ => ⟨hp, Or.inr hr⟩
  Iff.intro forward backward

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  . intro
    | Or.inl hp => exact ⟨Or.inl hp, Or.inl hp⟩
    | Or.inr ⟨hq, hr⟩ => exact ⟨Or.inr hq, Or.inr hr⟩
  . intro
    | ⟨Or.inl hp, _⟩ => exact Or.inl hp
    | ⟨_, Or.inl hp⟩ => exact Or.inl hp
    | ⟨Or.inr hq, Or.inr hr⟩ => apply Or.inr; constructor <;> assumption

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

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
