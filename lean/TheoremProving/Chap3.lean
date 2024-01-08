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

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  . intro f; apply And.intro
    . intro p; exact f (Or.inl p)
    . intro q; exact f (Or.inr q)
  . intro f; intro g; cases g
    . apply f.left; assumption
    . apply f.right; assumption

example : ¬p ∨ ¬q → ¬(p ∧ q) := fun h ⟨hp, hq⟩ =>
  Or.elim h (fun np => np hp) (fun nq => nq hq)

example : ¬(p ∧ ¬p) := fun ⟨p, np⟩ => np p
example : p ∧ ¬q → ¬(p → q) := fun ⟨p, nq⟩ pq => nq (pq p)
example : ¬p → (p → q) := fun np p => False.elim (np p)
example : (¬p ∨ q) → (p → q) :=
  fun npq p => Or.elim npq (fun np => absurd p np) id
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

example : (p → q) → (¬q → ¬p) := fun pq nq p => nq (pq p)

example : ¬(p ↔ ¬p) := fun ⟨p'np, np'p⟩ =>
  (fun np => absurd (np'p np) np)
  (fun p => absurd p (p'np p))

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

example : ¬(p → q) → p ∧ ¬q :=
  match em p with
  | Or.inl hp => fun npq => ⟨hp, fun hq => npq (fun _ => hq)⟩
  | Or.inr hnp => fun npq => (npq (fun hp => absurd hp hnp)).elim

example : (p → q) → (¬p ∨ q) := fun hpq =>
  match em p with
  | Or.inl hp => Or.inr (hpq hp)
  | Or.inr hnp => Or.inl hnp

example : (¬q → ¬p) → (p → q) := fun nq'np =>
  match em q with
  | Or.inl hq => fun _ => hq
  | Or.inr hnq => fun p => absurd p (nq'np hnq)

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) := fun pqpp =>
  match em p with
  | Or.inl hp  => hp
  | Or.inr hnp => pqpp (fun hp => absurd hp hnp)
