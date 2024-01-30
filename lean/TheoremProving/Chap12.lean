import Mathlib.Data.Set.Basic

-- Using a clever trick (known as Diaconescu's theorem), one can use propositional extensionality, function extensionality, and choice to derive the law of the excluded middle. As noted above, however, use of the law of the excluded middle is still compatible with bytecode compilation and code extraction, as are other classical principles, as long as they are not used to manufacture data.

-- Let me try it.

namespace Diaconescu

variable {α : Type}

open Set

#check propext
-- ⊢ ∀ {a b : Prop}, (a ↔ b) → a = b
#check funext
-- ⊢ ∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α), f x = g x) → f = g
#check Classical.choice
-- ⊢ {α : Sort u} → Nonempty α → α
-- ^ note: Nonempty α is a Prop, so the information about the element is erased.


-- def Set (α : Type) : Type := α → Prop

#check @Set.Nonempty
-- ⊢ {α : Type u_1} → Set α → Prop

#check @Set.Nonempty.some
-- ⊢ {α : Type u_1} → {s : Set α} → Set.Nonempty s → α
#check @Set.Nonempty.some_mem
-- ⊢ ∀ {α : Type u_1} {s : Set α} (h : Set.Nonempty s), Set.Nonempty.some h ∈ s
-- Note that (h ∈ s) := s h
-- ^ this is where the magic happens.

#check @Set.ext
-- ⊢ ∀ {α : Type u_1} {a b : Set α}, (∀ (x : α), x ∈ a ↔ x ∈ b) → a = b
-- ⊢ ∀ {α : Type u_1} {a b : Set α}, (∀ (x : α), a x ↔ b x) → a = b

theorem diaconescu (p : Prop) : p ∨ ¬p := by
    let U := { x | x = true  ∨ p }
    let V := { x | x = false ∨ p }

    have p_implies_UV  : p → U = V := by
      intro hp; apply ext; intro x; cases x <;> intros <;> simp [U, V, *]

    have exU : U.Nonempty := ⟨true, Or.inl rfl⟩
    have exV : V.Nonempty := ⟨false, Or.inl rfl⟩
    -- uses axiom of choice
    let u : Bool := exU.some
    let v : Bool := exV.some

    have uv_or_p : u ≠ v ∨ p :=
      match exU.some_mem, exV.some_mem with
      | Or.inr p, _ => Or.inr p
      | _, Or.inr p => Or.inr p
      | Or.inl h1, Or.inl h2 => Or.inl (by simp [true_ne_false, *])
    have uv_implies_p  : u = v → p := fun h => Or.neg_resolve_left uv_or_p h
    have p_implies_uv  : p → u = v := fun hp => by
      have : U = V := p_implies_UV hp
      simp [u, v]; congr -- really weird
    have uv_implies_np : u ≠ v → ¬p := fun h hp => h (p_implies_uv hp)

    have eq_or_not : u = v ∨ u ≠ v := by cases u <;> cases v <;> simp [*]
    match eq_or_not with
    | Or.inl huv => exact Or.inl (uv_implies_p huv)
    | Or.inr huv => exact Or.inr (uv_implies_np huv)

end Diaconescu
