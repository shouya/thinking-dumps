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

-- the lean framework is based on the system of universes, dependent type, inductive types with the following components:
--
-- 1. axiom of propositional extensionality
-- 2. quotient construct (with implies function extensionality)
-- 3. choice principle

-- In the Diaconescu namespace I proved the law of excluded middle is a result of 1,2,3.

namespace Quotient

#check propext

#check Quot.mk
-- ⊢ {α : Sort u} → (r : α → α → Prop) → α → Quot r

#check Quot.ind
-- ⊢ ∀ {α : Sort u} {r : α → α → Prop}
--     {β : Quot r → Prop},
--     (∀ (a : α), β (Quot.mk r a)) →
--     ∀ (q : Quot r), β q

#check Quot.lift
-- ⊢ {α : Sort u} → {r : α → α → Prop} → {β : Sort v} →
--   (f : α → β) →
--   (∀ (a b : α), r a b → f a = f b) →
--   Quot r → β

#check Quot.sound
-- ⊢ ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b

variable (r s r' r'' : α → α → Prop)

def liftR (a b : α) : Prop := Quot.mk r a = Quot.mk r b

def Rcontains (s : α → α → Prop) : Prop := ∀ (a b : α), s a b → r a b

infix:50 " ⊆ " => Rcontains

theorem liftR_contains_R : liftR r ⊆ r :=
  fun _a _b h => Quot.sound h

-- forall b, quot r a = quot r b -> r a b
-- β := λ b => Quot.mk r a = Quot.mk r b -> r a b
-- induction gives

-- theorem R_contains_liftR : r ⊆ liftR r :=
--   fun a b h =>
--     have β := λ qb => Quot.mk r a = qb -> r a b
--     have f : ∀ b', Quot.mk r a = Quot.mk r b' -> r a b' := by sorry
--     f b h
-- this is not provable without the constraint that r is an equivalence relation.
--
-- here's a counter example: Let r a b := False. Quot.mk r a = Quot.mk r a is always true, which implies r a a (contradiction).

-- theorem liftR_smallest : (r'' ⊆ r) → (r'' ⊆ liftR r) :=
--   fun r'' h a b r' => by
--     simp [Rcontains, liftR] at *;
--     have : r a b := sorry
--     exact h _ _ this

end Quotient


namespace UProd
variable {α : Type u}

-- unordered pair
def eqv (p₁ p₂ : α × α) : Prop := p₁.1 = p₂.1 ∧ p₁.2 = p₂.2 ∨ p₁.1 = p₂.2 ∧ p₁.2 = p₂.1
infix:50 " ~ " => eqv

theorem eqv.refl (p : α × α) : p ~ p := by cases p; simp [eqv]
theorem eqv.symm {p₁ p₂ : α × α} : p₁ ~ p₂ → p₂ ~ p₁ :=
  by intro h; cases h <;> rename_i h <;> cases h <;> simp [eqv, *]
theorem eqv.trans {p₁ p₂ p₃ : α × α} : p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃ :=
  by intro h₁ h₂; cases h₁ <;> rename_i h₁ <;> cases h₁ <;> cases h₂ <;> rename_i h₂ <;> cases h₂ <;> simp [eqv, *]

instance uprodSetoid : Setoid (α × α) where
  r := eqv
  iseqv := ⟨eqv.refl, eqv.symm, eqv.trans⟩

def UProd (α : Type u) := Quotient (@uprodSetoid α)

def mk (a b : α) : UProd α := Quotient.mk' (a, b)

notation "{{" a ", " b "}}" => mk a b

theorem mk_eq_mk (a b : α) : {{a,  b}} = {{b, a}} := by
  apply Quotient.sound; apply Or.inr; simp

def mem_fn (a : α) (p : α × α) : Prop := a = p.1 ∨ a = p.2

def mem_respects {p₁ p₂ : α × α} (h : p₁ ~ p₂) : ∀ a, mem_fn a p₁ = mem_fn a p₂ :=
  fun a => by match h with
    | Or.inl ⟨h₁, h₂⟩ => congr; rw [←Prod.eta p₁, ←Prod.eta p₂, h₁, h₂]
    | Or.inr ⟨h₁, h₂⟩ =>
      unfold mem_fn; simp; apply Iff.intro
      . intro h; cases h <;> simp [*]
      . intro h; cases h <;> simp [*]

def mem (a : α) (p : UProd α) : Prop :=
  Quotient.lift (mem_fn a) (fun _p₁ _p₂ h => mem_respects h a) p

infix:50 (priority := high) " ∈ " => mem

end UProd

-- Let me prove the non dependent-type version of function
-- extensionality. The type is cleaner this way. but the same proof
-- applies to the dependent type version as well.
namespace Funext

def f_eqv {α β} (f g : α → β) : Prop := ∀ x, f x = g x

theorem f_eqv.id (f : α → β) : f_eqv f f := fun x => rfl
theorem f_eqv.symm {f g : α → β} : f_eqv f g → f_eqv g f := fun h x => (h x).symm
theorem f_eqv.trans {f g h : α → β} : f_eqv f g → f_eqv g h → f_eqv f h :=
  fun fg gh x => Eq.trans (fg x) (gh x)

instance extfunSetoid α β : Setoid (α → β) where
  r := f_eqv
  iseqv := ⟨f_eqv.id, f_eqv.symm, f_eqv.trans⟩

def Extfun α β := Quotient (extfunSetoid α β)

def Extfun.app {α β} (f : Extfun α β) (x : α) : β := by
  apply Quotient.liftOn f (fun g => g x)
  intro g₁ g₂ heqv
  exact heqv x

def Extfun.mk {α β} (f : α → β) : Extfun α β := Quotient.mk' f

def funext {f g : α → β} (h : ∀ x, f x = g x) : f = g := by
  let fext : Extfun α β := Extfun.mk f
  let gext : Extfun α β := Extfun.mk g
  let heq1 : f = Extfun.app fext := by rfl
  let heq2' : fext = gext := Quotient.sound h
  let heq2 : Extfun.app fext = Extfun.app gext := by rw [heq2']
  let heq3 : Extfun.app gext = g := by rfl
  exact heq1 ▸ heq2 ▸ heq3

#check funext
-- |- {f g : α → β} (h : ∀ (x : α), f x = g x) : f = g

end Funext
