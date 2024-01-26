open Nat
def add (m: Nat) : Nat → Nat
  | 0 => m
  | n + 1 => (add m n) + 1

#print add

def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n


def fibFast (n : Nat) : Nat := (loop n).2
where
  loop : Nat → (Nat × Nat)
    | 0   => (0, 1)
    | n+1 => let (a, b) := loop n; (b, a+b)

-- theorem fib_eq_fib_fast : ∀ n, fib n = fibFast n
--   | 0   => by rfl
--   | 1   => by rfl
--   | n+2 => by
--     simp [fib, fibFast, fibFast.loop]

-- The concept of well-foundedness is new to me. Let me try explain it.
-- reference: http://blog.ezyang.com/2010/06/well-founded-recursion-in-agda/
--
-- The first kind of induction that I'm familiar with is called the
-- "structural recursion". On natural number it's like: 1. prove P 0,
-- 2. given P n, prove P (n+1).
--
-- But I also learned in logic there is a second kind of induction. On
-- natural number, it states, 1. prove P 0, 2. given P n for all n < x, prove P x.
-- The second kind of induction is called "well-founded induction".

-- well-founded induction works on types that satisfies a property
-- called well-foundedness, which is defined in terms of accessibility
-- of the elements of the types.

-- what is accessibility? accessibility is in-turn defined on top of a
-- type (or a set; let's name it A) and a relation (A → A → Prop). We
-- shall call this relation "<". An element of (a : A) is accessible,
-- definitionally, only if forall (b : A) where b < a, b is
-- accessible. This gives us the definition accessibility:

#print Acc
#print WellFounded

inductive Accessible {α : Type} (lt : α → α → Prop) : α → Prop where
  | acc : (∀ b, lt b a → Accessible lt b) → Accessible lt a

-- then the property of well-foundedness means the all elemennts of
-- type α is well-founded.

def WF (α : Type) (lt : α → α → Prop) : Prop :=
  forall (a : α), Accessible lt a

-- First we shall prove that Nat is WF over Nat.lt relation. Let's
-- show that.
theorem any_nat_is_accessible (n : Nat) : Accessible Nat.lt n := by
  let rec aux : ∀ (a b : Nat), b < a -> Accessible Nat.lt b := by
    intro a b h; induction h
    . apply any_nat_is_accessible
    . rename_i ih; apply ih
  exact Accessible.acc (aux n)

theorem nat_is_well_founded : WF Nat Nat.lt := by
  simp [WF, any_nat_is_accessible]
