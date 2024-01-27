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

#check Nat.brecOn
-- ⊢ {motive : Nat → Sort u} →
-- (t : Nat) →
-- ((t : Nat) → Nat.below t → motive t)
-- → motive t

#check Nat.recOn
-- ⊢ {motive : Nat → Sort u} →
-- (t : Nat) →
-- motive zero →
-- ((n : Nat) → motive n → motive (succ n)) →
-- motive t

#check List.brecOn
-- ⊢ {α : Type u} →
-- {motive : List α → Sort u_1} →
-- (t : List α) →
-- ((t : List α) → List.below t → motive t) →
-- motive t

section WF

-- The concept of well-foundedness is new to me. Let me try explain it.
-- reference: http://blog.ezyang.com/2010/06/well-founded-recursion-in-agda/
--
-- The first kind of induction that I'm familiar with is called the
-- "structural recursion". On natural number it's like: 1. prove P 0,
-- 2. given P n, prove P (n+1).
--
-- But I also learned in logic there is a second kind of induction. On
-- natural number, it states: given P n for all n < x, prove P x.
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
  | acc : ∀ a, (∀ b, lt b a → Accessible lt b) → Accessible lt a

-- then the property of well-foundedness means the all elemennts of
-- type α is well-founded.

def WF (α : Type) (lt : α → α → Prop) : Prop :=
  forall (a : α), Accessible lt a

-- First we shall prove that Nat is WF over Nat.lt relation. Let's
-- show that.
theorem any_nat_is_accessible (n : Nat) : Accessible Nat.lt n := by
  induction n with
  -- zero is always accessible because there is no b < 0
  | zero => apply Accessible.acc 0; simp [Nat.not_lt_zero]
  | succ n ih =>
    apply Accessible.acc (succ n); intro m h
    cases Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ h) with
    | inl heq => rw [heq]; apply ih
    | inr hlt => -- hlt : m < n
      cases ih; rename_i ih -- ih : ∀ (b : Nat), b < n → Accessible Nat.lt b
      apply ih m hlt

#print any_nat_is_accessible

theorem nat_is_well_founded : WF Nat Nat.lt := any_nat_is_accessible


#check Accessible.rec
--{
--⊢ {α : Type} →
--    {lt : α → α → Prop} →
--      {motive : (a : α) → Accessible lt a → Sort u} →
--        ({a : α} → (a_1 : ∀ (b : α), lt b a → Accessible lt b) → ((b : α) → (a : lt b a) → motive b _) → motive a _) →
--          {a : α} → (t : Accessible lt a) → motive a t
--}

-- An element is accessible means there is a way to construct a type depending on that.
-- we call it fixF. (I use fixF' to avoid name conflict with Lean's fixF)
noncomputable def fixF' {lt : α → α → Prop} {C : α → Type}
                        (F : ∀ x, (∀ y, lt y x → C y) → C x)
                        (x : α) (acc : Accessible lt x) : C x := by
  induction acc with
  | acc y _pacc ih => apply F y ih

#check WellFounded

noncomputable def fixF'' {lt : α → α → Prop} {C : α → Type}
           {F : ∀ x, (∀ y, lt y x → C y) → C x}
           (x : α) (acc : Accessible lt x) : C x :=
  @Accessible.rec α lt
   (fun a _pacc => C a)
   (@fun y _pacc ih => F y ih)
   x
   acc

-- noncomputable modifier is needed because:
-- code generator does not support recursor 'Accessible.rec' yet, consider using 'match ... with' and/or structural recursion.

-- If i use match to define the function, i then in turn need to
-- show the function is reducing using a measure.


-- the principle of well-founded recursion is therefore defined as:
noncomputable def wf_fix {α : Type} {lt : α → α → Prop}
  {C : α → Type}
  (hwf : WF α lt)
  (F : ∀ (x : α), (∀ (y : α), lt y x → C y) → C x)
  : (x : α) → C x := fun x => fixF' F x (hwf x)

-- it defines that if we can reduce the argument a to something
-- smaller than a, then we can perform the recursion.

end WF

section WF_Usage

-- here's a demo of using well-founded induction to define division on natural numbers.
--
-- this is done by repeatedly subtracting the divisor from the dividend
-- def div_attempt (n m : Nat) : Nat :=
--   if n < m then 0 else 1 + div_attempt (n - m) m

-- this definition is not accepted by Lean because it does not know
-- the first argument (on m) is reducing. This is because the
-- definition of subtraction is not structurally recursive. We can fix
-- this by showing n - m < m for m > 0 and use a well-founded
-- recursion instead.

-- note we also need n > 0 because the definition of subtraction gives
-- 0 - x = 0 for any x.

theorem div_sub_lt (n m : Nat) (h: n > 0 ∧ m > 0) : n - m < n :=
  Nat.sub_lt h.left h.right

def div.F (x : Nat) (f : (a : Nat) -> a < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < x ∧ 0 < y then
    (f (x - y) (div_sub_lt x y h) y) + 1
  else
    0

noncomputable def div (n m : Nat) : Nat :=
  wf_fix (hwf := nat_is_well_founded) (C := fun _ => Nat → Nat)
         (F := div.F) n m

#reduce div 8 2


end WF_Usage

section List
variable {α : Type}

def replicate (n : Nat) (a : α) : List α :=
  match n with
  | 0 => []
  | n+1 => a :: replicate n a

#eval replicate 5 'a'
-- ['a', 'a', 'a', 'a', 'a']

-- #reduce replicate 5 'a'
-- maximum recursion depth has been reached

def replicate' (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
   | 0, as => as
   | n+1, as => loop n (a :: as)
  loop n []

theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [replicate, ih]


end List
