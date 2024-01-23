inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday

open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

#check Weekday

set_option pp.all true
#print numberOfDay
#print numberOfDay.match_1
#print Weekday.casesOn
#print Weekday.rec
set_option pp.all false

universe u v

inductive Vector (α : Type u) : Nat → Type u where
  | nil : Vector α 0
  | cons : {n : Nat} → α → Vector α n → Vector α (n.succ)

#check @Vector.rec
#check (@Vector.rec : {α : Type u} →
  {motive : (n : Nat) → Vector α n → Type v} →
  motive 0 Vector.nil →
  ({m : Nat} → {x : α} → {vec : Vector α m} → motive m vec →
   motive m.succ (@Vector.cons α m x vec)) →
  (n : Nat) → { vec : Vector α n } → motive n vec
)

theorem my_subst_implict {α : Sort u} {a b : α} {p : α → Prop}
  (h₁ : Eq a b) (h₂ : p a) : p b := Eq.rec h₂ h₁
theorem my_subst_implict2 {α : Sort u} {a b : α} {p : α → Prop}
  (h₁ : Eq a b) (h₂ : p a) : p b :=
    Eq.rec (motive := λ (a : α) _ => p a) h₂ h₁

#check @Eq.rec
theorem my_subst {α : Sort u} {a b : α} {p : α → Prop}
  (h₁ : Eq a b) (h₂ : p a) : p b :=
    @Eq.rec α a (λ (a' : α) (_: @Eq α a a') => p a') h₂ b h₁

namespace Datastructure
inductive List (α : Type u) : Type u where
  | nil : List α
  | cons : α → List α → List α
  deriving Repr

namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

@[simp]
theorem nil_append (as : List α) : append nil as = as :=
  rfl

@[simp]
theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
  rfl

theorem append_nil (as : List α) : append as nil = as :=
  List.recOn as (rfl : append nil nil = nil)
  (fun (b : α) bs h => by simp [h, append] :
    ∀ b bs, append bs nil = bs → append (cons b bs) nil = cons b bs)
#print append_nil
#check of_eq_true
#check congrFun

theorem append_assoc (as bs cs : List α) :
  append (append as bs) cs = append as (append bs cs) :=
  List.recOn as (by simp) (fun a as h => by simp [h])

def length : List α → Nat
  | nil       => 0
  | cons _a as => Nat.succ (length as)

def reverse : List α → List α
  | nil       => nil
  | cons a as => append (reverse as) (cons a nil)

#eval reverse (cons 1 (cons 2 (cons 3 nil)))

theorem length_append (as bs : List α) :
        length (append as bs) = length as + length bs := by
  induction as with
  | nil => simp [length]
  | cons a as ih => simp [length, ih, Nat.succ_add]

theorem length_reverse (as : List α) :
        length (reverse as) = length as := by
  induction as with
  | nil => simp [length]
  | cons a as ih => simp [length, ih, reverse, length_append]

theorem reverse_append (as bs : List α) :
        reverse (append as bs) = append (reverse bs) (reverse as) := by
  induction as with
  | nil => simp [reverse, append, append_nil]
  | cons a as ih => simp [reverse, ih, append_assoc]

theorem reverse_reverse (as : List α) :
        reverse (reverse as) = as := by
  induction as with
  | nil => simp [reverse]
  | cons a as ih => simp [reverse, ih, append_assoc, reverse_append]

end List
end Datastructure

section exercise

-- 1. define more operations on nat
inductive N where
  | zero
  | succ (n : N)
open N
#check N.rec
-- ⊢ {motive : N → Sort u} →
--   motive N.zero →
--   ((n : N) → motive n → motive (N.succ n)) →
--   (t : N) → motive t

theorem pred (n : N) : N := N.rec (motive := λ _ => N) N.zero (λ m _ => m) n
-- using def gives "code generator does not support recursor 'N.rec' yet, consider using 'match ... with' and/or structural recursion"

def plus (n : N) (m : N) := match n with
  | zero => m
  | succ n' => succ (plus n' m)


@[simp]
theorem plus_n_zero (n : N) : plus n zero = n := by
  induction n with
  | zero => rfl
  | succ n' ih => simp [plus, ih]

@[simp]
theorem plus_n_succ_m (n : N) (m : N) : plus n (succ m) = succ (plus n m) := by
  induction n with
  | zero => rfl
  | succ n' ih => simp [plus, ih]

@[simp]
theorem plus_comm (n : N) (m : N) : plus n m = plus m n := by
  induction n with
  | zero => simp [plus]
  | succ n' ih => simp [plus, ih]
@[simp]
theorem plus_assoc (n : N) (m : N) (k : N) : plus (plus n m) k = plus n (plus m k) := by
  induction n with
  | zero => simp [plus]
  | succ n' ih => simp [plus]; rw [←ih, plus_comm]; simp

def mult (n : N) (m : N) := match n with
  | zero => zero
  | succ n' => plus (mult n' m) m

@[simp]
theorem mult_succ_n_m (n : N) (m : N) : mult (succ n) m = plus (mult n m) m := by rfl
@[simp]
theorem mult_n_zero (n : N) : mult n zero = zero := by
  induction n with
  | zero => rfl
  | succ n' ih => simp [mult, ih]
@[simp]
theorem mult_n_one (n : N) : mult n (succ zero) = n := by
  induction n with
  | zero => rfl
  | succ n' ih => simp [mult, ih]
@[simp]
theorem mult_n_succ_m (n : N) (m : N) : mult n (succ m) = plus (mult n m) n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp [mult, ih]
    clear ih
    rw [←plus_assoc, ←plus_assoc, plus_comm n' m]

@[simp]
theorem mult_comm (n : N) (m : N) : mult n m = mult m n := by
  induction n with
  | zero => simp [mult]
  | succ n' ih => simp [mult, ih, mult_n_succ_m, plus_comm]

@[simp]
theorem mult_dist (n : N) (m : N) (k : N) :
  mult k (plus n m) = plus (mult k n) (mult k m) := by
  induction k with
  | zero => simp [mult]
  | succ k' ih =>
      simp [mult, ih]
      rw [←plus_assoc m, plus_comm m (mult n k'), plus_assoc _ m]

@[simp]
theorem mult_assoc (n : N) (m : N) (k : N) :
        mult (mult n m) k = mult n (mult m k) := by
  induction n with
  | zero => simp [mult]
  | succ n' ih => simp [mult, ←ih]

section nat_expr

inductive nat_expr where
  | const (n : Nat) : nat_expr
  | var  (v : Nat) : nat_expr
  | plus (s : nat_expr) (t : nat_expr) : nat_expr
  | times (s : nat_expr) (t : nat_expr) : nat_expr

def assgn := List (Nat × Nat)

def lookup (v : Nat) : assgn → Nat
  | [] => 0
  | (x, n) :: xns => if x = v then n else lookup v xns

def eval_nat_expr (as : assgn) (e : nat_expr) :=
  match e with
  | nat_expr.const n => n
  | nat_expr.var v => lookup v as
  | nat_expr.plus s t => eval_nat_expr as s + eval_nat_expr as t
  | nat_expr.times s t => eval_nat_expr as s * eval_nat_expr as t

#eval eval_nat_expr [(0, 3), (1, 4)] (nat_expr.plus (nat_expr.var 0) (nat_expr.var 1))
-- 7

end nat_expr
namespace bool_expr

inductive bool_expr where
  | const (b : Bool) : bool_expr
  | var (v : Nat) : bool_expr
  | and (s : bool_expr) (t : bool_expr) : bool_expr
  | or (s : bool_expr) (t : bool_expr) : bool_expr
  | not (s : bool_expr) : bool_expr

def lookup_bool (v : Nat) : assgn → Bool
  | [] => false
  | (x, n) :: xns => if x = v then n else lookup v xns

def eval_bool_expr (as : assgn) : bool_expr → Bool
  | bool_expr.const b => b
  | bool_expr.var v => lookup_bool v as
  | bool_expr.and s t => eval_bool_expr as s && eval_bool_expr as t
  | bool_expr.or s t => eval_bool_expr as s || eval_bool_expr as t
  | bool_expr.not s => !eval_bool_expr as s

def subst_var (v : Nat) (v' : Nat) : bool_expr → bool_expr
  | bool_expr.const b => bool_expr.const b
  | bool_expr.var v'' => if v'' = v then bool_expr.var v' else bool_expr.var v''
  | bool_expr.and s t => bool_expr.and (subst_var v v' s) (subst_var v v' t)
  | bool_expr.or s t => bool_expr.or (subst_var v v' s) (subst_var v v' t)
  | bool_expr.not s => bool_expr.not (subst_var v v' s)

def complexity : bool_expr → Nat
  | bool_expr.const _ => 0
  | bool_expr.var _ => 0
  | bool_expr.and s t => max (complexity s) (complexity t) + 1
  | bool_expr.or s t => max (complexity s) (complexity t) + 1
  | bool_expr.not s => complexity s + 1

end bool_expr
end exercise
