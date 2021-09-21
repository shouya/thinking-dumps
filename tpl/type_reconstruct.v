Require Import Coq.Strings.String.
Open Scope string_scope.

Inductive typ : Type :=
| TyBase : string -> typ
| TyFun : typ -> typ -> typ
.

Inductive term : Type :=
| TVar (var: string) : term
| TLam (var: string) (typ: typ) (body: term) : term
| TApp (operator: term) (operand: term) : term
| TIf (cond: term) (then_: term) (else_: term) : term
.

Declare Custom Entry term.
Declare Custom Entry typ.

Notation "{{ x }}" := x (x custom term).
Notation "( x )" := x (in custom term, x custom term).

Notation "'λ' a : T , body" :=
  (TLam a T body) (in custom term at level 98
                      , a constr at level 0  (* avoid ":" being interpreted as type *)
                      , T custom typ at level 80
                      , body custom term
                      , right associativity).

Notation "t1 t2" :=
  (TApp t1 t2) (in custom term at level 97
                   , t1 custom term
                   , t2 custom term
                   , left associativity).

Notation "x" :=
  (TVar x) (in custom term at level 0, x constr at level 0).

Notation "x" :=
  (TyBase x) (in custom typ at level 0, x constr at level 0).

Notation "x -> y" :=
  (TyFun x y) (in custom typ at level 80,
                  x custom typ,
                  y custom typ,
                  right associativity).
Notation "( x )" := x (in custom typ, x custom typ).

Print Custom Grammar term.

(* Definition a := "a". *)
Definition b := "b".
Definition c := "c".
Definition x := "x".
Definition y := "y".
Definition z := "z".
Definition T := "T".
Definition S := "S".
Definition T1 := "T1".
Definition T2 := "T2".

Unset Printing Notations.

Definition foo := {{ λ x : (T -> T) -> T -> T, (λ y : S, (x x) (x x)) x }}.

Print foo.

Example expanded_foo :
  foo = TLam x (TyFun (TyFun (TyBase T) (TyBase T)) (TyFun (TyBase T) (TyBase T)))
             (TApp (TLam y (TyBase S) (TApp (TApp (TVar x) (TVar x)) (TApp (TVar x) (TVar x)))) (TVar x)).
Proof. reflexivity. Qed.

Set Printing Notations.
Print foo.
(* prints:
{{λ x : (T -> T) -> T -> T, (λ y : S, x x (x x)) x}}
 *)

Definition ctx := list (string * typ).

Definition type_check (Γ: ctx) (t: term) (T: typ) : bool :=
  true .
