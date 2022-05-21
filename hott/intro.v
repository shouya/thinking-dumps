Inductive paths {A} : A -> A -> Type :=
  idpath : forall x, paths x x.

Notation "x <~> y" := (paths x y) (at level 70).

Hint Resolve idpath.

Check paths_ind.

Definition ind :
  forall A
         (D : forall (x y : A), (x <~> y) -> Type),
         (forall (a : A), D a a (idpath a)) ->
         forall (x y : A) (p : (x <~> y)), D x y p.
Proof.
  intros.
  induction p.
  apply X.
Defined.

Definition inv: forall {A} {x y : A}, (x <~> y) -> (y <~> x).
Proof.
  intros.
  induction X.
  apply idpath.
Defined.

Definition inv_inv : forall {A} {x y : A} {p : x <~> y}, inv (inv p) <~> p.
Proof.
  intros.
  induction p.
  unfold inv. simpl.
  apply idpath.
Defined.

Definition concat: forall {A} {x y z : A}, (x <~> y) -> (y <~> z) -> (x <~> z) :=
  fun A x y z xy yz =>
    ind A
        (fun x y p => forall (z: A), (y <~> z) -> (x <~> z))
        (fun a =>
           ind A
               (fun a b _ => a <~> b)
               (fun w => idpath w)
               a
        )
        x y xy z yz
.

Print concat.

Notation "p @ q" := (concat p q) (at level 60).

Lemma concat_idpath : forall A {x: A}, (idpath x) @ (idpath x) = idpath x.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

(* It's very weird that concat defined in Proof mode will be
   un-expandable.  Proof. ... Qed. marks the definition
   opaque. Whereas Proof. ... Defined. marks the definition
   transparent.
  *)

Notation "! p" := (inv p) (at level 50).

Definition idpath_left_unit : forall A (x y : A) (p : x <~> y), (idpath x @ p) <~> p.
Proof.
  intros.
  induction p.
  auto.
Qed.

Definition idpath_right_unit : forall A (x y : A) (p : x <~> y), (p @ idpath y) <~> p.
Proof.
  intros.
  induction p.
  auto.
Qed.

Require Import Coq.Init.Nat.

Inductive pointed A (a : A) : Type :=
| point_intro : pointed A a.

Hint Resolve point_intro.

Definition loop A (a : A) : Type := (pointed (a <~> a) (idpath a)).

Print loop.

Definition loop_concat A (a : A) (x : loop A a) (y : loop A a) : loop A a.
Proof. trivial. Qed.

Print loop_concat.

Definition loop2 A (a : A) : Type := loop (loop A a) (point_intro _ _).
Print loop2.

(*
loop2 =
fun (A : Type) (a : A) => loop (loop A a) (point_intro (a <~> a) (idpath a))
     : forall A : Type, A -> Type
 *)
