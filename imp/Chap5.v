Module Chap5.

Require Import Relations.

Load "Chap4.v".


Definition symmetric {X} (R : relation X) :=
  forall x y, R x y -> R y x.


Theorem asym_imp_alio :
  forall {X} (R : relation X), asymmetrical R -> aliorelative R.
Proof.
  unfold asymmetrical. unfold aliorelative.
  intros. intro.
  remember H0. clear Heqr.
  generalize r.
  apply H. assumption.
Qed.





Definition many_many {X} (R : relation X) : Prop := True. (* tautology *)

(* page 47:
One-many relations may be defined as relations such that, if x has the
relation in question to y, there is no other term x' which also has the
relation to y.
*)
Definition one_many {X} (R : relation X) : Prop :=
  forall x y, R x y -> forall x', R x' y -> x = x'.

(*
Or, again, they may be defined as follows: Given two terms x and x',
the terms to which x has the given relation and those to which x' has
it have no member in common.
*)
Definition one_many' {X} (R : relation X) : Prop :=
  forall x x' y, R x y /\ R x' y -> x = x'.

(* Or, again, they may be defined as relations such that the relative *)
(*product of one of them and its converse implies identity, where the *)
(*“relative product” of two relations R and S is that relation which *)
(*holds between x and z when there is an intermediate term y, such *)
(*that x has the relation R to y and y has the relation S to z. *)

Inductive relative_product
          {X} (R: relation X) (S: relation X) : relation X :=
  | rp0 : forall x y, forall z, R x y -> S y z -> relative_product R S x z.

Inductive converse {X} (R : relation X) : relation X :=
  | cv0 : forall x y, R x y -> converse R y x.
Inductive id {X} : relation X :=
  | id0 : forall x, id x x.

Definition one_many'' {X} (R : relation X) : Prop :=
  forall x y, relative_product R (converse R) x y -> id x y.

(* I'll try to prove the equivalence between these three definitions *)

Theorem one_many_eqv1 :
  forall {X} (R : relation X), one_many R -> one_many' R.
Proof.
  unfold one_many. unfold one_many'.
  intros. inversion H0.
  apply H with y; assumption.
Qed.

Theorem one_many_eqv2 :
  forall {X} (R : relation X), one_many' R -> one_many R.
Proof.
  unfold one_many. unfold one_many'.
  intros.

  apply H with y. split; assumption.
Qed.

Lemma id_eqv : forall {X} (x:X) (y:X), x = y <-> id x y.
Proof.
  intros. split.
  intro. rewrite H. apply id0.
  intro. inversion H. reflexivity.
Qed.

(* I asked a question about this on stackoverflow:
   http://stackoverflow.com/q/25477855/1232832
*)

Definition my_one_many'' {X} (R : relation X) :=
  forall x y, R x y -> forall x', converse R y x' -> x = x'.


Lemma expand_one_many'' :
  forall {X} (R : relation X),
    one_many'' R <-> my_one_many'' R.
Proof.
  intros. unfold one_many''. unfold my_one_many''. split.

  intros.
  assert (relative_product R (converse R) x x' -> id x x'). apply H.

  apply id_eqv. apply H2.
  apply rp0 with y. assumption. assumption.

  intros.
  inversion H0. subst.
  apply id_eqv. apply H with y0.
  assumption. assumption.
Qed.


Theorem one_many_eqv3 :
  forall {X} (R : relation X), one_many R -> my_one_many'' R.
Proof.
  unfold my_one_many''. unfold one_many.
  intros.
  inversion H1. subst. clear H1.
  apply H with y; assumption.
Qed.


Theorem one_many_eqv4 :
  forall {X} (R : relation X), my_one_many'' R -> one_many R.
Proof.
  unfold one_many; unfold my_one_many''.
  intros.
  apply H with y. assumption.
  apply cv0. assumption.
Qed.

Definition many_one {X} (R : relation X) : Prop :=
  forall x y, R x y -> forall y', ~(R x y').
Definition one_one {X} (R : relation X) : Prop :=
  many_one R /\ one_many R.


Definition domain {X} (R : relation X) := {x | forall y, R x y }.
Definition converse_domain {X} (R : relation X) := {y | forall x, R x y }.
