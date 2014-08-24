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
  forall x y, R x y -> forall x', x <> x' -> ~(R x' y).

(*
Or, again, they may be defined as follows: Given two terms x and x',
the terms to which x has the given relation and those to which x' has
it have no member in common.
*)
Definition one_many' {X} (R : relation X) : Prop :=
  forall x x' y, x <> x' -> ~(R x y /\ R x' y).

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
  forall x y, relative_product R (converse R) x y <-> id x y.

(* I'll try to prove the equivalence between these three definitions *)

Theorem one_many_eqv1 :
  forall {X} (R : relation X), one_many R -> one_many' R.
Proof.
  unfold one_many. unfold one_many'.
  intros. intro.
  inversion H1; clear H1.

  apply H with (x':=x') in H2.
  apply H2 in H3.
  inversion H3. assumption.
Qed.

Theorem one_many_eqv2 :
  forall {X} (R : relation X), one_many' R -> one_many R.
Proof.
  unfold one_many. unfold one_many'.
  intros. intro.

  apply H with (y:=y) in H1.
  apply H1. split; assumption.
Qed.

Lemma id_eqv : forall {X} (x:X) (y:X), x = y <-> id x y.
Proof.
  intros. split.
  intro. rewrite H. apply id0.
  intro. inversion H. reflexivity.
Qed.


Lemma expand_one_many'' :
  forall {X} (R : relation X),
    one_many'' R <-> (forall x y, R x y -> forall x', converse R y x' -> x = x').
Proof.
  intros. unfold one_many''. split.

  intros.
  assert (relative_product R (converse R) x x' <-> id x x'). apply H.
  inversion H2. apply id_eqv. apply H3.
  apply rp0 with y. assumption. assumption.

  intros.
  split. intro.
  inversion H0. subst.
  apply id_eqv. apply H with y0.
  assumption. assumption.


  rename y into x'. intro.
  inversion H0. clear H0. subst x0.
  assert (y:X); intuition.

  (* Skip skip skip this~ too tough *)
  admit.
Admitted.


Theorem one_many_eqv3 :
  forall {X} (R : relation X), one_many R -> one_many'' R.
Proof.
  admit.
Admitted.  (* Skip *)

Theorem one_many_eqv4 :
  forall {X} (R : relation X), one_many'' R -> one_many R.
Proof.
  unfold one_many; unfold one_many''.
  intros. intro.

  assert (relative_product R (converse R) x y <-> id x y). apply H.
  inversion H3.
  admit.
Admitted. (* Skip *)

Definition many_one {X} (R : relation X) : Prop :=
  forall x y, R x y -> forall y', ~(R x y').
Definition one_one {X} (R : relation X) : Prop :=
  many_one R /\ one_many R.
