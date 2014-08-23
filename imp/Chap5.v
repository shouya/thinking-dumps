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
  forall x y, R x y -> forall x', ~(R x' y).

(*
Or, again, they may be defined as follows: Given two terms x and x',
the terms to which x has the given relation and those to which x' has
it have no member in common.
*)
Definition one_many' {X} (R : relation X) : Prop :=
  forall x x' y, ~(R x y /\ R x' y).

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
  forall x, relative_product R (converse R) x x.

(* I'll try to prove the equivalence between these three definitions *)

Theorem one_many_eqv1 :
  forall {X} (R : relation X), one_many R -> one_many' R.
Proof.
  unfold one_many. unfold one_many'.
  intros. intro.
  inversion H0; clear H0.

  apply H with (x':=x') in H1.
  apply H1; assumption.
Qed.

Lemma and_reproduce :
  forall a : Prop, a -> a /\ a.
Proof.
  intros. split; assumption.
Qed.

Theorem one_many_eqv2 :
  forall {X} (R : relation X), one_many' R -> one_many'' R.
Proof.
  unfold one_many'; unfold one_many''.
  intros.


  assert (forall x x' y : X, ~ (S y x /\ R y x')).
  apply S.

  induction H0.
  induction H1.
  assert (R x y /\ R x0 y). split; assumption.
  apply H in H2. inversion H2.

  intro. induction H0.
  assert (Hid : forall x, ~(R x x /\ R x x)); intros. apply H.
  assert (Hid' : forall x, ~(R x x)); intros.
  intro.
  apply and_reproduce in H0.
  apply Hid in H0. assumption.

  apply rp0 with x.

Admitted.  (* TODO: finish this proof *)

Theorem one_many_eqv3 :
  forall {X} (R : relation X), one_many'' R -> one_many R.
Proof.
  unfold one_many; unfold one_many''.
  intros.

  assert (relative_product R (converse R) x y <-> id x y). apply H.
  inversion H1.
  intro.


Definition many_one {X} (R : relation X) : Prop :=
  forall x y, R x y -> forall y', ~(R x y').
Definition one_one {X} (R : relation X) : Prop :=
  many_one R /\ one_many R.
