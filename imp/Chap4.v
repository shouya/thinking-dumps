Module Chap4.

Require Import Relations.
(* Require Import Coq.Setoids.Setoid. (* for the use of rewrite *) *)

(* Ordered Series *)


Definition asymmetrical {X : Type} (R : relation X) : Prop :=
  forall x y, R x y -> ~(R y x).

Definition transitive {X: Type} (R: relation X) : Prop :=
  forall x y z, R x y -> R y z -> R x z.

Definition connected {X: Type} (R: relation X) : Prop :=
  forall x y, x <> y -> (R x y) /\ (R y x).

Definition aliorelative {X: Type} (R: relation X) : Prop :=
  forall x, ~(R x x).

Inductive square {X: Type} (R: relation X) : relation X :=
  | sq0 : forall x y z, R x y -> R y z -> square R x z.

Inductive diversity {X} : relation X :=
  | dv0 : forall x y, x <> y -> diversity x y.




(* page 33:
It will be seen that an asymmetrical relation is the same thing as
a relation whose square is an aliorelative. It often happens that a
relation is an aliorelative without being asymmetrical, though an
asymmetrical relation is always an aliorelative. For example, “spouse”
is an aliorelative, but is symmetrical, since if x is the spouse of y, y is
the spouse of x. But among transitive relations, all aliorelatives are
asymmetrical as well as vice versa.
 *)
Theorem asy_implies_aliosq :
  forall {X: Type} (R: relation X), asymmetrical R -> aliorelative (square R).
Proof.
  intros.
  unfold aliorelative.
  intros.
  unfold asymmetrical in H.
  intro.
  inversion H0.
  subst.
  apply H in H1.
  apply H1 in H2.
  inversion H2.
Qed.

Theorem aliosq_implies_asy :
  forall {X: Type} (R: relation X), aliorelative (square R) -> asymmetrical R.
Proof.
  intros.
  unfold aliorelative in H.
  unfold asymmetrical.
  intros.
  intro.
  assert (H': square R x x).
  apply sq0 with y; assumption.
  apply H in H'.
  inversion H'.
Qed.

Theorem asy_eqv_aliosq :
  forall {X: Type} (R: relation X), aliorelative (square R) <-> asymmetrical R.
Proof.
  intros.
  split.
  apply aliosq_implies_asy.
  apply asy_implies_aliosq.
Qed.

(* One relation is said to contain or be implied by another if it
holds whenever the other holds.
*)

Definition contains {X} (R Q: relation X) :=
  forall x y, R x y -> Q x y.


(*
From the definitions it will be seen that a transitive relation is one
which is implied by its square, or, as we also say, “contains” its square.
*)

(*
Theorem sqself_imp_trans :
  forall {X: Type} (R: relation X), (R = square R) -> transitive R.
Proof.
  intros.
  unfold transitive.
  intros.
  rewrite H.
  apply sq0 with y; assumption.
Qed.
*)

(* Rectified theorem, this is exactly what the statement is talking *)
Theorem sqself_imp_trans :
  forall {X} (R: relation X), (contains (square R) R) -> transitive R.
Proof.
  intros.
  unfold transitive.
  intros.
  apply H.
  apply sq0 with y; assumption.
Qed.


Theorem trans_imp_sqself :
  forall {X} (R: relation X), transitive R -> (contains (square R) R).
Proof.
  unfold contains.
  intros.
  induction H0.
  unfold transitive in H.
  apply H with y; assumption.
Qed.


(*
A transitive aliorelative is one which contains its square
and is contained in diversity; or, what comes to the same thing, one
whose square implies both it and diversity
*)

Lemma diversity_eqv_aliorelative :
  forall {X} (R: relation X), (contains R diversity) <-> aliorelative R.
Proof.
  intros.
  unfold aliorelative.
  unfold contains.
  split.

  intros. intro.
  apply H in H0.
  inversion H0.
  apply H1. reflexivity.

  intros. intuition.
  apply dv0. intro.
  apply H with y.
  rewrite H1 in H0.
  assumption.
Qed.

Definition transitive_aliorelative {X} (R : relation X) : Prop :=
  contains R (square R) /\ contains R diversity.

Definition transitive_aliorelative' {X} (R : relation X) : Prop :=
  contains (square R) R /\ contains (square R) diversity.

(* continued from above.
—because, when a relation is transitive, asymmetry is equivalent
to being an aliorelative.
*)

Theorem trans_imp_asym_eqv_alio :
  forall {X} (R : relation X), transitive R -> (asymmetrical R <-> aliorelative R).
Proof.
  unfold transitive.
  unfold asymmetrical.
  unfold aliorelative.
  intros.
  split.

  intros. intro.
  apply H0 with x x; assumption.

  intros. intro.
  apply H0 with x.
  apply H with y; assumption.
Qed.
