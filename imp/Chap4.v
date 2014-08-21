Module Chap4.

Require Import Relations.

(* Ordered Series *)

Load "Chap3.v".


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

(* A relation is connected when, given any two different terms of its field,
the relation holds between the first and the second or between the second and
the first (not excluding the possibility that both may happen, though both
cannot happen if the relation is asymmetrical).
*)

(* Defined in the beginning as definition of 'connected' *)


(* A relation is serial when it is an aliorelative, transitive,
and connected; or, what is equivalent, when it is asymmetrical,
transitive, and connected.
*)

Definition serial {X} (R : relation X) : Prop :=
  aliorelative R /\ transitive R /\ connected R.
Definition serial' {X} (R : relation X) : Prop :=
  asymmetrical R /\ transitive R /\ connected R.


(*Definition proper_posterity {X} (R : relation X) *)

(* page 36:
The “proper posterity” of x with respect to R consists of
all terms that possess every R-hereditary property possessed by
every term to which x has the relation R.
*)

(* method 1: defining Type
Definition proper_posterity {X} (R : relation X) (x : X) :=
  { y | forall (p : X -> Prop), r_hereditary R p -> R y x }.
*)
(* method 2: defining Prop *)

Definition proper_posterity {X} (R : relation X) (x : X) : X -> Prop :=
  fun y => forall p, r_hereditary R p -> (forall t, R x t -> p t) -> p y.

(*
Definition proper_posterity {X} (R : relation X) (x : X) (y : X) : Prop :=
  r_posterity R y x /\ R y x.
*)

(* A term x is a “proper ancestor” of y with respect to R if y
belongs to the proper posterity of x with respect to R.
*)

Definition proper_ancestor {X} (R : relation X) (x : X) (y : X) : Prop :=
  proper_posterity R y x.


(* It will always be transitive: no matter what sort of relation
   R may be, “R-ancestor” and “proper R-ancestor” are always both transitive.
*)

Theorem r_anc_trans {X} :
  forall R : relation X, transitive (r_ancestor R).
Proof.
  intros.
  unfold transitive. unfold r_ancestor.
  intros.
  apply H0. exact H1.
  apply H. exact H1.
  assumption.
Qed.

Theorem prop_anc_trans {X} :
  forall R : relation X, transitive (proper_ancestor R).
Proof.
  intros.
  unfold transitive. unfold proper_ancestor. unfold proper_posterity.
  intros.

  apply H.
  exact H1.
  intros.
  unfold r_hereditary in H1.
  apply H1 with y.

  apply H0.
  exact H1.
  intros. apply H2. assumption.

  assumption.
Qed.
