
(* power set *)
Definition Pow T := T -> Prop.


Definition Subset {T} (s1 s2: Pow T) : Prop := forall t, s1 t -> s2 t.
Notation "s1 <: s2" := (Subset s1 s2)
                         (at level 30, no associativity).

Hint Unfold Subset.

Theorem subset_refl : forall T (s: Pow T), s <: s.
Proof.
  intros. unfold Subset. auto.
Qed.

Hint Resolve subset_refl.

Theorem subset_trans : forall T (a b c: Pow T), a <: b -> b <: c -> a <: c.
Proof.
  eauto.
Qed.

Hint Resolve subset_trans.

Definition Gen T := Pow T -> Pow T.
Hint Unfold Gen.

Definition monotone {T} (f: Gen T) : Prop := forall t1 t2, t1 <: t2 -> f t1 <: f t2.
Hint Unfold monotone.

Definition f_closed {T} (f: Gen T) (x: Pow T) := f x <: x.
Definition f_consistent {T} (f: Gen T) (x: Pow T) := x <: f x.
(* or [forall t, x t = f x t] because of prop_ext axiom. *)
Definition f_fixpoint {T} (f: Gen T) (x: Pow T) := forall t, x t <-> f x t.

Hint Unfold f_closed.
Hint Unfold f_consistent.
Hint Unfold f_fixpoint.

Require Import Coq.Logic.FunctionalExtensionality.

(* let's give it a try *)
Theorem closed_consistent_implies_fixpoint : forall T (f: Gen T) (x: Pow T),
    f_closed f x /\ f_consistent f x -> f_fixpoint f x.
Proof.
  intros.
  destruct H. unfold f_closed in *. unfold f_consistent in *. unfold f_fixpoint.
  unfold Subset in *.
  intros.
  pose proof H t.
  pose proof H0 t.
  split; auto.
Qed.

Hint Resolve closed_consistent_implies_fixpoint.

Theorem fixpoint_implies_closed_consistent : forall T (f: Gen T) (x: Pow T),
    f_fixpoint f x -> f_closed f x /\ f_consistent f x.
Proof.
  intros.
  unfold f_closed in *. unfold f_consistent in *. unfold f_fixpoint in *.
  split; unfold Subset.
  - intros. apply H. auto.
  - intros. apply H. auto.
Qed.

Hint Resolve fixpoint_implies_closed_consistent.

Lemma f_consistent_recursive : forall T (f: Gen T) (x: Pow T),
    monotone f -> f_consistent f x -> f_consistent f (f x).
Proof.
  unfold f_consistent.
  intros.
  intro.
  intro.
  eapply H with x.
  apply H0. apply H1.
Qed.

Definition Intersect {T} (p: Pow T -> Prop) : Pow T :=
  (fun t => forall x, p x -> x t).

Definition Union {T} (p: Pow T -> Prop) : Pow T :=
  (fun t => exists x, p x /\ x t).

Hint Unfold Intersect. Hint Unfold Union.

Lemma Intersect_Subset : forall T {p: Pow T -> Prop} x, p x -> Intersect p <: x.
Proof.
  intros.
  unfold Intersect, Subset.
  intros.
  apply H0.
  apply H.
Qed.

Lemma Union_Subset : forall T {p: Pow T -> Prop} x, p x -> x <: Union p.
Proof. eauto. Qed.

Lemma Intersect_f_closed : forall T (f: Gen T),
    monotone f -> f_closed f (Intersect (f_closed f)).
Proof.
  intros.
  repeat intro.
  apply H1. eapply H.
  apply Intersect_Subset.
  apply H1. apply H0. Qed.

Lemma Union_f_consistent : forall T (f: Gen T),
    monotone f -> f_consistent f (Union (f_consistent f)).
Proof.
  intros.
  intro. intro.
  unfold Union in *. destruct H0. destruct H0.
  apply H with x. apply Union_Subset.
  apply H0. unfold f_consistent in H0. unfold Subset in H0.
  auto.
Qed.

Lemma knaster_tarski_1_fixpoint : forall T (f: Gen T),
    monotone f -> f_consistent f (Intersect (f_closed f)).
Proof.
  intros T f Hmono.
  unfold f_consistent.
  repeat intro.
  apply H.
  apply Hmono.
  clear H.
  repeat intro.
  apply H0.
  eapply Hmono.
  apply Intersect_Subset.
  apply H0. apply H.
Qed.

Lemma knaster_tarski_2_fixpoint : forall T (f: Gen T),
    monotone f -> f_closed f (Union (f_consistent f)).
Proof.
  intros T f Hmono.
  unfold f_closed.
  repeat intro.
  exists (f (Union (f_consistent f))).
  split.
  - repeat intro.
    apply f_consistent_recursive; auto.
    apply Union_f_consistent. auto.
  - apply H.
Qed.

Definition IsMin {T} (p: Pow T -> Prop) (x: Pow T) : Prop :=
  p x /\ forall x', p x' -> x <: x'.
Definition IsMax {T} (p: Pow T -> Prop) (x: Pow T) : Prop :=
  p x /\ forall x', p x' -> x' <: x.


Lemma knaster_tarski_1 : forall T (f: Gen T),
    monotone f -> IsMin (f_fixpoint f) (Intersect (f_closed f)).
Proof.
  intros.
  unfold IsMin.
  split.
  - apply closed_consistent_implies_fixpoint. split.
    + apply Intersect_f_closed; easy.
    + apply knaster_tarski_1_fixpoint; easy.
  - intros.
    apply Intersect_Subset.
    apply fixpoint_implies_closed_consistent in H0. easy.
Qed.

Lemma knaster_tarski_2 : forall T (f: Gen T),
    monotone f -> IsMax (f_fixpoint f) (Union (f_consistent f)).
Proof.
  intros.
  unfold IsMax.
  split.
  - apply closed_consistent_implies_fixpoint. split.
    + apply knaster_tarski_2_fixpoint; easy.
    + apply Union_f_consistent; easy.
  - intros.
    apply Union_Subset.
    apply fixpoint_implies_closed_consistent in H0. easy.
Qed.

Theorem knaster_tarski: forall T (f: Gen T),
    monotone f ->
    IsMin (f_fixpoint f) (Intersect (f_closed f)) /\
    IsMax (f_fixpoint f) (Union (f_consistent f)).
Proof.
  auto using knaster_tarski_1, knaster_tarski_2.
Qed.

Lemma min_unique : forall T (p: Pow T -> Prop) (x1 x2: Pow T),
    IsMin p x1 -> IsMin p x2 -> forall t, x1 t <-> x2 t.
Proof.
  unfold IsMin.
  unfold Subset.
  intros. destruct H; destruct H0.
  split; intro.
  - apply H1; eauto.
  - apply H2; eauto.
Qed.

Lemma max_unique : forall T (p: Pow T -> Prop) (x1 x2: Pow T),
    IsMax p x1 -> IsMax p x2 -> forall t, x1 t <-> x2 t.
Proof.
  unfold IsMax.
  unfold Subset.
  intros. destruct H; destruct H0.
  split; intro.
  - apply H2 with x1; eauto.
  - apply H1 with x2; eauto.
Qed.

Definition MinFix {T} (f: Gen T) := (Intersect (f_closed f)).
Definition MaxFix {T} (f: Gen T) := (Union (f_consistent f)).
