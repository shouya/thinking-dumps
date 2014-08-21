Module Chap3.

Require Import Relations.



(*
Inductive nat : Set :=
  | zero : nat
  | succ : nat -> nat.
*)

Inductive succR : nat -> nat -> Prop :=
  | s1 : (forall a b : nat, S a = b -> succR a b).

Inductive immediatePredR : nat -> nat -> Prop :=
  | p0 : (forall a b, succR a b -> immediatePredR b a)
  | pi : (forall a b, forall c, immediatePredR b c -> succR a c
                                -> immediatePredR b a).

Example ex1 : immediatePredR 5 3.
Proof.
  apply pi with (c:=4).
  apply p0.
  apply s1.
  reflexivity.
  apply s1.
  reflexivity.
Qed.

(* Peano's Axioms *)

Theorem thm3 : forall a b, S a = S b -> a = b.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Theorem thm4 : forall a, ~(S a = 0).
Proof.
  intros. intro.
  inversion H.
Qed.

Theorem thm5 : forall (p : nat -> Prop), p 0
                                         -> (forall n, p n -> p (S n))
                                         -> (forall n, p n).
Proof.
  intros.
  induction n.
  (* n = 0 *)
  assumption.
  (* n = S n *)
  apply H0.
  assumption.
Qed.
(* Prooving inductivity with inductive assumption is actually meaningless.
   So they're just demonstrations *)


(* page 25:
A property is called “R-hereditary” when, if it belongs to a term x, and x
has the relation R to y, then it belongs to y.
*)
Definition r_hereditary {X} (R : relation X) (p : X -> Prop) : Prop :=
  forall x y, p x -> R x y -> p y.

(*
A term x is said to be an “R-ancestor” of the term y if y has every
R-hereditary property that x has, provided x is a term which has the
relation R to something or to which something has the relation R.
(This is only to exclude trivial cases.)
*)

Definition r_ancestor {X} (R : relation X) (x : X) (y : X) :=
  forall (p : X -> Prop), r_hereditary R p -> p x -> p y.

(* My own understandings *)
Example __ex1 : r_hereditary lt (fun x => x > 0).
Proof.
  unfold r_hereditary.
  unfold lt.
  intros.
  induction H0.
  induction H. constructor. constructor.
  constructor. apply IHle.
  constructor. apply IHle.
Qed.

Example __ex2 : r_ancestor lt 3 5.
Proof.
  unfold r_ancestor.
  unfold r_hereditary.
  intros.
  apply H with 3.
  assumption. auto.
Qed.


(* page 26:
The “R-posterity” of x is all the terms of which x is an R-ancestor.
*)

Definition r_posterity {X} (R : relation X) (x : X) (y : X) := r_ancestor R y x.
