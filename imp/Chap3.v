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
