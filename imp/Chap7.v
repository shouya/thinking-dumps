
(* CHAPTER VI: RATIONAL, REAL, AND COMPLEX NUMBERS *)

Require Export Chap6.

Require Import Omega.

Inductive plus_one : relation nat :=
| plus_one0 : forall n, plus_one n (S n).
Inductive minus_one : relation nat :=
| minus_one0 : forall n, minus_one (S n) n.

Theorem plus_one_minus_one_converse :
  forall n, relative_product plus_one minus_one n n.
Proof.
  intros.
  apply rp0 with (y := S n); constructor.
Qed.

Inductive plus_m : nat -> relation nat :=
| plus_m0 : forall m n, plus_m m n (n + m).

Inductive minus_m : nat -> relation nat :=
| minus_m0 : forall m n, minus_m m (n + m) n.


Theorem plus_minus_converse :
  forall m n, relative_product (plus_m m) (minus_m m) n n.
Proof.
  intros.
  apply rp0 with (y := n + m); constructor.
Qed.


Inductive frac : nat -> nat -> relation nat :=
| frac0 : forall m n x y, x * n = y * m -> frac m n x y.


Theorem frac_inv_imp :
  forall m n, m <> 0 -> n <> 0 -> forall x y, frac m n x y -> x * n = y * m.
Proof.
  intros.
  inversion H1.
  subst.
  assumption.
Qed.

Theorem frac_0_n_same :
  forall n n' x y, n' <> 0 -> n <> 0 -> (frac 0 n x y <-> frac 0 n' x y).
Proof.
  intros.
  split; intros; inversion H1; clear H1; subst;
  apply frac0;

  rewrite mult_0_r;
  rewrite mult_0_r in H2;

  apply mult_is_O in H2;
  inversion H2; subst; try reflexivity; omega.
Qed.


Theorem frac_m_0_same :
  forall m m' x y, m' <> 0 -> m <> 0 -> (frac m 0 x y <-> frac m' 0 x y).
Proof.
  intros.
  split; intros; inversion H1; clear H1; subst;
  apply frac0;

  rewrite mult_0_r;
  rewrite mult_0_r in H2;

  symmetry in H2; symmetry;

  apply mult_is_O in H2;
  inversion H2; subst; try reflexivity; omega.
Qed.


Theorem one_many_frac :
  forall m n, m = 0 -> n <> 0 -> one_many (frac m n).
Proof.
  intros.
  unfold one_many.
  intros.
  inversion H1. inversion H2. clear H1 H2. subst.
  rewrite mult_0_r in H3.
  rewrite mult_0_r in H8.
  apply mult_is_O in H3.
  apply mult_is_O in H8.

  inversion H3; subst;
  inversion H8; subst;
  intuition.
Qed.

Theorem oneone_frac :
  forall m n, m <> 0 -> n <> 0 -> one_one (frac m n).
Proof.
  intros. constructor.
  unfold many_one.

  intros.
  inversion H1. inversion H2. clear H1 H2. subst.


  induction m. omega.
  induction n. omega.


Theorem converse_frac :
  forall m n a, relative_product (frac m n) (frac n m) a a.
Proof.
  intros.
  apply rp0 with
  apply frac0.