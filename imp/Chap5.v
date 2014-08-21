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
