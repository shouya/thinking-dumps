
Require Export A007logic.

Definition even (n:nat) : Prop :=
  evenb n = true.



Inductive ev : nat -> Prop :=
  | ev0  : ev 0
  | evSS : forall n : nat, ev n -> ev (S (S n)).



Theorem double_even : forall n,
  ev (double n).
Proof.
  intro.
  induction n.
  simpl. apply ev0.
  simpl. apply evSS. exact IHn.
Qed.

Theorem xxx : forall n : nat, n = n -> n <= n.
Proof.
  intros n.
  induction n.
  reflexivity.
  intro.
  simpl.




Theorem ev_even : forall n,
                    ev n -> even n.
Proof.
  intros.
  induction H.
  simpl