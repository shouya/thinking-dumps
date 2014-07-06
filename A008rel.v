

Require Export A007logic.

Definition relation (X: Type) := X->X->Prop.


Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.


Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold partial_function.
  intro.
  assert (0 = 1) as nonsense.
  apply H with (x:=0).
  reflexivity.
  apply le_S. reflexivity.
  inversion nonsense.
Qed.


Inductive total_relation : nat -> nat -> Prop :=
  tot : forall n m : nat, total_relation n m.


Theorem total_relation_not_a_partial_function :
  ~ (partial_function total_relation).
Proof.
  unfold partial_function.
  intro.
  assert (0 = 1).
  apply H with (x := 0).
  apply tot.
  apply tot.
  inversion H0.
Qed.


Inductive empty_relation : nat -> nat -> Prop :=.

Theorem empty_relation_is_a_partial_function :
  partial_function empty_relation.
Proof.
  unfold partial_function.
  intros.
  inversion H.
Qed.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive.
  intro.
  apply le_n.
Qed.


Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).



Theorem le_trans :
  transitive le.
Proof.
  unfold transitive.
  intros.
  induction H0.
  assumption.
  apply le_S. assumption.
Qed.

Theorem lt_le :
  forall a b : nat, a < b -> a < S b.
Proof.
  intros.
  apply le_S in H.
  induction H.
  apply le_S.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt.
  unfold transitive.
  intros.
  apply le_S in H.
  apply le_trans with (a := (S a)) (b := (S b)) (c := c).
  assumption.
  assumption.
Qed.


Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that m is less than o. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo.
  apply le_S in Hnm. assumption.
  apply le_S in IHHm'o. assumption.
Qed.

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
