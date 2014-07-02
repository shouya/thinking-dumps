(* Chapter: Logic *)

Require Export "A006morecoq".

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).
Notation "P /\ Q" := (and P Q) : type_scope.


Theorem proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros.
  inversion H.
  assumption.
Qed.

Theorem proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros. inversion H. assumption. Qed.


Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros.
  inversion H.
  split.
  assumption. assumption.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split.
    split. assumption. assumption.
    assumption.
Qed.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

Theorem iff_implies : forall P Q : Prop,
  (P <-> Q) -> P -> Q.
Proof.
  intros P Q H.
  inversion H as [HAB HBA]. apply HAB. Qed.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB. Qed.


Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros.
  split; intro.
  assumption. assumption.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R H1 H2.
  inversion H1.
  inversion H2.
  split; intro.
  apply H3. apply H. assumption.
  apply H0. apply H4. assumption.
Qed.


Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.


Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros.
  inversion H.
  apply or_intror. assumption.
  apply or_introl. assumption.
Qed.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros.
  split.
  Case "P \/ (Q /\ R) -> (P \/ Q)".
    inversion H.
    SCase "P -> (P \/ Q)".
      left. assumption.
    SCase "(Q /\ R) -> (P \/ Q)".
      inversion H0.
      right. assumption.
  Case "P \/ (Q /\ R) -> (P \/ R)".
    inversion H.
    SCase "P -> P \/ R".
      left. assumption.
    SCase "(Q /\ R) -> (P \/ R)".
      inversion H0. right. assumption.
Qed.


Theorem or_distributes_over_and_1' : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros.
  inversion H.
  split. left. assumption.
  left. assumption.
  inversion H0.
  split. right. assumption.
  right. assumption.
Qed.



Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros.
  inversion H.
  inversion H0.
  Case "P -> P \/ Q /\ R".
    left. assumption.
  Case "Q -> P \/ Q /\ R".
    inversion H1.
    left. assumption.
    right. split. assumption. assumption.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros.
  split.
  apply or_distributes_over_and_1.
  apply or_distributes_over_and_2.
Qed.


Theorem andb_prop : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros.
  split.
  destruct b, c. reflexivity. reflexivity. inversion H. inversion H.
  destruct b, c. reflexivity. inversion H. inversion H. inversion H.
Qed.

Theorem andb_true_intro : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  intros.
  inversion H.
  rewrite H0. rewrite H1. reflexivity.
Qed.

Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof.
  intros.
  destruct b, c.
  inversion H.
  right. reflexivity.
  left. reflexivity.
  left. reflexivity.
Qed.


Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros.
  destruct b,c.
  left. reflexivity.
  left. reflexivity.
  right. reflexivity.
  inversion H.
Qed.


Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof.
  intros.
  destruct b, c.
  inversion H. inversion H. inversion H.
  split. reflexivity. reflexivity.
Qed.

Inductive False : Prop :=.

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof.
  intros.
  inversion H.
Qed.

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros.
  inversion H.
Qed.


Inductive True : Prop := I : True.
Definition not (A:Prop) := A -> False.

Notation "~ x" := (not x) : type_scope.


Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  inversion contra. Qed.


Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros.
  inversion H.
  unfold not in H1.
  apply H1 in H0. inversion H0.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros.
  unfold not. intro.
  apply H0 in H.
  inversion H.
Qed.

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros.
  unfold not in H0.
  unfold not.
  intro.
  apply H in H1. apply H0 in H1. assumption.
Qed.


Theorem not_both_true_and_false : forall P : Prop,
  ~(P /\ ~P).
Proof.
  intros.
  unfold not. intros. inversion H. apply H1 in H0. assumption.
Qed.


Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  intros.
  unfold not in H.
Abort.


Definition peirce := forall P Q: Prop,
                       ((P->Q)->P)->P.
Definition classic := forall P:Prop,
  ~~P -> P.
Definition excluded_middle := forall P:Prop,
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).


Theorem peirce_classic : peirce -> classic.
Proof.
  unfold peirce. unfold classic.
  intros peirce P.
  assert (((P -> False) -> P) -> P).
  apply peirce.
  unfold not. intros. apply H. intro. apply H0 in H1. inversion H1.
Qed.

Theorem classic_excluded_middle : classic -> excluded_middle.
Proof.
  unfold classic. unfold excluded_middle.
  intros classic P.
  unfold not in classic.
  unfold not.
  apply classic. intro. apply H.
  left. apply classic. intro. apply H. right. assumption.
Qed.


Theorem excluded_middle_de_morgan_not_and_not:
  excluded_middle -> de_morgan_not_and_not.
Proof.
  unfold excluded_middle. unfold de_morgan_not_and_not.
  intros.
  assert (P \/ ~P). apply H.
  assert (Q \/ ~Q). apply H.
  inversion H1. left. assumption.
  inversion H2. right. assumption.
  unfold not in H0, H3, H4.
  apply ex_falso_quodlibet. apply H0. split; assumption.
Qed.

Theorem de_morgan_not_and_not_implies_to_or:
  de_morgan_not_and_not -> implies_to_or.
Proof.
  unfold de_morgan_not_and_not. unfold implies_to_or.
  intros.
  assert (~(~~P /\ ~Q)-> ~P \/ Q).
  apply H.
  apply H1.
  intro. inversion H2. apply H3. intro. apply H0 in H5.
  apply H4 in H5. inversion H5.
Qed.

Theorem implies_to_or_peirce : implies_to_or -> peirce.
Proof.
  unfold implies_to_or. unfold peirce.
  intros.
  apply H0.
  intro.
  assert (~(~P \/ Q) \/ P).
  apply H. intro. assumption.
  inversion H2.
(* TODO: no idea *)
admit. admit.
Qed.

Theorem excluded_middle_irrefutable: forall (P:Prop), ~~(P \/ ~P).
Proof.
  intros.
  intro.
  apply H.
  right. intro.
  apply H.
  left.
  assumption.
Qed.

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros.
  destruct b. reflexivity.
  unfold not in H.
  apply ex_falso_quodlibet.
  apply H.
  reflexivity.
Qed.
