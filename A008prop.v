
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


Theorem ev__even : forall n,
                    ev n -> even n.
Proof.
  intros.
  induction H.
  simpl.
  reflexivity.
  unfold even in IHev. unfold even. simpl. assumption.
Qed.

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof.
  intros.
  induction H.
  simpl. assumption.
  simpl. apply evSS. assumption.
Qed.

Inductive beautiful : nat -> Prop :=
| b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum : forall m n : nat,
            beautiful m -> beautiful n ->
            beautiful (m + n).

Theorem beautiful_8 : beautiful 8.
Proof.
  replace (8) with (3 + 5).
  apply b_sum.
  apply b_3.
  apply b_5.
  reflexivity.
Qed.

Theorem beautiful_8' : beautiful 8.
Proof.
  replace (8) with ((5 + 3) + 0).
  apply b_sum.
  apply b_sum.
  apply b_5.
  apply b_3.
  apply b_0.
  reflexivity.
Qed.

Theorem beautiful_plus_eight:
  forall n, beautiful n -> beautiful (8+n).
Proof.
  intros.
  apply b_sum.
  apply beautiful_8.
  assumption.
Qed.

Theorem b_times2:
  forall n, beautiful n -> beautiful (2 * n).
Proof.
  simpl.
  intros.
  rewrite plus_assoc.
  apply b_sum.
  apply b_sum.
  assumption. assumption.
  apply b_0.
Qed.

Theorem b_timesm:
  forall n m, beautiful n -> beautiful (m * n).
Proof.
  intros.
  induction m.
  simpl. apply b_0.
  simpl. apply b_sum.
  assumption.
  assumption.
Qed.

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

Theorem gorgeous_plus13: forall n,
                           gorgeous n -> gorgeous (13+n).
Proof.
  intros.
  replace 13 with (3 + 5 + 5).
  replace (3 + 5 + 5 + n) with (3 + (5 + (5 + n))).
  apply g_plus3. apply g_plus5. apply g_plus5.
  assumption.
  reflexivity.
  reflexivity.
Qed.


Theorem gorgeous__beautiful : forall n,
                                gorgeous n -> beautiful n.
Proof.
  intros.
  induction H.
  Case "0".
  apply b_0.
  Case "3 + n".
  apply b_sum. apply b_3. assumption.
  Case "5 + n".
  apply b_sum. apply b_5. assumption.
Qed.


Theorem gorgeous_sum : forall n m,
                         gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros.
  induction H.
  Case "0". simpl. assumption.
  Case "3+n". rewrite <- plus_assoc. apply g_plus3. assumption.
  Case "5+n". rewrite <- plus_assoc. apply g_plus5. assumption.
Qed.

Theorem beautiful__gorgeous :
  forall n, beautiful n -> gorgeous n.
Proof.
  intros.
  induction H.
  SCase "0". apply g_0.
  SCase "3". apply g_plus3 with (n:=0). apply g_0.
  SCase "5". apply g_plus5. apply g_0.
  SCase "m + n". apply gorgeous_sum; assumption.
Qed.

Lemma helper_g_times2 :
  forall x y z, x + (z + y)= z + x + y.
Proof.
  intros.
  rewrite plus_assoc.
  replace (x + z) with (z + x). reflexivity.
  rewrite plus_comm. reflexivity.
Qed.

Theorem g_times2:
  forall n, gorgeous n -> gorgeous (2 * n).
Proof.
   intros n H. simpl.
   induction H.

   Case "0".
   simpl. apply g_0.

   Case "3 + n".
   rewrite <- helper_g_times2.
   apply gorgeous_sum. assumption.
   apply g_plus3. rewrite <- plus_assoc. apply g_plus3.
   rewrite plus_comm. simpl. assumption.

   Case "5 + n".
   rewrite <- helper_g_times2.
   apply gorgeous_sum. assumption.
   apply g_plus5. rewrite <- plus_assoc. apply g_plus5.
   rewrite plus_comm. simpl. assumption.
Qed.



   (* FILL IN HERE *) Admitted.


n



(*
  induction H.
  Case "0".
    apply g_0.
  Case "3".
    apply g_plus3. apply g_0.
  Case "5".
    apply g_plus5. apply g_0.
  Case "m + n".
    apply gorgeous_sum.
*)