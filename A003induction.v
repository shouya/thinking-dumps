Require String.
Require Export A001bool.
Require Export A002nat.

Open Scope string_scope.


(* definition of Case tacit *)

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.


Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c.
  intro H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H.
    reflexivity.
Qed.

Lemma andb_fail2 : forall b : bool,
  andb b false = false.
Proof.
  destruct b; simpl; reflexivity.
Qed.


(*
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  Case "c = true".
    reflexivity.
  Case "c = false".
    (* TODO *)
Abort.


Theorem plus_0_r_firsttry : forall n : nat,
  n + 0 = n.
Proof.
  intro n.
  destruct n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n".
    simpl.
Abort.
*)

Theorem plus_0_r : forall n : nat,
  n + 0 = n.
Proof.
  intro n.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite IHn'.
    reflexivity.
Qed.

Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  intro n.
  induction n as [|n'].
  reflexivity.
  simpl.
  rewrite IHn'.
  reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n.
  Case "n = 0".
    reflexivity.
  Case "n = S n".
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n.
  Case "n = 0".
    simpl.
    rewrite plus_0_r.
    reflexivity.
  Case "n = S n".
    simpl.
    rewrite IHn.
    rewrite plus_n_Sm.
    reflexivity.
Qed.


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n.
  Case "n = 0".
    reflexivity.
  Case "n = S n".
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | 0 => 0
  | S n' => S (S (double n'))
  end.


Lemma double_plus : forall n : nat,
  double n = n + n.
Proof.
  intro n.
  induction n.
  Case "n = 0".
    reflexivity.
  Case "n = S n".
    simpl.
    rewrite IHn.
    rewrite plus_n_Sm.
    reflexivity.
Qed.



(*
Exercise: 1 star (destruct_induction)
Briefly explain the difference between
the tactics *destruct* and *induction*.

Answer:
both *destruct* and *induction* separate
the argument into two cases.

while induction provide an addition assumption
while dealing with the (S n) case. so we can
use that assumption to carry out our proof.
this is methodology we take when we do
mathematical induction, simpl., rewrite
accordingly, and finally simply/reflexivity.

*)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
    Case "Proof of assertion".
    reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "proof of assertion".
    rewrite plus_comm.
    reflexivity.
  rewrite H.
  reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite plus_assoc.
  assert (H: n + m = m + n).
    Case "proof of assertion".
    rewrite plus_comm. reflexivity.
  rewrite H.
  rewrite plus_assoc.
  reflexivity.
Qed.

(*
Lemma plus_uniq_r : forall n k k' : nat,
  n + k = n + k' -> k = k'.
Proof.
  intros n k k'.
  induction n as [|n'].
  Case "n' = 0".
    rewrite plus_comm. simpl.
    rewrite plus_comm. simpl.
    intro.
    rewrite H.
    reflexivity.
  Case "n = S n".
    simpl.
    assert (H: forall a a', S a = S a' -> a = a').
      SCase "proof of assertion".
      intros a a'.
      destruct a'.
    intro.
Abort.
*)

Theorem mult_n_Sm : forall n m : nat,
  n * S m = n * m + n.
Proof.
  intros n m.
  induction n as [|n'].
  Case "n' = 0".
    simpl. reflexivity.
  Case "n' = S n'".
    simpl. rewrite IHn'. rewrite plus_assoc. rewrite plus_n_Sm.
    reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  intros n m.
  induction n as [|n'].
  Case "n = 0".
    simpl.
    rewrite mult_0_r.
    reflexivity.
  Case "n = S n".
    simpl.
    rewrite mult_n_Sm.
    rewrite IHn'.
    rewrite plus_comm.
    reflexivity.
Qed.

Lemma negb_negb_b : forall b : bool,
                      (negb (negb b)) = b.
Proof.
  intro b. destruct b; reflexivity.
Qed.

Lemma even_SSn_eq_even_n : forall n : nat,
                             (evenb (S (S n))) = (evenb n).
Proof. reflexivity. Qed.

Lemma evenb_n : forall n : nat,
                  evenb (S n) = negb (evenb n).
Proof.
  intro.
  induction n.
  Case "n = 0".
    reflexivity.
  Case "n = S n".
    assert (H0: evenb (S (S n)) = evenb n). reflexivity.
    rewrite H0.
    rewrite IHn.
    rewrite negb_negb_b.
    reflexivity.
Qed.

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  intro n.
  induction n.
  Case "n = 0".
    reflexivity.
  Case "n = S n".
    rewrite even_SSn_eq_even_n.
    rewrite IHn.
    rewrite negb_negb_b.
    reflexivity.
Qed.

Theorem ble_nat_refl : forall n : nat,
  true = ble_nat n n.
Proof.
  intro n.
  induction n as [|n'].
  reflexivity.
  simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n : nat,
  beq_nat 0 (S n) = false.
Proof.
  intro n.
  destruct n as [|n']; reflexivity.
Qed.


Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intro b.
  induction b; reflexivity.
Qed.


Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p.
  induction p.
  simpl. intro. rewrite H. reflexivity.
  intro. simpl. rewrite IHp. reflexivity.
  rewrite H.
  reflexivity.
Qed.



Theorem S_nbeq_0 : forall n : nat,
                     beq_nat (S n) 0 = false.
Proof.
  intro n.
  induction n; reflexivity.
Qed.

Theorem mult_1_l : forall n : nat,
                     1 * n = n.
Proof.
  intro n.
  destruct n; simpl.
  reflexivity.
  rewrite plus_0_r.
  reflexivity.
Qed.


Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
    = true.
Proof.
  intros b c.
  destruct b, c; reflexivity.
Qed.

(*
Lemma plus_eq_0_l : forall a b : nat,
                 a + b = 0 -> a = 0.
Proof.
  intros.
Abort.
*)


Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction p.
  Case "p = 0".
    rewrite mult_0_r.
    rewrite mult_0_r.
    rewrite mult_0_r.
    simpl.
    reflexivity.
  Case "p > 0".
    rewrite mult_comm. simpl.
    rewrite mult_comm. rewrite IHp.
    rewrite plus_assoc.
    assert (H: n + m + n * p + m * p = n * p + n + (m * p + m)).
    assert (H0: n + m + n * p = n * p + n + m).
    rewrite plus_comm. rewrite plus_assoc.
    rewrite <- mult_n_Sm. reflexivity.
    rewrite H0.
    assert (H1: m * p + m = m + m * p). rewrite plus_comm. reflexivity.
    rewrite H1.
    rewrite <- plus_assoc. reflexivity.
    rewrite H.
    rewrite <- mult_n_Sm. rewrite <- mult_n_Sm.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n.
  Case "n = 0".
    rewrite mult_0_l.
    rewrite mult_0_l.
    reflexivity.
  Case "n > 0".
    simpl.
    rewrite mult_plus_distr_r.
    rewrite IHn.
    reflexivity.
Qed.


Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intro n.
  induction n.
  Case "n = 0". reflexivity.
  Case "n = S n". simpl. rewrite <- IHn. reflexivity.
Qed.


Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite plus_assoc.
  rewrite plus_assoc.
  replace (n + m) with (m + n).
    reflexivity.
  Case "n + m = m + n".
    rewrite plus_comm.
    reflexivity.
Qed.

Theorem plus_1_l : forall a : nat, 1 + a = S a.
Proof. reflexivity. Qed.
Theorem plus_1_r : forall a : nat, a + 1 = S a.
Proof. intro. rewrite plus_comm. rewrite plus_1_l. reflexivity. Qed.

Theorem mult_2_l : forall a : nat, 2 * a = a + a.
Proof. intro.  simpl. rewrite plus_assoc. rewrite plus_0_r. reflexivity. Qed.

Theorem plus_swap_dist : forall a b c d : nat,
                           (a + b) + (c + d) = (a + c) + (b + d).
Proof.
  intros.
  replace (a + b + (c + d)) with (b + (c + d) + a).
  replace (a + c + (b + d)) with (c + (b + d) + a).
  replace (b + (c + d)) with (c + (b + d)).
  reflexivity.
  Case "(b + (c + d)) with (c + (b + d))". rewrite <- plus_swap. reflexivity.
  Case "c + (b + d) + a = a + c + (b + d)".
    rewrite plus_comm. rewrite plus_assoc. reflexivity.
  Case "b + (c + d) + a = a + b + (c + d)".
    rewrite plus_comm. rewrite plus_assoc. reflexivity.
Qed.

Theorem binary_unary_conv_inc_comm :
  forall a : bin, S (bin2nat a) = bin2nat (inc a).
Proof.
  intro a.
  induction a.
  Case "a = O".
    reflexivity.
  Case "a = T2".
    simpl.
    rewrite <- plus_1_l.
    rewrite plus_comm.
    reflexivity.
  Case "a = T1".
    simpl.
    rewrite <- IHa.
    rewrite mult_comm.
    replace (S (bin2nat a) * 2) with (2 * S (bin2nat a)).
    rewrite <- plus_1_l.
    rewrite plus_swap.
    rewrite mult_2_l.
    rewrite mult_2_l.
    rewrite plus_swap_dist.
    rewrite plus_1_r.
    reflexivity.
  rewrite mult_comm.
  reflexivity.
Qed.

Fixpoint divtwo (n: nat) : nat :=
  match n with
    | 0 => 0
    | 1 => 0
    | S (S n) => S (divtwo n)
  end.

Fixpoint modtwo (n : nat) : nat :=
  match evenb n with
      | true => 1
      | false => 0
  end.

(* (* I'm so stupid... divtwo not recognized as reduction *)
Fixpoint nat2bin (n : nat) : bin :=
  match n with
    | 0 => O
    | _ => match evenb n with
            | true => T2 (nat2bin (divtwo n))
            | false => T1 (nat2bin (divtwo n))
          end
  end
*)
