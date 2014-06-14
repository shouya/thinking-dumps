Module Playgroud1.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | (S n') => n'
  end.

End Playgroud1.



Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | (S O) => false
  | (S (S a)) => evenb a
  end.

Definition oddb (n:nat) : bool :=
  negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O)))))
                    = false.
Proof. reflexivity. Qed.

Module Playground2.
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | (S n') => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity. Qed.

Fixpoint minus (m n : nat) :=
  match m, n with
  | O, _ => 0
  | S m', O => m
  | (S m'), (S n') => minus m' n'
  end.

End Playground2.

Fixpoint exp (a n : nat) : nat :=
  match n with
  | O => S O
  | S n' => (mult a (exp a n'))
  end.


Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | 1 => 1
  | (S n') => (mult n (factorial n'))
  end.
Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.


Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                      : nat_scope.
Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                      : nat_scope.
Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                      : nat_scope.
Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | _ => false
    end
  | S n' => match m with
            | O => false
            | S m' => (beq_nat n' m')
    end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => (ble_nat n' m')
            end
  end.



Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.


Definition blt_nat (n m : nat) : bool :=
  (andb (ble_nat n m) (negb (beq_nat n m))).


Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.


(* proof by simplification *)

Theorem plus_0_n : forall n: nat, 0 + n = n.
Proof.
  intro n.
  reflexivity.
Qed.


Theorem plus_1_l : forall n: nat, 1 + n = S n.
Proof.
  intro n.
  reflexivity.
Qed.


Theorem mult_0_l : forall n: nat, 0 * n = 0.
Proof.
  intros n. simpl. reflexivity.
Qed.


(* proof by rewriting *)

Theorem plus_id_example : forall n m : nat,
  n = m -> n + n = m + m.
Proof.
  intros n m.
  intro H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H H'.
  rewrite H.
  rewrite H'.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_0_n.
  reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m.
  intro H.
  rewrite plus_1_l.
  rewrite H.
  reflexivity.
Qed.


Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intro n.
  destruct n as [| n'].
  reflexivity.
  simpl. reflexivity.
Qed.


Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intro n.
  destruct n as [| n']; reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall b : bool, f (f b) = b.
Proof.
  intros.
  rewrite H.
  rewrite H.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall b : bool, f (f b) = b.
Proof.
  intros.
  rewrite H.
  rewrite H.
  destruct b; (compute; reflexivity).
Qed.


Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) -> b = c.
Proof.
  intros b c.
  destruct b, c; simpl.
  reflexivity.
  intro. rewrite H. reflexivity.
  intro. rewrite H. reflexivity.
  reflexivity.
Qed.


Inductive bin : Type :=
  | O : bin
  | T2 : bin -> bin
  | T1 : bin -> bin.

Fixpoint inc(n : bin) :=
  match n with
  | O => T1 O
  | T1 a => T2 (inc a)
  | T2 a => T1 a
  end.

Example inc_O_is_T1O : inc O = T1 O.
Proof. reflexivity. Qed.
Example inc_1_is_T2T1O : inc (T1 O) = T2 (T1 O).
Proof. reflexivity. Qed.
Example inc_2_is_T1T10 : inc (T2 (T1 O)) = T1 (T1 O).
Proof. reflexivity. Qed.
Example inc_3_is_T2T20 :
  inc (T1 (T1 O)) = T2 (T2 (T1 O)).
Proof. reflexivity. Qed.

Fixpoint bin2nat(n : bin) : nat :=
  match n with
  | O => 0
  | T1 a => (bin2nat a) * 2 + 1
  | T2 a => (bin2nat a) * 2
  end.


(* TODO *)

(*
Fixpoint nat2bin(n : nat) : bin :=
  match n with
  | 0 => O
  | evenb n     => T2 (nat2bin n)
  | oddbb 1 => T1 (nat2bin n)
  end.
  *)

(*
   exercise: write a fix-point definition that
   does terminate on all input but coq does not
   accept because of this restriction.
*)

(*
Fixpoint plus' (n m : nat) : nat :=
  match n with
  | 0 => m
  | S 0 => S (plus' 0 m)
  | S (S n') => S (plus' n' (S m))
  end.
*)

(* this is cool *)
