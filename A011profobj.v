
Require Export A010logic.

Print beautiful.

Theorem eight_is_beautiful: beautiful 8.
Proof.
    apply b_sum with (n := 5) (m := 3).
    apply b_3.
    apply b_5. Qed.

Print eight_is_beautiful.
Check (b_sum 3 5 b_3 b_5).
Check (b_sum 3 8 b_3 (b_sum 3 5 b_3 b_5)).

Theorem eight_is_beautiful': beautiful 8.
Proof.
   apply (b_sum 3 5 b_3 b_5).
Qed.

Theorem eight_is_beautiful'': beautiful 8.
Proof.
  Show Proof.
  apply b_sum with (n:=3) (m:=5).
  Show Proof.
  apply b_5.
  Show Proof.
  apply b_3.
  Show Proof.
Qed.

Theorem eleven_is_beautiful : beautiful 11.
  apply b_sum with (m:=3) (n:=8). Show Proof.
  apply b_3. Show Proof.
  apply (b_sum 3 5 b_3 b_5). Show Proof.
Qed.

Definition eight_is_beautiful''' : beautiful 8 :=
  b_sum 3 5 b_3 b_5.

Print eight_is_beautiful'''.



Theorem six_is_beautiful :
  beautiful 6.
Proof.
  apply (b_sum 3 3 b_3 b_3).
Qed.


Definition six_is_beautiful' : beautiful 6 :=
  b_sum 3 3 b_3 b_3.

Theorem b_plus3: forall n, beautiful n -> beautiful (3+n).
Proof.
   intros n H.
   apply b_sum.
   apply b_3.
   apply H.
Qed.

Definition b_plus3' : forall n, beautiful n -> beautiful (3+n) :=
  fun (n : nat) => fun (H : beautiful n) =>
    b_sum 3 n b_3 H.

Definition b_plus3'' (n : nat) (H : beautiful n) : beautiful (3+n) :=
  b_sum 3 n b_3 H.

Definition beautiful_plus3 : Prop :=
  forall n (E : beautiful n), beautiful (n+3).


(* In general, "P → Q" is just syntactic sugar for "∀ (_:P), Q". *)
Theorem b_times2 : forall n, beautiful n -> beautiful (2*n).
Proof.
  intros.
  replace (2*n) with (n+n).
  Show Proof.
  apply (b_sum n n H H).
  Show Proof.
  Print eq_ind.
  simpl. rewrite plus_assoc.
  rewrite plus_0_r. Show Proof.
  reflexivity. Show Proof.
Qed.

Definition b_times2': forall n, beautiful n -> beautiful (n+n) :=
  fun n (H: beautiful n) => b_sum n n H H.

Theorem gorgeous_plus13_p: forall n, gorgeous n -> gorgeous (13+n).
Proof.
  intros. Show Proof.
  apply g_plus5. Show Proof.
  apply g_plus5. Show Proof.
  apply g_plus3. Show Proof.
  apply H. Show Proof.
Qed.


Definition gorgeous_plus13_po: forall n, gorgeous n -> gorgeous (13+n):=
  fun n (H: gorgeous n) => g_plus5 (8+n) (g_plus5 (3+n) (g_plus3 n H)).

Theorem and_example :
  (beautiful 0) /\ (beautiful 3).
Proof.
  apply conj. Show Proof.
  apply b_0. Show Proof.
  apply b_3. Show Proof.
  Print conj. (* fun (P: Prop) (Q: Prop) (_: P) (_: Q) => and P Q *)
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  split.
    (* Case "left". *) apply HQ.
    (* Case "right". *) apply HP. Qed.
Print and_commut.

Check conj. (* fun (P Q : Prop) (_: P) (_: Q) => and P Q : and P Q *)
Print conj. (* fun (_: P) (_: Q) : and P Q *)

(* ===>
   and_commut =
     fun (P Q : Prop) (H : P /\ Q) =>
     match H with
     | conj HP HQ => conj Q P HQ HP
     end
     : forall P Q : Prop, P /\ Q -> Q /\ P *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) (H1 : P /\ Q) (H2 : Q /\ R) =>
    match H1 with
      | conj HP HQ => match H2 with
                        | conj _ HR => conj P R HP HR
                      end
    end.

Definition beautiful_iff_gorgeous :
  forall n, beautiful n <-> gorgeous n :=
  fun n =>
    conj (beautiful n -> gorgeous n) (gorgeous n -> beautiful n)
         (beautiful__gorgeous n) (gorgeous__beautiful n).

(*
Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.
*)

Definition or_comm : forall P Q, P \/ Q -> Q \/ P :=
  fun P Q (H1 : P \/ Q) =>
    match H1 with
      | or_introl HP => or_intror Q P HP
      | or_intror HQ => or_introl Q P HQ
    end.

Check ex.

Definition some_nat_is_even : Prop :=
  ex _ ev.

(*
Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.
*)

Definition snie : some_nat_is_even :=
  ex_intro _ ev 4 (evSS 2 (evSS 0 ev0)).



Definition ex_beautiful_Sn : ex _ (fun n => beautiful (S n)) :=
  ex_intro _ (fun x => beautiful (S x)) 2 b_3.

Lemma plus_comm_r : forall a b c, c + (b + a) = c + (a + b).
Proof.
   intros a b c. Show Proof.
   rewrite (plus_comm b). Show Proof.
   (* (fun a b c : nat =>
         eq_ind_r (fun n : nat => c + n = c + (a + b))
                  ?128
                  (plus_comm b a)) *)
   Print eq_ind_r.
   (* eq_ind_r = fun (A : Type) (x : A) (P : A -> Prop)
                     (H : P x) (y : A) (H0 : y = x) =>
                   eq_ind x (fun y0 : A => P y0) H y (eq_sym H0)
     : forall (A : Type) (x : A) (P : A -> Prop),
         P x -> forall y : A, y = x -> P y *)
   reflexivity. Show Proof.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros.
  apply (trans_eq _ _ [c;d]); assumption.
Qed.

Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n.
Show Proof.
Defined.

Compute (add1 2).
