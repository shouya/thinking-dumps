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


Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros.
(*(* the induction way *)
  induction H.
  simpl. apply ev0.
  simpl. apply H.
*)
  (* the inversion way *)
  inversion H.
  simpl. apply ev0.
  simpl. assumption.

  (* ex: Why not `destruct`?
     because destruct does not introduce the inductive rule for
      ev n -> ev (S (S n))
     therefore the second goal will be `ev (S (S n))` while without an
     assumption of `ev n`, which is not provable.
  *)
 Qed.

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros.
  inversion H.
  assumption.
Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  inversion H.
  inversion H1.
  assumption.
Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros.
  inversion H. inversion H1. inversion H3.
Qed.



Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros.
  induction H0.

  simpl in H. assumption.

  simpl in H. inversion H.
  apply IHev in H2. assumption.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros.
  apply ev_sum with (n := n + p) in H.
  replace (n + p + (n + m)) with (double n + m + p) in H.
  rewrite <- plus_assoc in H.
  apply ev_ev__ev with (m := m + p) in H. assumption.

  (* disgusting.... *)
  assert (forall n' m', double n' + m' + m' = double (n' + m')).
  clear. intros. rewrite double_plus.
  replace (n' + n' + m' + m') with ((n' + m') + (n' + m')).
  rewrite <- double_plus. reflexivity.
  rewrite <- plus_assoc. replace (m' + (n' + m')) with (n' + m' + m').
  rewrite plus_assoc. rewrite plus_assoc. reflexivity.
  rewrite plus_comm. reflexivity.
  rewrite H1. apply double_even.

  rewrite double_plus.
  rewrite plus_assoc. rewrite <- plus_assoc with (m := p).
  rewrite <- plus_comm with (m := p) (n := n).
  rewrite plus_assoc. rewrite <- plus_assoc with (m := p).
  rewrite plus_comm with (m := m) (n := p).
  rewrite plus_assoc. reflexivity.

  assumption.
Qed.


Inductive pal {X : Type} : list X -> Prop :=
  | pal_null : pal []
  | pal_one : forall x, pal [x]
  | pal_induction : forall (xs : list X) (x : X),
                      pal xs -> pal ([x] ++ xs ++ [x]).

Lemma snoc_app :
  forall {X : Type} (xs : list X) (x : X), snoc xs x = xs ++ [x].
Proof.
  intros.
  induction xs.
  simpl. reflexivity.
  simpl.
  rewrite IHxs. reflexivity.
Qed.

Lemma cons_app :
  forall {X : Type} (xs : list X) (x : X), cons x xs = [x] ++ xs.
Proof.
  intros.
  induction xs.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Lemma app_assoc' : forall {X : Type} (l m n: list X),
                     l ++ m ++ n = (l ++ m) ++ n.
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros.
  rewrite IHl.
  reflexivity.
Qed.


Goal forall {X : Type} (l : list X), pal (l ++ rev l).
Proof.
  intros.
  induction l.
  Case "l = []".
    simpl. apply pal_null.
  Case "l = x :: l".
    simpl. rewrite cons_app.
    rewrite snoc_app.
    replace ([x] ++ l ++ rev l ++ [x]) with ([x] ++ (l ++ rev l) ++ [x]).
    apply pal_induction. assumption.

    replace ((l ++ rev l) ++ [x]) with (l ++ rev l ++ [x]).
    reflexivity. apply app_assoc'.
Qed.

Lemma rev_appl : forall {X:Type} (l : list X) (x : X),
                   rev (l ++ [x]) = [x] ++ rev l.
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  rewrite snoc_app.
  rewrite snoc_app.
  rewrite IHl.
  rewrite cons_app with (xs := (rev l ++ [x0])).
  symmetry.
  apply app_assoc'.
Qed.

Goal forall {X:Type} (l : list X), pal l -> l = rev l.
Proof.
  intros.
  induction H.
  reflexivity.
  reflexivity.

  simpl.
  rewrite snoc_app.
  rewrite rev_appl.
  rewrite cons_app.
  rewrite <- IHpal.
  apply app_assoc'.
Qed.

Lemma rev_appr : forall {X:Type} (l : list X) (x : X),
                   rev ([x] ++ l) = rev l ++ [x].
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  rewrite snoc_app.
  rewrite snoc_app.
  reflexivity.
Qed.

Goal forall {X:Type} (l:list X), l = rev l -> pal l.
Proof.
  induction l.
  intros.
  apply pal_null.

  simpl.
  rewrite cons_app.
  rewrite snoc_app.
  intros.

  induction (rev l) eqn:revl.
  inversion H. constructor.

  inversion H. clear IHl0.

  (* TODO: too difficult. 5 star question *)
Abort.

Inductive subseq : list nat -> list nat -> Prop :=
  | ss_nul : forall ns, subseq [] ns
  | ss_mat : forall ns ms, subseq ns ms -> (forall n, subseq (n::ns) (n::ms))
  | ss_notmat : forall ns ms, subseq ns ms -> (forall m, subseq ns (m :: ms)).

Theorem subseq_refl : forall l, subseq l l.
Proof.
  intros.
  induction l.

  constructor.
  constructor. assumption.
Qed.

Lemma app_comm_cons' :
  forall {A:Type} (x y:list A) (a:A), a :: (x ++ y) = (a :: x) ++ y.
Proof.
  intros.
  induction x.
  reflexivity.
  reflexivity.
Qed.

Theorem subseq_app : forall l1 l2 l3, subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros.
  induction H.

  constructor.

  rewrite <- app_comm_cons'.
  constructor. assumption.

  rewrite <- app_comm_cons'.
  constructor. assumption.
Qed.

Lemma subseq_notnull : forall x, forall l1,
                         ~(subseq (x :: l1) []).
Proof.
  intros. intro.
  inversion H.
Qed.


Theorem subseq_trans : forall l1 l2 l3,
                         subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros l1 l2 l3 H1 H2.
  generalize dependent l2.
  generalize dependent l3.

  induction l1.
  constructor.

  intros.
  induction H1.
  constructor.

(* To save your life, keep away from such tough questions *)
Abort.


Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.

Goal R 2 [1;0].
Proof.
  apply c2. apply c2. apply c1.
Qed.

Goal R 1 [1;2;1;0].
Proof.
  apply c3. apply c2. apply c3. apply c3. apply c2. apply c2. apply c2.
  apply c1.
Qed.

Goal R 6 [3;2;1;0].
Proof.
  (* impossible to prove this *)
Abort.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Definition lt n m := le (S n) m.

Notation "m <= n" := (le m n).

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
  | ne_1 : ev (S n) -> next_even n (S n)
  | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

Inductive total_relation : nat -> nat -> Prop :=
  | tr_0 : forall m, total_relation 0 m
  | tr_n : forall n m,
             total_relation n m -> total_relation (S n) m.

Theorem total_relation_all : forall n m, total_relation n m.
Proof.
  intros.
  induction n.
  constructor.
  constructor. assumption.
Qed.


Inductive empty_relation : nat -> nat -> Prop :=.

Example er_1: ~(empty_relation 6 5). Proof. intro. induction H. Qed.


Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros.
  induction H0.
  assumption.
  constructor.
  apply IHle.
  assumption.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  induction n.
  constructor.
  constructor. assumption.
Qed.


Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros.
  induction H.
  constructor.
  constructor.
  assumption.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  induction m.
  intros.
  inversion H.
  constructor.

  inversion H2.

  intros.
  inversion H.
  constructor.

  apply IHm in H2.
  constructor.
  assumption.
Qed.


Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  induction b.
  rewrite plus_0_r.
  constructor.

  rewrite plus_comm.
  simpl.
  rewrite plus_comm.
  constructor.
  assumption.
Qed.

Lemma plus_le_l : forall n1 n2 m,
                    le (n1 + n2) m -> le n1 m.
Proof.
  intros.
  generalize dependent n2.
  induction n2.

  intros.
  replace (n1 + 0) with n1 in H. assumption.
  rewrite plus_0_r. reflexivity.

  intros. apply IHn2.
  replace (n1 + S n2) with (S (n1 + n2)) in H.
  apply le_S in H.
  apply Sn_le_Sm__n_le_m in H. assumption.
  rewrite plus_comm with (m := S n2) (n := n1).
  simpl.
  rewrite plus_comm with (m := n2) (n := n1). reflexivity.
Qed.

Lemma plus_le_self : forall n m, le n (n + m).
Proof.
  intros.
  induction n.
  simpl. apply O_le_n.
  simpl.
  apply n_le_m__Sn_le_Sm. assumption.
Qed.

Theorem plus_lt : forall n1 n2 m,
  lt (n1 + n2) m ->
  lt n1 m /\ lt n2 m.
Proof.
  unfold lt.
  intros. inversion H.
  split.

  apply n_le_m__Sn_le_Sm.
  apply plus_le_self.

  apply n_le_m__Sn_le_Sm. rewrite plus_comm.
  apply plus_le_self.

  split. subst.

  apply n_le_m__Sn_le_Sm.
  apply Sn_le_Sm__n_le_m in H.
  assert (n1 <= n1 + n2). apply plus_le_self.
  apply le_trans with (n1+n2); assumption.

  apply n_le_m__Sn_le_Sm. subst.
  apply Sn_le_Sm__n_le_m in H.
  assert (n2 <= n1 + n2). rewrite plus_comm. apply plus_le_self.
  apply le_trans with (n1+n2); assumption.
Qed.


Theorem lt_S : forall n m,
  lt n m ->
  lt n (S m).
Proof.
  unfold lt.
  intros.
  apply le_S. assumption.
Qed.


Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  intro.
  induction n.
  intros. apply O_le_n.

  intros.
  induction m.
  simpl in H. inversion H.
  simpl in H. apply n_le_m__Sn_le_Sm. apply IHn.
  assumption.
Qed.

Lemma ble_refl : forall m, ble_nat m m = true.
Proof.
  intros. induction m. reflexivity. simpl. assumption.
Qed.


Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  intros.
  generalize dependent n.
  induction m.
  intro. intro.
  inversion H. reflexivity.

  destruct n.
  simpl. reflexivity.

  intro. simpl. apply IHm. apply Sn_le_Sm__n_le_m in H.
  assumption.
Qed.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.
Proof.
  intros.
  apply le_ble_nat.
  apply ble_nat_true in H.
  apply ble_nat_true in H0.

  apply le_trans with m; assumption.
Qed.

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  intros.
  generalize dependent n.

  induction m. intros. intro. inversion H0. subst. inversion H.

  intros. intro. destruct n. inversion H.

  simpl in H. apply IHm in H. apply Sn_le_Sm__n_le_m in H0.
  apply H. assumption.
Qed.

Module R.

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

Example r_test_1 : R 1 1 2.
Proof. apply c3. apply c2. apply c1. Qed.

Example r_test_2 : R 2 2 6.
Proof.
  apply c3. apply c2. apply c3. apply c2.
Abort.

(* If we dropped constructor c5 from the definition of R, would the set of provable propositions change? Briefly (1 sentence) explain your answer.  *)

(* Answer: No, because c2 and c3 is symmetric over m and n. *)


(* If we dropped constructor c4 from the definition of R, would the set of provable propositions change? Briefly (1 sentence) explain your answer. *)

(* Answer: No, because c4 is equivalent to c2 + c3. *)

Goal forall m n o, m + n = o -> R m n o.
Proof.
  intros.
  generalize dependent o.
  induction m.
    induction n.
      destruct o.
        constructor.
        intro. inversion H.
      destruct o.
        intro. inversion H.
        intro. constructor. apply IHn. inversion H. reflexivity.
    induction n.
      intros. destruct o.
        inversion H.
        constructor. apply IHm. inversion H. reflexivity.
      intros.
        destruct o.
          inversion H.
          destruct o.
            inversion H. destruct m; inversion H1.
            constructor. apply IHm. inversion H. reflexivity.
Qed.

Goal forall m n o, R m n o -> m + n = o.
Proof.
  intros.
  induction H.
    reflexivity.
    rewrite plus_Sn_m. apply f_equal. assumption.
    rewrite <- plus_n_Sm. apply f_equal. assumption.
    inversion IHR. rewrite <- plus_n_Sm in H1. inversion H1. reflexivity.
    rewrite plus_comm. assumption.
Qed.

End R.



Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.


Definition teen : nat->Prop := between 13 19.

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

Definition natural_number_induction_valid : Prop :=
  forall (P:nat->Prop),
    true_for_zero P ->
    preserved_by_S P ->
    true_for_all_numbers P.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => if oddb n then Podd n else Peven n.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros.
  unfold combine_odd_even.
  destruct (oddb n).
  apply H. reflexivity.
  apply H0. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros.
  unfold combine_odd_even in H.
  rewrite H0 in H. assumption.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros.
  unfold combine_odd_even in H.
  rewrite H0 in H. assumption.
Qed.

Fixpoint true_upto_n__true_everywhere n (P : nat -> Prop) : Prop :=
  match n with
    | 0 => (forall m, P m)
    | S n => P (S n) -> true_upto_n__true_everywhere n P
  end.


Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity. Qed.
