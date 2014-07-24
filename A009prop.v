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

Lemma ev_n__nev_Sn : forall n, ev n -> ~(ev (S n)).

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
  intros.
  generalize dependent m.
  induction n.
  intros.
  apply O_le_n.

  intros.
  inversion H.
  constructor.

  subst.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt.
 (* FILL IN HERE *) Admitted.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  (* Hint: This may be easiest to prove by induction on m. *)
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.
Proof.
  (* Hint: This theorem can be easily proved without using induction. *)
  (* FILL IN HERE *) Admitted.
