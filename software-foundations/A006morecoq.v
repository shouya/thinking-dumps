Require Export A005poly.

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  (* At this point, we could finish with
     "rewrite → eq2. reflexivity." as we have
     done several times above. But we can achieve the
     same effect in a single step by using the
     apply tactic instead: *)
  apply eq2. Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.


Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m) ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.



Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros h1 h2.
  apply h1.
  apply h2.
Qed.


Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5 ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  rewrite H.  (* we cannot us apply here directly *)
  simpl.
  reflexivity.
Qed.

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5 ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl.
  apply H.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros.
  rewrite H.
  symmetry.
  apply rev_involutive.
Qed.


(* Difference between 'rewrite' and 'apply'

1. to use reflexivity you will always finish the goal.
   to use rewrite you will not finish the goal.
   to use apply either finish the goal or not is okay.
2. apply must apply on a hypothesis/lemma/theorem exactly matching the goal or
   exactly matching the simplified goal. where using rewrite it requires only
   that the goal contains the expression of one side of the hypo/lem/theom.
3. you can rewrite from the right hand side of a hypothesis, with the syntax
     rewrite <- xxx.
   while apply only apply hypothesis exactly matching even if it's simply
   swapped both sides of an equality. use 'symmetry' tactic to swap the
   expressions around an equality sign.
*)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.
Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.


Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  (* If we simply tell Coq apply trans_eq at this point,
     it can tell (by matching the goal against the
     conclusion of the lemma) that it should instantiate X
     with [nat], n with [a,b], and o with [e,f].
     However, the matching process doesn't determine an
     instantiation for m: we have to supply one explicitly
     by adding with (m:=[c,d]) to the invocation of
     apply. *)

  apply trans_eq with (m:=[c;d]). apply eq1. apply eq2. Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p h1 h2.
  apply trans_eq with (m := m).
  apply h2.
  apply h1.
Qed.


Example inversion_try1 : forall (m n : nat), (S m = S n) -> m = n.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  intros.
  inversion H0.
  reflexivity.
Qed.


Theorem silly6 : forall (n : nat),
     S n = 0 ->
     2 + 2 = 5.
Proof.
  intros.
  inversion H.
Qed.

Theorem silly7 : forall (n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m contra. inversion contra. Qed.

Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  intros.
  inversion H.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
    x = y -> f x = f y.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.


Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  intros.
  destruct n.
  reflexivity.
  inversion H.
Qed.


Theorem beq_nat_0_r : forall n,
   beq_nat n 0 = true -> n = 0.
Proof.
  destruct n.
  reflexivity.
  simpl. intro.
  inversion H.
Qed.


Example inversion_try2 : forall (n k k' : nat),
                           (n + k = n + k' -> k = k').
Proof.
  intros n k k'.
  induction n.
  Case "n = 0".
    intro.
    simpl.
    assumption.
  Case "n = S n".
    simpl.
    intro.
    apply IHn.
    inversion H.
    reflexivity.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b ->
     beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.


Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5 ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    intro.
    destruct m.
    SCase "m = 0". reflexivity.
    SCase "m = S m". intro. inversion H.
  Case "n = S n".
    intro. simpl.
    destruct m.
    SCase "m = 0".
      intro. inversion H.
    SCase "m = S m".
      simpl.
      intro.
      inversion H.
      rewrite <- plus_n_Sm in H1.
      rewrite <- plus_n_Sm in H1.
      inversion H1.
      apply IHn' in H2.
      apply f_equal.
      assumption.
Qed.

Theorem double_injective_try: forall n m, double n = double m -> n = m.
Proof.
  intros n m.
  induction n, m.
  reflexivity.
  intro. inversion H.
  intro. inversion H.
  simpl. intro. inversion H.
Abort.

Theorem double_injective_try: forall n m, double n = double m -> n = m.
Proof.
  intros n.
  induction n.
  Case "n = 0".
    intros m eq. simpl in eq.
    destruct m. reflexivity. inversion eq.
  Case "n = S n".
    intros m eq. simpl in eq.
    destruct m. inversion eq.
    simpl in eq. inversion eq. apply f_equal. apply IHn. assumption.
Qed.


Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intro n.
  induction n.
  Case "n = 0".
    intros m eq.
    induction m.
    SCase "m = 0". reflexivity.
    SCase "m = S m". inversion eq.
  Case "n = S n".
    intros m eq.
    induction m.
    SCase "m = 0".
      inversion eq.
    SCase "m = S m".
      inversion eq.
      apply f_equal.
      apply IHn.
      assumption.
Qed.


Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index n l = None.
Proof.
  intros.
  generalize dependent n.
  induction l.
  Case "l = []".
    intros. reflexivity.
  Case "l = x :: l".
    intros n eq.
    induction n.
    SCase "n = 0". inversion eq.
    SCase "n = S n". simpl. apply IHl. simpl in eq. inversion eq. reflexivity.
Qed.


Theorem length_snoc''' : forall (n : nat) (X : Type)
                                (v : X) (l : list X),
                           length l = n ->
                           length (snoc l v) = S n.
Proof.
  intros. generalize dependent n.
  induction l.
  Case "l = []".
    intros. simpl. rewrite <- H. reflexivity.
  Case "l = x :: l".
    simpl. intros.
    destruct n.
    SCase "n = 0". inversion H.
    SCase "n = S n".
      inversion H.
      rewrite H1.
      apply f_equal.
      apply IHl.
      assumption.
Qed.

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X)
                                 (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  intros X l1 l2 x.
  induction l1.
  Case "l1 = []". simpl. intros. assumption.
  Case "l1 = x :: l1". simpl. intros.
    destruct n.
      SCase "n = 0". inversion H.
      SCase "n = S n".
        inversion H.
        apply f_equal.
        rewrite H1.
        apply IHl1.
        assumption.
Qed.

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  intros X n l. generalize dependent n.
  induction l.
  Case "l1 = []". simpl. intros. rewrite <- H. reflexivity.
  Case "l1 = x : l1". simpl. intros.
  destruct n. inversion H. inversion H. simpl. apply f_equal.
  rewrite <- plus_n_Sm. rewrite H1.
  assert (forall (a b : list X), (length a) + (length b) = length (a ++ b)).
  intros. induction a. reflexivity. simpl. rewrite IHa. reflexivity.
  rewrite <- H0.
  simpl. rewrite <- plus_n_Sm. apply f_equal. rewrite H0. apply IHl.
  assumption.
Qed.

Theorem double_induction: forall (P : nat -> nat -> Prop),
  P 0 0 ->
  (forall m, P m 0 -> P (S m) 0) ->
  (forall n, P 0 n -> P 0 (S n)) ->
  (forall m n, P m n -> P (S m) (S n)) ->
  forall m n, P m n.
Proof.
  intros.
  generalize dependent n.
  induction m.
  intro n.
  induction n.
  assumption.
  apply H1. assumption.
  intro n.
  induction n.
  apply H0.
  apply IHm.
  apply H2.
  apply IHm.
Qed.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
      SCase "beq_nat n 5 = true". reflexivity.
      SCase "beq_nat n 5 = false". reflexivity. Qed.

Theorem override_shadow : forall (X:Type) x1 x2 k1 k2 (f : nat -> X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros.
  unfold override.
  destruct (beq_nat k1 k2).
  reflexivity.
  reflexivity.
Qed.


Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l.
  Case "l = []".
    simpl.
    intros.
    inversion H.
    reflexivity.
  Case "l = (x,y) :: l".
    intros.
    simpl in H.
    destruct x.
    destruct (split l).
    inversion H.
    simpl.
    apply f_equal.
    apply IHl.
    reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

(*
  My Note: destruct <expr> eqn:<eqn>. is used when the destructed case should be
           used in the following proof.

*)

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct (f b) eqn:f'.
  destruct b eqn:b'.
  Case "b = true, f true = true".
    rewrite f'. assumption.
  Case "b = false, f false = true".
    destruct (f true) eqn:f''.
    SCase "f true = true".
      rewrite f''. reflexivity.
    SCase "f true = false".
      rewrite f'. reflexivity.
  destruct b.
  Case "b = true, f true = false".
    destruct (f false) eqn:f''.
    SCase "f false = true". assumption.
    SCase "f false = false". assumption.
  Case "b = false".
    rewrite f'. assumption.
Qed.

Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat -> X),
  f k1 = x1 ->
  (override f k1 x1) k2 = f k2.
Proof.
  intros.
  unfold override.
  destruct (beq_nat k1 k2) eqn:eq.
  Case "k1 = k2".
    apply beq_nat_true in eq.
    rewrite <- eq. rewrite H. reflexivity.
  Case "k1 /= k2".
    reflexivity.
Qed.

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intro n.
  induction n as [| n'].
  Case "n = 0".
    intros m.
    destruct m.
    SCase "m = 0". reflexivity.
    SCase "m = S m".
      destruct (beq_nat 0 m).
      SSCase "0 = m". reflexivity.
      SSCase "0 /= m". reflexivity.
  Case "n = S n'".
    destruct m.
    SCase "m = 0". reflexivity.
    SCase "m = S m".
      destruct (beq_nat (S n') (S m)) eqn:eq.
      SSCase "S n = S m".
        simpl in eq. simpl. rewrite <- eq.
        apply IHn'.
      SSCase "S n /= S m".
        simpl in eq. simpl. rewrite <- eq.
        apply IHn'.
Qed.


Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
  intros.
  apply beq_nat_true in H.
  apply beq_nat_true in H0.
  rewrite H. rewrite H0.
  symmetry. apply beq_nat_refl.
Qed.



(*
Definition split_combine_statement : Prop :=
  forall (X : Type) (Y : Type)
         (l1 : list X) (l2 : list Y) (l : list (X * Y)),
      length l1 = length l
   -> length l2 = length l
   -> combine l1 l2 = l
   -> split l = (l1,l2)
*)


Definition split_combine_statement : Prop :=
  forall {X Y} (l1 : list X) (l2 : list Y) (l : list (X * Y)),
    length l1 = length l2 ->
    combine l1 l2 = l ->
    split l = (l1,l2).

Theorem split_combine : split_combine_statement.
Proof.
  unfold split_combine_statement.
  intros.
  generalize dependent l1.
  generalize dependent l2.
  induction l as [| [x y] l' ].

  Case "l = []".
    intros.
    destruct l1,l2.
    reflexivity.
    inversion H. inversion H.
    inversion H0.

  Case "l = (x,y) :: l'".
    intros.
    destruct l1,l2.

    SCase "l1 = l2 = []". inversion H0.
    SCase "l1 = [], l2 = y0::l2". inversion H.
    SCase "l1 = x0::l1, l2 = []". inversion H.
    SCase "l1 = x0::l1, l2 = y0::l2".
      simpl in H0.
      inversion H0.
      simpl.
      simpl in H. inversion H.
      apply IHl' in H5.
      rewrite H4.
      rewrite H5.
      reflexivity.

      SSCase "showing 'combine l1 l2 = l'". assumption.
Qed.


(*
Definition split_combine_statement : Prop :=
  forall {X Y} (l : list (X * Y)) l1 l2,
    (l1,l2) = split l -> combine l1 l2 = l.

Theorem split_combine : split_combine_statement.
Proof.
  unfold split_combine_statement.
  intros X Y l.
  induction l as [| [x y] l'].
  Case "l = []".
    simpl. intros.
    inversion H.
    reflexivity.
  Case "l = (x,y) :: l'".
    simpl. destruct (split l') as [lx ly]. intros.
    inversion H. simpl. apply f_equal. apply IHl'. reflexivity.
Qed.
*)

Theorem override_permute : forall (X:Type) x1 x2 k1 k2 k3 (f : nat -> X),
  beq_nat k2 k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros.
  unfold override.
  destruct (beq_nat k2 k3) eqn:eq.
  Case "k2 = k3".
    apply beq_nat_true in eq. rewrite <- eq.
    rewrite beq_nat_sym. rewrite H. reflexivity.
  Case "k2 /= k3".
    reflexivity.
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x l.
  induction l as [| x' l'].
  Case "l = []".
    intros.
    inversion H.
  Case "l = x' :: l'".
    destruct (test x') eqn:eq.
    SCase "test x' = true".
      simpl. rewrite eq. intros. inversion H. rewrite <- H1. assumption.
    SCase "test x' = false".
      simpl. rewrite eq. intro lf. apply IHl'.
Qed.

Fixpoint forallb {X} (f : X -> bool) (l : list X) : bool :=
  match l with
    | []       => true
    | x :: xs  => andb (f x) (forallb f xs)
  end.

Fixpoint existsb {X} f (l : list X) : bool :=
  match l with
    | []       => false
    | x :: xs  => orb (f x) (existsb f xs)
  end.

Definition existsb' {X} f (l : list X) := negb (forallb (fun x => negb (f x)) l).

Theorem existsb_variant : forall {X: Type} (f : X -> bool) (l: list X),
                            existsb f l = existsb' f l.
Proof.
  intros.
  induction l.
  Case "l = []".
    reflexivity.
  Case "l = x :: l".
    unfold existsb'.
    simpl.
    unfold existsb' in IHl.
    destruct (f x) eqn:fx.
    reflexivity.
    simpl. assumption.
Qed.
