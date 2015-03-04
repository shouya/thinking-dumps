Require Export A014imp.

Require Import Coq.Bool.Bool.


Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state),
    beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st || st') <-> (c2 / st || st').



(* Exercise: 2 stars (equiv_classes) *)

Definition prog_a : com :=
  WHILE BNot (BLe (AId X) (ANum 0)) DO
    X ::= APlus (AId X) (ANum 1)
  END.

Definition prog_b : com :=
  IFB BEq (AId X) (ANum 0) THEN
    X ::= APlus (AId X) (ANum 1);;
    Y ::= ANum 1
  ELSE
    Y ::= ANum 0
  FI;;
  X ::= AMinus (AId X) (AId Y);;
  Y ::= ANum 0.

Definition prog_c : com :=
  SKIP.

Definition prog_d : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= APlus (AMult (AId X) (AId Y)) (ANum 1)
  END.

Definition prog_e : com :=
  Y ::= ANum 0.

Definition prog_f : com :=
  Y ::= APlus (AId X) (ANum 1);;
  WHILE BNot (BEq (AId X) (AId Y)) DO
    Y ::= APlus (AId X) (ANum 1)
  END.

Definition prog_g : com :=
  WHILE BTrue DO
    SKIP
  END.

Definition prog_h : com :=
  WHILE BNot (BEq (AId X) (AId X)) DO
    X ::= APlus (AId X) (ANum 1)
  END.

Definition prog_i : com :=
  WHILE BNot (BEq (AId X) (AId Y)) DO
    X ::= APlus (AId Y) (ANum 1)
  END.



Definition equiv_classes : list (list com) :=
  [[prog_a ; prog_g ] ;
    [prog_c ; prog_h] ;
    [prog_i] ;
    [prog_f] ;
    [prog_e] ;
    [prog_b]
  ].
(* GRADE_TEST 2: check_equiv_classes equiv_classes *)


Theorem aequiv_example:
  aequiv (AMinus (AId X) (AId X)) (ANum 0).
Proof.
  unfold aequiv. intros.
  unfold aeval.
  assert (forall n : nat, n - n = 0).
  intros. induction n. reflexivity. assumption.
  apply H.
Qed.

Theorem bequiv_example:
  bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue.
Proof.
  unfold bequiv. intros. unfold beval. simpl. rewrite minus_diag. reflexivity.
Qed.

Theorem skip_left: forall c,
  cequiv
     (SKIP;; c)
     c.
Proof.
  unfold cequiv. intros.
  split; intros.

  Case "→".
  inversion H; subst.
  inversion H2; subst.
  assumption.

  Case "←".
  apply E_Seq with (st' := st).
  apply E_Skip. assumption.
Qed.


(* Exercise: 2 stars (skip_right) *)

Theorem skip_right: forall c,
  cequiv
    (c;; SKIP)
    c.
Proof.
  unfold cequiv. intros.
  split; intros.

  inversion H; subst. inversion H5; subst. assumption.
  apply E_Seq with (st' := st'). assumption. apply E_Skip.
Qed.


Theorem IFB_true_simple: forall c1 c2,
  cequiv
    (IFB BTrue THEN c1 ELSE c2 FI)
    c1.
Proof.
  unfold cequiv. intros.
  split; intros.

  Case "->".
  inversion H; subst. assumption. inversion H5.

  Case "<-".
  apply E_IfTrue. reflexivity. assumption.
Qed.

(* Exercise: 2 stars (IFB_false) *)
Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c2.
Proof.
  unfold bequiv. unfold cequiv. intros.
  split; intros.

  inversion H0; subst; try assumption.
  specialize H with st.
  inversion H.
  rewrite H2 in H6. inversion H6.

  specialize H with st.
  inversion H.
  apply E_IfFalse; try assumption.
Qed.

(* Exercise: 3 stars (swap_if_branches) *)
Lemma bool_neg_equiv :
  forall st b r, beval st b = r <-> beval st (BNot b) = negb r.
Proof.
  intros. split; intros.
  destruct r; (simpl; rewrite H; reflexivity).
  destruct r; inversion H; [apply negb_false_iff in H1 | apply negb_true_iff in H1]; assumption.
Qed.

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  unfold cequiv; intros.
  split; intros.

  Case "b ? e1 : e2 -> !b ? e2 : e1".
  inversion H; subst.
  apply E_IfFalse; try assumption. simpl. apply negb_false_iff; assumption.
  apply E_IfTrue; try assumption. simpl. apply negb_true_iff. assumption.

  Case "!b ? e2 : e1 -> b ? e1 : e2".
  inversion H; subst. simpl in H5.
  apply E_IfFalse; apply negb_true_iff in H5;  assumption.
  apply E_IfTrue;  simpl in H5; apply negb_false_iff in H5; assumption.
Qed.
