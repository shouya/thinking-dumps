Require Import List.
Import ListNotations.
Require Import Lia.

Definition set X := X -> Prop.

Inductive term : Type :=
| T0 : term
| TTrue : term
| TFalse : term
| TSucc (t: term) : term
| TPred (t: term) : term
| TIszero (t: term) : term
| TIf (t1 t2 t3: term) : term
.
Hint Constructors term.

Definition emptyset {X} : set X := fun x => False.
Definition union {X} (a b: set X) : set X := fun x => a x \/ b x.
Definition union3 {X} (a b c: set X) : set X := fun x => a x \/ b x \/ c x.
Definition singletonset {X} (x: X) : set X := fun x' => x = x'.
Definition setfromlist {X} (xs : list X) : set X := fun x => In x xs.
Definition setfrommappedset {X} (xs : set X) (f : X -> set X) : set X :=
  fun x => exists y, xs y /\ f y x.

Definition subset {X} (a b : set X) :=
  forall x, a x -> b x.

Hint Unfold emptyset.
Hint Unfold union.
Hint Unfold union3.
Hint Unfold singletonset.
Hint Unfold setfromlist.
Hint Unfold setfrommappedset.
Hint Unfold subset.
Hint Unfold List.In.

(* concrete term from 3.2.3 *)
Fixpoint Sterm (n : nat) : set term :=
  match n with
  | 0 => emptyset
  | S n => let stn := Sterm n
          in union3
               (setfromlist [T0; TTrue; TFalse])
               (setfrommappedset
                  stn (fun x => setfromlist [TSucc x; TPred x; TIszero x]))
               (setfrommappedset
                  stn (fun x => (setfrommappedset
                                stn (fun y => (setfrommappedset
                                              stn (fun z => singletonset (TIf x y z)))))))
  end.
Hint Unfold Sterm.

(* ex 3.2.5  *)
Lemma Sterm_cumulative :
  forall n, subset (Sterm n) (Sterm (S n)).
Proof.
  induction n.
  - simpl. repeat intro.
    inversion H.

  - repeat intro.
    simpl in H. unfold union3 in H.
    destruct H.

    + left. auto.
    + destruct H.
      * right. left.
        unfold setfrommappedset in *. destruct H. destruct H.
        apply IHn in H.
        exists x0. split; auto.
      * right. right. unfold setfrommappedset in *.
        destruct H. destruct H. destruct H0.
        destruct H0. destruct H1. destruct H1.
        apply IHn in H. apply IHn in H0. apply IHn in H1.
        exists x0. split; auto. exists x1. split; auto. exists x2. split; auto.
Qed.

(* because Sterm_cumulative, we can define the limit like this *)
Definition Sterm_lim : set term := fun x => exists n, Sterm n x.

Hint Unfold Sterm_lim.

Corollary Sterm_inclusion :
  forall n m, n <= m -> subset (Sterm n) (Sterm m).
Proof.
  intros.
  induction H.
  - auto.
  - repeat intro.
    apply Sterm_cumulative. apply IHle. apply H0.
Qed.

Definition max3 a b c := (Nat.max (Nat.max a b) c).

Lemma max3_le : forall a b c,
    a <= max3 a b c /\
    b <= max3 a b c /\
    c <= max3 a b c.
Proof.
  intros. unfold max3.
  split; try split; lia.
Qed.

Definition Sterm_complete : forall x, Sterm_lim x.
Proof.
  intros.
  induction x;
    try solve [exists 1; eauto 10];
    try solve [destruct IHx as [n ?]; exists (S n); eauto 20].
  destruct IHx1 as [n1 ?].
  destruct IHx2 as [n2 ?].
  destruct IHx3 as [n3 ?].
  exists (S (max3 n1 n2 n3)).
  destruct (max3_le n1 n2 n3) as [Hn1 [Hn2 Hn3]].
  simpl. unfold union3. right. right.
  unfold setfrommappedset.
  exists x1. split.
  eapply Sterm_inclusion with (n := n1); auto.
  exists x2. split.
  eapply Sterm_inclusion with (n := n2); auto.
  exists x3. split.
  eapply Sterm_inclusion with (n := n3); auto.
  eauto.
Qed.
