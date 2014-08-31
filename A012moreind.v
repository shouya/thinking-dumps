
Require Export A011profobj.


Print nat_ind.
(*
nat_ind =
fun P : nat -> Prop => nat_rect P
     : forall P : nat -> Prop,
       P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
*)


Theorem mult_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind. reflexivity.
  simpl. intros. assumption.
Qed.

Print nat_rect.

(*
nat_rect =
fun (P : nat -> Type) (f : P 0) (f0 : forall n : nat, P n -> P (S n)) =>
fix F (n : nat) : P n :=
  match n as n0 return (P n0) with
  | 0 => f
  | S n0 => f0 n0 (F n0)
  end
     : forall P : nat -> Type,
       P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
*)


Definition nat_ind' (P : nat -> Prop) :
   (P 0) -> (forall n, P n -> P (S n)) -> forall n, P n.
Proof.
  intros. induction n.
  assumption. apply H0. assumption.
Defined.

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind'. reflexivity.
  intros. simpl. rewrite H. reflexivity.
Qed.

Print plus_one_r'.
(*
plus_one_r' =
nat_ind (fun n : nat => n + 1 = S n) eq_refl
  (fun (n : nat) (H : n + 1 = S n) =>
   eq_ind_r (fun n0 : nat => S n0 = S (S n)) eq_refl H)
     : forall n : nat, n + 1 = S n
*)

Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind.


Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.

Definition rgb_ind' (P : rgb -> Prop) (_ : P red) (_ : P green) (_ : P blue)
   : forall a : rgb, P a.
Proof.
  intros.
  induction a; assumption.
Qed.

Check rgb_ind'. (* forall P : rgb -> Prop, P red -> P green -> P blue -> forall a : rgb, P a *)
Check rgb_ind.  (* forall P : rgb -> Prop, P red -> P green -> P blue -> forall r : rgb, P r *)

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

Definition natlist_ind' (P : natlist -> Prop)
                        (_ : P nnil)
                        (_ : forall x l, P l -> P (ncons x l))
                        (n : natlist) := P n.
Check natlist_ind'.
(* !!!Notice!!! Not correct!
natlist_ind'
     : forall P : natlist -> Prop,
       P nnil ->
       (forall (x : nat) (l : natlist), P l -> P (ncons x l)) ->
       natlist -> Prop
*)

Check natlist_ind.
(*
natlist_ind
     : forall P : natlist -> Prop,
       P nnil ->
       (forall (n : nat) (n0 : natlist), P n0 -> P (ncons n n0)) ->
       forall n : natlist, P n
*)


Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

(* natlist1_ind :
 forall P : natlist1 -> Prop, P nnil1
                              -> (forall l, P l -> forall a, P (nsnoc1 l a))
                              -> forall l, P l.
*)
Check natlist1_ind.
(*
natlist1_ind
     : forall P : natlist1 -> Prop,
       P nnil1 ->
       (forall n : natlist1, P n -> forall n0 : nat, P (nsnoc1 n n0)) ->
       forall n : natlist1, P n
*)

Inductive byntree : Type :=
 | bempty : byntree
 | bleaf : yesno -> byntree
 | nbranch : yesno -> byntree -> byntree -> byntree.

(* byntree_ind
      : forall P: byntree -> Prop,
            P empty
        -> (forall x, P (bleaf x))
        -> (forall x t1 t2, P t1 -> P t2 -> P (nbranch x t1 t2))
        -> forall t, P t.
*)

Check byntree_ind.
(*
byntree_ind
     : forall P : byntree -> Prop,
       P bempty ->
       (forall y : yesno, P (bleaf y)) ->
       (forall (y : yesno) (b : byntree),
        P b -> forall b0 : byntree, P b0 -> P (nbranch y b b0)) ->
       forall b : byntree, P b
*)

(*
  ExSet_ind :
         ∀P : ExSet → Prop,
             (∀b : bool, P (con1 b)) →
             (∀(n : nat) (e : ExSet), P e → P (con2 n e)) →
             ∀e : ExSet, P e
*)

Inductive ExSet :=
  | con1 : bool -> ExSet
  | con2 : nat -> ExSet -> ExSet.
Check ExSet_ind.
(*
ExSet_ind
     : forall P : ExSet -> Prop,
       (forall b : bool, P (con1 b)) ->
       (forall (n : nat) (e : ExSet), P e -> P (con2 n e)) ->
       forall e : ExSet, P e
*)

Inductive tree (X:Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.

Definition tree_ind' {X} (P : tree X -> Prop) :
    (forall x : X, P (leaf X x))
    -> (forall t1 t2 : tree X, P t1 -> P t2 -> P (node X t1 t2))
    -> forall t : tree X, P t.
admit.
Defined.

Check tree_ind.

(*
      mytype_ind :
        ∀(X : Type) (P : mytype X → Prop),
            (∀x : X, P (constr1 X x)) →
            (∀n : nat, P (constr2 X n)) →
            (∀m : mytype X, P m →
               ∀n : nat, P (constr3 X m n)) →
            ∀m : mytype X, P m
*)

Inductive mytype (X : Type) :=
  | constr1 : X -> mytype X
  | constr2 : nat -> mytype X
  | constr3 : mytype X -> nat -> mytype X.
Check mytype_ind.
(*
mytype_ind
     : forall (X : Type) (P : mytype X -> Prop),
       (forall x : X, P (constr1 X x)) ->
       (forall n : nat, P (constr2 X n)) ->
       (forall m : mytype X, P m -> forall n : nat, P (constr3 X m n)) ->
       forall m : mytype X, P m
*)


(*
      foo_ind :
        ∀(X Y : Type) (P : foo X Y → Prop),
             (∀x : X, P (bar X Y x)) →
             (∀y : Y, P (baz X Y y)) →
             (∀f1 : nat → foo X Y,
               (∀n : nat, P (f1 n)) → P (quux X Y f1)) →
             ∀f2 : foo X Y, P f2
*)
Inductive foo (X : Type) (Y : Type) :=
  | bar : X -> foo X Y
  | baz : Y -> foo X Y
  | quux : (nat -> foo X Y) -> foo X Y.
Check foo_ind.

(*
foo_ind
     : forall (X Y : Type) (P : foo X Y -> Prop),
       (forall x : X, P (bar X Y x)) ->
       (forall y : Y, P (baz X Y y)) ->
       (forall f1 : nat -> foo X Y,
        (forall n : nat, P (f1 n)) -> P (quux X Y f1)) ->
       forall f2 : foo X Y, P f2
*)

Inductive foo' (X:Type) : Type :=
  | C1 : list X -> foo' X -> foo' X
  | C2 : foo' X.

(*
foo'_ind :
  forall (X : Type) (P : foo' X -> Prop),
    (forall (l : list X) (f : foo' X), P f -> P (C1 X l f)) ->
    P (C2 X) ->
    forall f : foo' X, P f.
*)
Check foo'_ind.
(*
foo'_ind
     : forall (X : Type) (P : foo' X -> Prop),
       (forall (l : list X) (f : foo' X), P f -> P (C1 X l f)) ->
       P (C2 X) -> forall f1 : foo' X, P f1
*)


Theorem plus_assoc' :
  forall n m p, n + (m + p) = n + m + p.
Proof.
  intros.
  induction n as [| n'].
  reflexivity.
  simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_comm' : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  intros. rewrite plus_0_r. reflexivity.
  intros. simpl. rewrite -> IHn'.
  rewrite plus_n_Sm. reflexivity.
Qed.

Definition P_pa : nat -> nat -> nat -> Prop :=
  fun n => fun m p => n + (m + p) = n + m + p.

Theorem plus_assoc'' :
  forall m, forall p, forall n, P_pa n m p.
Proof.
  intros m p.
  apply nat_ind. reflexivity.
  unfold P_pa. intros. simpl. rewrite H. reflexivity.
Qed.

Definition P_pc (n : nat) (m : nat) : Prop :=
  n + m = m + n.

Theorem plus_comm'' :
  forall m n, P_pc n m.
Proof.
  intro. apply nat_ind.
  unfold P_pc. rewrite plus_0_r. reflexivity.
  unfold P_pc. intros. simpl. rewrite -> H.
  rewrite plus_n_Sm. reflexivity.
Qed.

(*
Inductive beautiful : nat -> Prop :=
| b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum : forall m n : nat,
            beautiful m -> beautiful n ->
            beautiful (m + n).
*)

Lemma one_not_beautiful_FAILED: ~ beautiful 1.
Proof.
  intro H.
  remember 1.
  induction H; inversion Heqn.
  destruct m.
    destruct n.
      inversion H2.
      simpl in H2. apply IHbeautiful2 in H2. inversion H2.
    destruct n.
      rewrite plus_0_r in H2. apply IHbeautiful1 in H2. inversion H2.
      inversion H2. rewrite NPeano.Nat.add_succ_r in H3. inversion H3.
Qed.
