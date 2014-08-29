
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