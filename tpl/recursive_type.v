Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

(* power set *)
Definition Pow T := T -> Prop.


Definition Subset {T} (s1 s2: Pow T) : Prop := forall t, s1 t -> s2 t.
Notation "s1 <: s2" := (Subset s1 s2)
                         (at level 30, no associativity).

Hint Unfold Subset.

Theorem subset_refl : forall T (s: Pow T), s <: s.
Proof.
  intros. unfold Subset. auto.
Qed.

Hint Resolve subset_refl.

Theorem subset_trans : forall T (a b c: Pow T), a <: b -> b <: c -> a <: c.
Proof.
  eauto.
Qed.

Hint Resolve subset_trans.

Definition Gen T := Pow T -> Pow T.
Hint Unfold Gen.

Definition monotone {T} (f: Gen T) : Prop := forall t1 t2, t1 <: t2 -> f t1 <: f t2.
Hint Unfold monotone.

Definition f_closed {T} (f: Gen T) (x: Pow T) := f x <: x.
Definition f_consistent {T} (f: Gen T) (x: Pow T) := x <: f x.
(* or [forall t, x t = f x t] because of prop_ext axiom. *)
Definition f_fixpoint {T} (f: Gen T) (x: Pow T) := forall t, x t <-> f x t.
Definition f_fixpoint' {T} (f: Gen T) (x: Pow T) := x = f x.

Hint Unfold f_closed.
Hint Unfold f_consistent.
Hint Unfold f_fixpoint.

Lemma fixpoint_ext : forall T (f: Gen T) x, f_fixpoint' f x  <-> f_fixpoint f x.
Proof.
  unfold f_fixpoint, f_fixpoint'.
  intros. split.
  - intros. split; intro. rewrite <- H. auto. rewrite H. auto.
  - intros.
    apply functional_extensionality. intro t.
    apply propositional_extensionality. specialize H with t. destruct H.
    split; intro; auto.
Qed.

(* let's give it a try *)
Theorem closed_consistent_implies_fixpoint : forall T (f: Gen T) (x: Pow T),
    f_closed f x /\ f_consistent f x -> f_fixpoint f x.
Proof.
  intros.
  destruct H. unfold f_closed in *. unfold f_consistent in *. unfold f_fixpoint.
  unfold Subset in *.
  intros.
  pose proof H t.
  pose proof H0 t.
  split; auto.
Qed.

Hint Resolve closed_consistent_implies_fixpoint.

Theorem fixpoint_implies_closed_consistent : forall T (f: Gen T) (x: Pow T),
    f_fixpoint f x -> f_closed f x /\ f_consistent f x.
Proof.
  intros.
  unfold f_closed in *. unfold f_consistent in *. unfold f_fixpoint in *.
  split; unfold Subset.
  - intros. apply H. auto.
  - intros. apply H. auto.
Qed.

Hint Resolve fixpoint_implies_closed_consistent.

Lemma f_consistent_recursive : forall T (f: Gen T) (x: Pow T),
    monotone f -> f_consistent f x -> f_consistent f (f x).
Proof.
  unfold f_consistent.
  intros.
  intro.
  intro.
  eapply H with x.
  apply H0. apply H1.
Qed.

Definition Intersect {T} (p: Pow T -> Prop) : Pow T :=
  (fun t => forall x, p x -> x t).

Definition Union {T} (p: Pow T -> Prop) : Pow T :=
  (fun t => exists x, p x /\ x t).

Hint Unfold Intersect. Hint Unfold Union.

Lemma Intersect_Subset : forall T {p: Pow T -> Prop} x, p x -> Intersect p <: x.
Proof.
  intros.
  unfold Intersect, Subset.
  intros.
  apply H0.
  apply H.
Qed.

Lemma Union_Subset : forall T {p: Pow T -> Prop} x, p x -> x <: Union p.
Proof. eauto. Qed.

Lemma Intersect_f_closed : forall T (f: Gen T),
    monotone f -> f_closed f (Intersect (f_closed f)).
Proof.
  intros.
  repeat intro.
  apply H1. eapply H.
  apply Intersect_Subset.
  apply H1. apply H0. Qed.

Lemma Union_f_consistent : forall T (f: Gen T),
    monotone f -> f_consistent f (Union (f_consistent f)).
Proof.
  intros.
  intro. intro.
  unfold Union in *. destruct H0. destruct H0.
  apply H with x. apply Union_Subset.
  apply H0. unfold f_consistent in H0. unfold Subset in H0.
  auto.
Qed.

Lemma knaster_tarski_1_fixpoint : forall T (f: Gen T),
    monotone f -> f_consistent f (Intersect (f_closed f)).
Proof.
  intros T f Hmono.
  unfold f_consistent.
  repeat intro.
  apply H.
  apply Hmono.
  clear H.
  repeat intro.
  apply H0.
  eapply Hmono.
  apply Intersect_Subset.
  apply H0. apply H.
Qed.

Lemma knaster_tarski_2_fixpoint : forall T (f: Gen T),
    monotone f -> f_closed f (Union (f_consistent f)).
Proof.
  intros T f Hmono.
  unfold f_closed.
  repeat intro.
  exists (f (Union (f_consistent f))).
  split.
  - repeat intro.
    apply f_consistent_recursive; auto.
    apply Union_f_consistent. auto.
  - apply H.
Qed.

Definition IsMin {T} (p: Pow T -> Prop) (x: Pow T) : Prop :=
  p x /\ forall x', p x' -> x <: x'.
Definition IsMax {T} (p: Pow T -> Prop) (x: Pow T) : Prop :=
  p x /\ forall x', p x' -> x' <: x.


Lemma knaster_tarski_1 : forall T (f: Gen T),
    monotone f -> IsMin (f_fixpoint f) (Intersect (f_closed f)).
Proof.
  intros.
  unfold IsMin.
  split.
  - apply closed_consistent_implies_fixpoint. split.
    + apply Intersect_f_closed; easy.
    + apply knaster_tarski_1_fixpoint; easy.
  - intros.
    apply Intersect_Subset.
    apply fixpoint_implies_closed_consistent in H0. easy.
Qed.

Lemma knaster_tarski_2 : forall T (f: Gen T),
    monotone f -> IsMax (f_fixpoint f) (Union (f_consistent f)).
Proof.
  intros.
  unfold IsMax.
  split.
  - apply closed_consistent_implies_fixpoint. split.
    + apply knaster_tarski_2_fixpoint; easy.
    + apply Union_f_consistent; easy.
  - intros.
    apply Union_Subset.
    apply fixpoint_implies_closed_consistent in H0. easy.
Qed.

Theorem knaster_tarski: forall T (f: Gen T),
    monotone f ->
    IsMin (f_fixpoint f) (Intersect (f_closed f)) /\
    IsMax (f_fixpoint f) (Union (f_consistent f)).
Proof.
  auto using knaster_tarski_1, knaster_tarski_2.
Qed.

Lemma min_unique : forall T (p: Pow T -> Prop) (x1 x2: Pow T),
    IsMin p x1 -> IsMin p x2 -> forall t, x1 t <-> x2 t.
Proof.
  unfold IsMin.
  unfold Subset.
  intros. destruct H; destruct H0.
  split; intro.
  - apply H1; eauto.
  - apply H2; eauto.
Qed.

Lemma max_unique : forall T (p: Pow T -> Prop) (x1 x2: Pow T),
    IsMax p x1 -> IsMax p x2 -> forall t, x1 t <-> x2 t.
Proof.
  unfold IsMax.
  unfold Subset.
  intros. destruct H; destruct H0.
  split; intro.
  - apply H2 with x1; eauto.
  - apply H1 with x2; eauto.
Qed.

Definition MinFix {T} (f: Gen T) : Pow T := Intersect (f_closed f).
Definition MaxFix {T} (f: Gen T) : Pow T := Union (f_consistent f).

Corollary principle_of_induction : forall T (f: Gen T) (x : Pow T),
    monotone f -> f_closed f x -> MinFix f <: x.
Proof.
  intros.
  apply Intersect_Subset.
  auto.
Qed.

Corollary principle_of_coinduction : forall T (f: Gen T) (x : Pow T),
    monotone f -> f_consistent f x -> x <: MaxFix f.
Proof.
  intros.
  apply Union_Subset.
  auto.
Qed.


Inductive TypeTreeNode := TNTop | TNArrow | TNPair.

(* a tree is a partial function from a list of branches to a node
   branch mapping: false => left, true => right
 *)
Definition Tree : Type := list bool -> option TypeTreeNode.

Definition is_some {T} (v: option T) : Prop := match v with
                                            | Some _ => True
                                            | _ => False
                                            end.

Import ListNotations.

(* Assert whether or not t is defined for input pi *)
Inductive tree_defined : Tree -> list bool -> Prop :=
| TD_nil : forall t, tree_defined t nil
(* i simplified the rule from the book to an equivalent form *)
| TD_split : forall t p1 s, tree_defined t (p1 ++ [s]) -> tree_defined t p1
| TD_arrow : forall t p1 s, t p1 = Some(TNArrow) -> tree_defined t (p1 ++ cons s nil)
| TD_pair  : forall t p1 s, t p1 = Some(TNPair) -> tree_defined t (p1 ++ cons s nil)
.

Definition tree_valid (t: Tree) : Prop :=
  forall path, tree_defined t path <-> is_some (t path).

(* I used an alternative definition for a tree to be finite:

  if a tree is undefined after a given path length, then this tree is finite.
 *)
Definition tree_finite (t: Tree): Prop :=
  exists n, forall p, n <= length p -> t p = None.

Definition tree_infinite (t: Tree): Prop := ~(tree_finite t).

(* The tree: (Top -> Top, Top) *)
Example tree1 : Tree :=
  fun p => match p with
        | [] => Some TNPair
        | [false] => Some TNArrow
        | [false; _] => Some TNTop
        | [true] => Some TNTop
        | _ => None
        end.

Inductive TypeTree : Type :=
| TTop : TypeTree
| TArrow (l r: TypeTree) : TypeTree
| TPair (l r: TypeTree) : TypeTree.

Fixpoint depth(t: TypeTree) : nat :=
  match t with
  | TTop => 1
  | TArrow a b => max (depth a) (depth b)
  | TPair a b => max (depth a) (depth b)
  end.

Definition FiniteTree (t: TypeTree) : Prop := exists d, depth t <= d.
Definition InfiniteTree (t: TypeTree) : Prop := ~(FiniteTree t).

Definition relation (T: Type) := Pow (T * T).

Definition TR {U} (R: relation U) : relation U :=
  fun pair => match pair with
           | (x, y) => exists z, R (x, z) /\ R (z, y)
           end.

Definition Transitive {U} (R: relation U) := TR R <: R.


Lemma fixpoint_transitive :
  forall U (F : relation U -> relation U),
    monotone F ->
    (forall R, TR(F(R)) <: F(TR(R))) ->
    Transitive (MaxFix F).
Proof.
  intros.
  intro. intro.
  assert (f_fixpoint' F (MaxFix F)).
  { apply fixpoint_ext.
    apply knaster_tarski_2.
    apply H.
  }
  assert (f_consistent F (TR (MaxFix F))).
  { intro. intro.
    apply H0.
    rewrite <- H2. apply H3.
  }
  apply principle_of_coinduction in H3; auto.
Qed.
