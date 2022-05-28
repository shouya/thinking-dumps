Inductive paths {A} : A -> A -> Type :=
  idpath : forall x, paths x x.

Notation "x <~> y" := (paths x y) (at level 70).

#[local] Hint Resolve idpath : core.

Check paths_ind.

Definition ind :
  forall A
         (D : forall (x y : A), (x <~> y) -> Type),
         (forall (a : A), D a a (idpath a)) ->
         forall (x y : A) (p : (x <~> y)), D x y p.
Proof.
  intros.
  induction p.
  apply X.
Defined.

Definition inv: forall {A} {x y : A}, (x <~> y) -> (y <~> x).
Proof.
  intros.
  induction X.
  apply idpath.
Defined.

Definition inv_inv : forall {A} {x y : A} {p : x <~> y}, inv (inv p) <~> p.
Proof.
  intros.
  induction p.
  unfold inv. simpl.
  apply idpath.
Defined.

Definition concat: forall {A} {x y z : A}, (x <~> y) -> (y <~> z) -> (x <~> z) :=
  fun A x y z xy yz =>
    ind A
        (fun x y p => forall (z: A), (y <~> z) -> (x <~> z))
        (fun a =>
           ind A
               (fun a b _ => a <~> b)
               (fun w => idpath w)
               a
        )
        x y xy z yz
.

Print concat.

Notation "p @ q" := (concat p q) (at level 60).

Lemma concat_idpath : forall A {x: A}, (idpath x) @ (idpath x) = idpath x.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

(* It's very weird that concat defined in Proof mode will be
   un-expandable.  Proof. ... Qed. marks the definition
   opaque. Whereas Proof. ... Defined. marks the definition
   transparent.
  *)

Notation "! p" := (inv p) (at level 50).

Definition idpath_left_unit : forall A (x y : A) (p : x <~> y), (idpath x @ p) <~> p.
Proof.
  intros.
  induction p.
  auto.
Qed.

Definition idpath_right_unit : forall A (x y : A) (p : x <~> y), (p @ idpath y) <~> p.
Proof.
  intros.
  induction p.
  auto.
Qed.

Require Import Coq.Init.Nat.

Inductive pointed A (a : A) : Type :=
| point_intro : pointed A a.

#[local] Hint Resolve point_intro : core.

Definition loop A (a : A) : Type := (pointed (a <~> a) (idpath a)).

Print loop.

Definition loop_concat A (a : A) (x : loop A a) (y : loop A a) : loop A a.
Proof. trivial. Qed.

Print loop_concat.

Definition loop2 A (a : A) : Type := loop (loop A a) (point_intro _ _).
Print loop2.

(*
loop2 =
fun (A : Type) (a : A) => loop (loop A a) (point_intro (a <~> a) (idpath a))
     : forall A : Type, A -> Type
 *)

Definition ap {A B} (f : A -> B) {x y : A} : (x <~> y) -> (f x <~> f y).
Proof. intros. induction X. auto. Defined.

Lemma ap_functor_hor_comp :
  forall A B (f : A -> B) (x y z : A) (p : x <~> y) (q : y <~> z),
         ap f (p @ q) = (ap f p) @ (ap f q).
Proof. intros. induction p. induction q. simpl. reflexivity. Qed.

Lemma ap_functor_inv :
  forall A B (f : A -> B) (x y : A) (p : x <~> y),
         ap f (! p) = ! (ap f p).
Proof. intros. induction p. simpl. reflexivity. Qed.

Require Import Coq.Program.Basics.

Lemma ap_functor_vert_comp :
  forall A B C (f : A -> B) (g : B -> C) (x y : A) (p : x <~> y),
           ap (compose g f) p = ap g (ap f p).
Proof. intros. induction p. simpl. reflexivity. Qed.

Lemma ap_functor_id :
  forall A (x y : A) (p : x <~> y), ap id p = p.
Proof. intros. induction p. simpl. reflexivity. Qed.

Definition transport {A} (P : A -> Type) {x y : A} (p : x <~> y) : P x -> P y.
Proof.
  intros.
  induction p.
  apply X.
Defined.


(* For sigT type *)
Require Import Coq.Init.Specif.

Lemma test_sig : sigT (fun t => t).
Proof.
  exists nat. apply 1.
Qed.

Lemma test_sig2 : {a & a}.
Proof.
  exists nat. apply 1.
Qed.

Print test_sig.
Print existT.
(*
Inductive sigT (A : Type) (P : A -> Type) : Type :=
    existT : forall x : A, P x -> {x : A & P x}.

Arguments sigT [A]%type_scope P%type_scope
Arguments existT [A]%type_scope P%function_scope x _
 *)

Lemma path_lift {A} (P : A -> Type) {x y : A}
      (u: P x) (p : x <~> y) :
         (existT P x u) <~> (existT P y (transport P p u)).
Proof. induction p. simpl. constructor. Qed.

Check path_lift.

(* dependent map *)
Definition apd {A} (P : A -> Type) (f : forall (x:A), P x) :
  forall {x y : A} (p : x <~> y), transport P p (f x) <~> f y.
Proof. intros. induction p. auto. Defined.

Print apd.

Definition ConstTF A {B} : A -> Type := (fun _a => B).

Definition transport_const : forall {A B} {x y : A} (p : x <~> y) (b : B),
         (transport (ConstTF A) p b) <~> b.
Proof. intros. induction p. simpl. apply idpath. Defined.

Lemma apd_eq_transport_const :
  forall {A B} {x y : A} (f : A -> B) (p : x <~> y) (P := ConstTF A),
         apd P f p <~> (transport_const p (f x)) @ (ap f p).
Proof. intros. unfold P. induction p. simpl. auto. Defined.
