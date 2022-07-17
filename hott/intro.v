Inductive paths {A} : A -> A -> Type :=
  idpath : forall x, paths x x.

Notation "x == y" := (paths x y) (at level 70).

#[local] Hint Resolve idpath : core.

Check paths_ind.

Definition ind :
  forall A
         (D : forall (x y : A), (x == y) -> Type),
         (forall (a : A), D a a (idpath a)) ->
         forall (x y : A) (p : (x == y)), D x y p.
Proof.
  intros.
  induction p.
  apply X.
Defined.

Lemma paths_refl : forall {A} {x: A}, x == x.
Proof. auto. Qed.

Lemma paths_symm : forall {A} {x y : A}, x == y -> y == x.
Proof. intros. induction X. auto. Qed.

Lemma paths_trans : forall {A} {x y z : A}, x == y -> y == z -> x == z.
Proof. intros. induction X. auto. Qed.

Definition inv: forall {A} {x y : A}, (x == y) -> (y == x).
Proof.
  intros.
  induction X.
  apply idpath.
Defined.

Definition inv_inv : forall {A} {x y : A} (p : x == y), inv (inv p) == p.
Proof.
  intros.
  induction p.
  unfold inv. simpl.
  apply idpath.
Defined.

Definition concat: forall {A} {x y z : A}, (x == y) -> (y == z) -> (x == z).
Proof. intros. induction X. apply X0. Defined.


Definition concat': forall {A} {x y z : A}, (x == y) -> (y == z) -> (x == z) :=
  fun A x y z xy yz =>
    ind A
        (fun x y p => forall (z: A), (y == z) -> (x == z))
        (fun a =>
           ind A
               (fun a b _ => a == b)
               (fun w => idpath w)
               a
        )
        x y xy z yz
.

Print concat.

Notation "p @ q" := (concat p q) (at level 60).

Lemma concat_idpath : forall {A} {x: A}, (idpath x) @ (idpath x) = idpath x.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma concat_inv : forall {A} {x y : A} {p : x == y}, p @ inv p = idpath x.
Proof.
  intros.
  induction p. simpl. reflexivity.
Qed.

Lemma concat_inv2 : forall {A} {x y : A} {p : x == y}, inv p @ p = idpath y.
Proof.
  intros.
  induction p. simpl. reflexivity.
Qed.

Lemma concat_assoc : forall {A} (x y z w : A)
                       (p : x == y) (q : y == z) (r : z == w),
         (p @ q) @ r = p @ (q @ r).
Proof.
  intros.
  induction p. induction q. induction r. simpl. reflexivity.
Qed.

Notation "! p" := (inv p) (at level 50).

Definition idpath_left_unit : forall {A} {x y : A} (p : x == y), (idpath x @ p) == p.
Proof.
  intros.
  induction p.
  auto.
Defined.

Definition idpath_right_unit : forall {A} {x y : A} (p : x == y), p == (p @ idpath y).
Proof.
  intros.
  induction p.
  auto.
Defined.

Require Import Coq.Init.Nat.

Inductive pointed A (a : A) : Type :=
| point_intro : pointed A a.

#[local] Hint Resolve point_intro : core.

Definition loop A (a : A) : Type := (pointed (a == a) (idpath a)).

Print loop.

Definition loop_concat A (a : A) (x : loop A a) (y : loop A a) : loop A a.
Proof. trivial. Qed.

Print loop_concat.

Definition loop2 A (a : A) : Type := loop (loop A a) (point_intro _ _).
Print loop2.

Lemma concat_same_right : forall {A} {x y z: A} (p q : x == y) (r : y == z),
         p == q -> (p @ r) == (q @ r).
Proof. intros. induction X. auto. Qed.

Lemma concat_same_left : forall {A} {x y z: A} (p : x == y) (r s : y == z),
         r == s -> (p @ r) == (p @ s).
Proof. intros. induction X. auto. Qed.


Definition whisker_right {A} {a b c : A} {p q : a == b}
           (alpha : p == q) (r : b == c) : (p @ r) == (q @ r).
Proof. intros. simpl. induction r. induction alpha. auto. Defined.

Definition whisker_left {A} {a b c : A} {r s : b == c}
           (p : a == b) (beta : r == s) : (p @ r) == (p @ s).
Proof. intros. simpl. induction p. induction beta. auto. Defined.

Lemma whisker_right_idpath : forall {A} {a b: A} {p q : a == b} (alpha : p == q),
         whisker_right alpha (idpath b) =
           (! idpath_right_unit p) @ alpha @ (idpath_right_unit q).
Proof. intros. induction p. induction alpha. induction x0. simpl. auto. Qed.

Lemma whisker_left_idpath : forall A {b c : A} {r s : b == c} (beta : r == s),
         whisker_left (idpath b) beta =
           (idpath_left_unit r) @ beta @ (! idpath_left_unit s).
Proof. intros. induction r. induction beta. induction x0. simpl. auto. Qed.

(*
loop2 =
fun (A : Type) (a : A) => loop (loop A a) (point_intro (a == a) (idpath a))
     : forall A : Type, A -> Type
 *)

Definition ap {A B} (f : A -> B) {x y : A} : (x == y) -> (f x == f y).
Proof. intros. induction X. auto. Defined.

Lemma ap_functor_hor_comp :
  forall A B (f : A -> B) (x y z : A) (p : x == y) (q : y == z),
         ap f (p @ q) = (ap f p) @ (ap f q).
Proof. intros. induction p. induction q. simpl. reflexivity. Qed.

Lemma ap_functor_inv :
  forall A B (f : A -> B) (x y : A) (p : x == y),
         ap f (! p) = ! (ap f p).
Proof. intros. induction p. simpl. reflexivity. Qed.

Require Import Coq.Program.Basics.
Open Scope program_scope.

Lemma ap_functor_vert_comp :
  forall A B C (f : A -> B) (g : B -> C) (x y : A) (p : x == y),
           ap (g ∘ f) p = ap g (ap f p).
Proof. intros. induction p. simpl. reflexivity. Qed.

Lemma ap_functor_id :
  forall A (x y : A) (p : x == y), ap id p = p.
Proof. intros. induction p. simpl. reflexivity. Qed.

Definition transport {A} (P : A -> Type) {x y : A} (p : x == y) : P x -> P y.
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

Definition path_lift {A} (P : A -> Type) {x y : A}
      (u: P x) (p : x == y) :
         (existT P x u) == (existT P y (transport P p u)).
Proof. induction p. simpl. constructor. Defined.

Check path_lift.

(* dependent map *)
Definition apd {A} (P : A -> Type) (f : forall (x:A), P x) :
  forall {x y : A} (p : x == y), transport P p (f x) == f y.
Proof. intros. induction p. auto. Defined.

Print apd.

Definition ConstTF A {B} : A -> Type := (fun _a => B).

Definition transport_const : forall {A B} {x y : A} (p : x == y) (b : B),
         (transport (ConstTF A) p b) == b.
Proof. intros. induction p. simpl. apply idpath. Defined.

Lemma apd_eq_transport_const :
  forall {A B} {x y : A} (f : A -> B) (p : x == y) (P := ConstTF A),
         apd P f p == (transport_const p (f x)) @ (ap f p).
Proof. intros. unfold P. induction p. simpl. auto. Defined.

Lemma transport_concat :
  forall A (P : A -> Type) (x y z : A) (p : x == y) (q : y == z) (u : P x),
         transport P q (transport P p u) == transport P (p @ q) u.
Proof.
  intros. induction p. induction q. simpl. auto.
Qed.

Lemma transport_comp :
  forall A B (x y : A) (f : A -> B) (P : B -> Type) (p : x == y) (u : P (f x)),
         transport (P ∘ f) p u == transport P (ap f p) u.
Proof. intros. induction p. auto. Qed.

Lemma transport_comp2 :
  forall A (x y : A) (P Q : A -> Type) (f : forall x, P x -> Q x) (p : x == y) (u : P x),
         transport Q p (f x u) == f y (transport P p u).
Proof. intros. induction p. auto. Qed.


(* homotopy between functions/paths *)

Definition homotopy {A} {P : A -> Type} (f g : forall (x : A), P x)
  := forall x, f x == g x.
Check homotopy.
(*
homotopy
     : (forall x : ?A, ?P x) -> (forall x : ?A, ?P x) -> Type
 *)

Notation "f ~ g" := (homotopy f g) (at level 40).

Lemma ap_idpath :
  forall {A B} {x : A} (f : A -> B), ap f (idpath x) = idpath (f x).
Proof. intros. simpl. reflexivity. Qed.

Lemma homotopy_refl : forall {A B} {f : A -> B}, f ~ f.
Proof. intros. intro. auto. Qed.

Lemma homotopy_symm : forall {A B} {f g : A -> B}, f ~ g -> g ~ f.
Proof. intros. intro. pose proof (X x). apply (inv X0).
Defined.

Lemma homotopy_trans : forall {A B} {f g h : A -> B}, f ~ g -> g ~ h -> f ~ h.
Proof. intros. intro. pose proof (X x). pose proof (X0 x).
       induction X1. induction X2. auto. Qed.

#[local] Hint Resolve homotopy_refl : core.
#[local] Hint Resolve homotopy_symm : core.
#[local] Hint Resolve homotopy_trans : core.

Lemma homotopy_natural :
  forall {A B} (f g : A -> B) (H : f ~ g) (x y : A) (p : x == y),
         H x @ ap g p == ap f p @ H y.
Proof.
  intros. induction p.
  rewrite ap_idpath. rewrite ap_idpath. induction (H x).
  auto.
Qed.

#[local] Hint Unfold id : core.

Lemma paths_eq : forall {A} {x y : A} (p : x == y), x = y.
Proof. intros. induction p. auto. Qed.

Lemma ap_id :
  forall {A} {x y : A} (p : x == y), ap id p = p.
Proof. intros. induction p. simpl. reflexivity. Qed.


Lemma homotopy_comp_id :
  forall A (f : A -> A) (H : f ~ id) (x : A), H (f x) == ap f (H x).
Proof.
  intros.
  pose (Hinv := homotopy_symm H).
  assert (Hcompinv : H x @ Hinv x = idpath (f x)).
  { unfold Hinv. unfold homotopy_symm. apply concat_inv. }
  pose proof homotopy_natural _ _ H (f x) x (H x).
  rewrite ap_id in X.

  apply (fun X => whisker_right X (Hinv x)) in X.
  (* Set Printing All. *)
  (* This line is necessary, otherwise the left hand side of the paths
     contains dummy ids than H x @ Hinv x and cannot rewrite
     therefore. Weirdly the id around some terms wasn't printed out unless
     I Set Printing All.
   *)
  unfold id in X.
  unfold id in Hcompinv.
  rewrite concat_assoc in X.
  rewrite concat_assoc in X.
  repeat rewrite Hcompinv in X.
  rewrite <- (paths_eq (idpath_right_unit _)) in X.
  rewrite <- (paths_eq (idpath_right_unit _)) in X.
  apply X.
  (* Phew! That's a tough proof! *)
Qed.

Check paths.
Check @pair.

(* quasi-inversion *)
Class QInv {A B} (f : A -> B) :=
  { qinv_g : B -> A
  ; qinv_fg : f ∘ qinv_g ~ id
  ; qinv_gf : qinv_g ∘ f ~ id
  }.

Check QInv.

Example qinv_id : forall A, QInv (@id A).
Proof.
  intro.
  split with (qinv_g := id).
  - intro. auto.
  - intro. auto.
Qed.

Example qinv_invpath1 : forall {A} {x y z : A} {p : x == y},
         QInv (fun (q : y == z) => p @ q).
(* y == z -> x == z *)
Proof.
  intros.
  split with (qinv_g := (fun (q : x == z) => !p @ q)).
  - induction p. intro. unfold compose. simpl.
    auto.

  - induction p. intro. unfold compose. simpl.
    auto.
Qed.

Example qinv_invpath2 : forall {A} {x y z : A} {p : x == y},
         QInv (fun (q : z == x) => q @ p).
(* z == x -> z == y *)
Proof.
  intros.
  split with (qinv_g := (fun q : z == y => q @ !p)).
  - induction p. intro. unfold compose. simpl.
    rewrite <- (paths_eq (idpath_right_unit _)).
    rewrite <- (paths_eq (idpath_right_unit _)).
    auto.

  - induction p. intro. unfold compose. simpl.
    rewrite <- (paths_eq (idpath_right_unit _)).
    rewrite <- (paths_eq (idpath_right_unit _)).
    auto.
Qed.


Example qinv_transport : forall {A} {x y : A} {p : x == y} {P : A -> Type},
         QInv (fun px => transport P p px).
(* P x -> P y *)
Proof.
  intros.
  split with (qinv_g := (fun py => transport P (inv p) py)).
  - induction p. simpl. unfold compose. intro. auto.
  - induction p. simpl. unfold compose. intro. auto.
Qed.


Class Eqv {A B} (f : A -> B) :=
  { eqv_g : B -> A
  ; eqv_fg : f ∘ eqv_g ~ id
  ; eqv_h : B -> A
  ; eqv_hf : eqv_h ∘ f ~ id
  }.

(* Definition isequiv {A B} (f : A -> B) : Type := *)
(*   {g : B -> A & f ∘ g ~ id} * {h : B -> A & h ∘ f ~ id}. *)

Lemma qinv_implies_isequiv : forall {A B} (f : A -> B), QInv f -> Eqv f.
Proof.
  intros.
  destruct X as [g alpha beta].
  esplit.
  - apply alpha.
  - apply beta.
Defined.


Lemma isequiv_implies_qinv : forall {A B} (f : A -> B), Eqv f -> QInv f.
Proof.
  intros.
  destruct X as [g alpha h beta].
  esplit.
  - apply alpha.
  - intro.
    eapply concat.
    + eapply concat.
      * apply inv.
        apply beta.
      * eapply (ap h).
        apply alpha.
    + unfold id at 1.
      apply beta.
Defined.

Lemma isequiv_uniq_attempt : forall {A B} (f : A -> B) (e1 e2 : Eqv f),
         e1 == e2.
  (* It requires identifying the identity types for cartesian product
  and dependent pair types, so we'll prove it later *)
Admitted.

(* an equivalence between A and B is a function f plus a proof isequiv f *)
Definition Equivalence A B := {f : A -> B & Eqv f}.
Notation "A ~= B" := (Equivalence A B) (no associativity, at level 40).

Definition eqv_to_fn A B (f : A ~= B) : A -> B := projT1 f.
Coercion eqv_to_fn : Equivalence >-> Funclass.

(* Set Printing Coercion eqv_to_fn. *)
Print Graph.

Definition type_equiv_refl : forall A, A ~= A.
Proof.
  intros.
  exists id. esplit.
  - intro. apply idpath.
  - intro. apply idpath.
Defined.

Definition type_equiv_inv : forall A B, A ~= B -> B ~= A.
Proof.
  intros.
  destruct X.
  apply isequiv_implies_qinv in e.
  destruct e.
  exists qinv_g0. split with (1 := qinv_gf0) (2 := qinv_fg0).
Defined.

Definition type_equiv_comp : forall {A B C} (f : A ~= B) (g : B ~= C), A ~= C.
Proof.
  intros.
  destruct f, g.
  apply isequiv_implies_qinv in e, e0.
  destruct e, e0.
  exists (x0 ∘ x).
  split with (eqv_g := qinv_g0 ∘ qinv_g1) (eqv_h := qinv_g0 ∘ qinv_g1).
  - intro. eapply concat.
    + eapply (ap x0). apply qinv_fg0.
    + unfold id. apply qinv_fg1.
  - intro. eapply concat.
    + eapply (ap qinv_g0). apply qinv_gf1.
    + unfold id. apply qinv_gf0.
Defined.

Lemma product_implication :  forall {A B} {x x' : A} {y y' : B},
         ((x, y) == (x', y')) -> ((x == x') * (y == y')).
Proof.
  intros.
  split.
  - apply (ap fst) in X. apply X.
  - apply (ap snd) in X. apply X.
Defined.

Lemma product_implication_converse :  forall {A B} {x x' : A} {y y' : B},
         ((x == x') * (y == y')) -> ((x, y) == (x', y')).
Proof.
  intros.
  destruct X. induction p, p0. apply idpath.
Defined.

Lemma product_equiv : forall {A B} {x x' : A} {y y' : B},
         ((x, y) == (x', y')) ~= ((x == x') * (y == y')).
Proof.
  intros.
  exists product_implication.
  apply qinv_implies_isequiv.
  exists product_implication_converse.
  - intro.
    destruct x0. induction p, p0. auto.
  - intro.
    unfold product_implication_converse, product_implication.
    (* I failed to prove this clause, so I decided to go on *)
Admitted.

Lemma transport_product :
  forall {A} (B C : A -> Type) (P := fun x => prod (B x) (C x)) {x y : A} (p : x == y)
    (b : B x) (c : C x),
         transport P p (b,c) == (transport B p b, transport C p c).
Proof.
  intros. induction p. simpl. apply idpath.
Defined.

Definition prod_elim {A B} {x y : A * B} :
  (x == y) -> ((fst x == fst y) * (snd x == snd y)).
Proof.
  intro. split; apply (ap _ X).
Defined.

Definition prod_intro {A B} {x y : A * B} :
  ((fst x == fst y) * (snd x == snd y)) -> (x == y).
Proof.
  intros.
  destruct X.
  induction x, y.
  simpl in p, p0.
  induction p, p0. auto.
Defined.

Lemma prod_equiv {A B} {x y : A * B} : Eqv (@prod_elim A B x y).
Proof.
  apply qinv_implies_isequiv.
  exists prod_intro.
  - intro. induction x0, x, y. simpl in a, b. induction a. induction b.
    unfold prod_elim, prod_intro, compose, id. simpl. auto.
  - intro. induction x0, x.
    unfold prod_elim, prod_intro, compose, id. simpl. auto.
Qed.

Lemma prod_pointwise_transport :
  forall {Z} (A B : Z -> Type) (P := fun x => prod (A x) (B x))
    {z w : Z} (p : z == w) (x : P z),
         transport P p x  == (transport A p (fst x), transport B p (snd x)).
Proof.
  intros. induction p. simpl. unfold P in x. induction x. simpl.
  apply idpath.
Defined.

Lemma prod_prop_uniq :
  forall {A B} {x y : A * B} (r : x == y), r == prod_intro (ap fst r, ap snd r).
Proof.
  intros.
  induction x, y.
  induction r. induction x. simpl. auto.
Qed.

Ltac myauto :=
  repeat intro;
  repeat (multimatch goal with
          | [H : (?x == ?y) |- _] =>
              lazymatch x with
              | ?a ?b => fail
              | _ => lazymatch y with
                    | ?a ?b => fail
                    | _ => induction H
                    end
              end
          | x : _ * _ |- _ => induction x
          | x : unit |- _ => induction x
          | x : {_ & _} |- _ => induction x
          | [ |- {_ : ?x == ?x & _}] => (exists (idpath _))
          end;
          simpl in *);
  auto.

Lemma prod_functor :
  forall A B A' B' {g : A -> A'} {h : B -> B'}
    (f : (A * B -> A' * B') := fun x => (g (fst x), h (snd x)))
    {x y : A * B}
    (p : fst x == fst y) (q : snd x == snd y),
         @paths (f x == f y)
                (ap f (prod_intro (p, q)))
                (* this type hint is necessary for coq to figure out
                the two types are equal *)
                (prod_intro (ap g p : fst (f _) == fst (f _), ap h q)).
Proof. myauto. Qed.

Definition sigma_proj1 {A} {P : A -> Type}
           {w w' : {x : A & P x}} (p : w == w') : projT1 w == projT1 w'.
Proof. myauto. Defined.


Definition sigma_proj2 {A} {P : A -> Type}
           {w w' : {x : A & P x}} (p : w == w') :
  transport _ (sigma_proj1 p) (projT2 w) == projT2 w'.
Proof. myauto. Qed.

(*
From the book:

Remark 2.7.1. Note that if we have x : A and u, v : P(x) such that (x, u) = (x, v), it does not follow that u = v. All we can conclude is that there exists p : x = x such that p∗(u) = v.
 *)

Import SigTNotations.
(*
Imported for syntaxes:

- (a; b)
- a.1
- b.2
 *)


Lemma sigma_elim : forall {A} {P: A -> Type} {w w' : {x : A & P x}},
         (w == w') -> {p : w.1 == w'.1 & transport _ p (w.2) == w'.2 }.
Proof. myauto. Defined.

Lemma sigma_intro : forall {A} {P: A -> Type} {w w' : {x : A & P x}},
         {p : w.1 == w'.1 & transport _ p (w.2) == w'.2 } -> (w == w').
Proof. myauto. Defined.

Lemma sigma_equiv : forall {A} {P : A -> Type} {w w' : {x : A & P x}},
         Eqv (@sigma_elim A P w w').
Proof.
  intros.
  split with (eqv_g := sigma_intro) (eqv_h := sigma_intro).
  - myauto.
  - myauto.
Qed.

Lemma sigma_prop_uniq : forall {A P} (z : {x : A & P x}), z == (z.1 ; z.2).
Proof. intros. myauto. Qed.

Remark sigma_proj2_path : forall {A} {P : A -> Type} {x : A} {u v : P x},
         (x ; u) == (x ; v) ->
         {p : x == x & transport _ p u == v}.
Proof.
  intros.
  apply sigma_elim in X.
  induction X. simpl in *.
  exists x0. auto.
Qed.

Definition sigma_path_lift : forall {A} {P : A -> Type} {x y : A}
                          (p : x == y) (u : P x),
         (x; u) == (y; transport P p u).
Proof. intros. apply path_lift. Defined.

Definition sigma_intro_transport {A P} {x y : A} (p : x == y) (u : P x) :
  (x ; u) == (y ; transport P p u) :=
  sigma_intro (w := (x ; u)) (w' := (y ; transport P p u))
              (p; idpath (transport P p u)).

Lemma sigma_transport : forall {A P} {Q : {x : A & P x} -> Type}
                      {x y : A}
                      (p : x == y)
                      (w : {u : P x & Q (x ; u)}),
           (transport (fun x => {u : P x & Q (x ; u)}) p w)
           ==
           (transport P p w.1 ;
            transport Q (sigma_intro_transport p w.1) w.2).
Proof. myauto. Qed.

Definition sigma_functor_helper :
  forall {A B A' B'} {g : A -> A'} {h : forall x x', B x -> B' x'}
    (f : {x:A & B x} -> {x:A' & B' x} := fun w => (g w.1 ; h w.1 (g w.1) w.2))
    {w w' : {x:A & B x}}
    (p : w.1 == w'.1) (q : transport B p w.2 == w'.2),
         transport B' (ap g p) (f w).2 == (f w').2.
Proof. myauto. Defined.

Print sigma_functor_helper.

Lemma sigma_functor :
  forall A B A' B' {g : A -> A'} {h : forall x x', B x -> B' x'}
    (f : {x:A & B x} -> {x:A' & B' x} := fun w => (g w.1 ; h w.1 (g w.1) w.2))
    {w w' : {x:A & B x}}
    (p : w.1 == w'.1) (q : transport B p w.2 == w'.2),
         @paths (f w == f w')
                (ap f (sigma_intro (p ; q)))
                (sigma_intro (ap g p : (f w).1 == (f w').1 ;
                              sigma_functor_helper p q)).
Proof. intros. myauto. Qed.

(* Unit type *)
Theorem unit_equality_eqv_unit : forall {x y : unit}, (x == y) ~= unit.
Proof.
  intro. induction x. intro y. induction y.
  exists (const tt). split with (eqv_h := const (idpath _)) (eqv_g := const (idpath _)).
  - intro. unfold const, compose. induction x. auto.
  - intro. unfold const, compose. unfold id. auto.
    (* We are stuck here to prove idpath tt == x where x : tt == tt *)
  Restart.
  intros.
  exists (const tt).
  esplit.
  - induction x, y. intro. induction x. auto.
  - intro. induction x0. induction x. unfold compose, const, id.
    Unshelve. 2: { induction x, y. auto. }
    Unshelve. 2: { induction x, y. auto. }
    simpl. auto.
Defined.

(* if you know x == y, then you know nothing. it is a tautology. *)
Lemma unit_intro : forall {x y : unit}, x == y -> unit.
Proof. intros. apply tt. Defined.

Lemma unit_elim : forall {x y : unit}, unit -> x == y.
Proof. myauto. Defined.

Lemma unit_equiv : forall {x y}, Eqv (@unit_intro x y).
Proof.
  intros.
  split with (eqv_h := unit_elim) (eqv_g := unit_elim).
  - myauto.
  - myauto.
Qed.

(* the same as transport_const *)
Lemma unit_transport : forall {B} {x y : unit} {p : x == y} {u: B},
         transport (ConstTF unit) p u == u.
Proof. myauto. Qed.


(* function extensionality *)
Axiom funext : forall {A B} (f g : forall (x : A), B x),
         (f == g) ~= (forall (x : A), f x == g x).

Definition happly : forall {A B} (f g : forall (x : A), B x),
         (f == g) -> (forall (x : A), f x == g x).
Proof. myauto. Qed.

Definition pi_elim {A B} := happly (A := A) (B := B).

Lemma pi_intro {A B} {f g : forall x, B x} : (forall (x : A), f x == g x) -> f == g.
Proof.
  intro. pose proof funext f g. destruct X0. destruct e.
  auto.
Defined.

Definition pi_func_family {T} A B := fun (x : T) => (A x) -> (B x).

Definition pi_func_transport : forall {T} {A B : T -> Type} {x y : T} (p : x == y)
                            (f : pi_func_family A B x),
         transport (pi_func_family A B) p f ==
         fun x => transport B p (f (transport A (inv p) x)).
Proof. myauto. Qed.

Definition pi_family {T} A B : T -> Type :=
  fun (x : T) => (forall a: A x, B x a).
Check pi_family.
(* forall A : ?T -> Type, (forall x : ?T, A x -> Type) -> ?T -> Type *)

Definition pi_sigma_family {T A} (B : forall x: T, A x -> Type) : {x: T & A x} -> Type :=
  fun w => B w.1 w.2.

Definition pi_transport : forall {T} {A : T -> Type} {B : forall x: T, A x -> Type}
                            {x1 x2 : T} {f : forall a: A x1, B x1 a} (p : x1 == x2)
                            (a : A x2),
         transport (pi_family A B) p f a ==
         transport (fun w => B w.1 w.2)
                   (! (sigma_path_lift (! p) a))
                   (f (transport A (inv p) a)).
Proof. myauto. Qed.

Notation "p '⋆' '(' u ')'" := (transport _ p u)
                         (no associativity, at level 50).

Definition func_transport_equiv :
  forall {T} {A B : T -> Type} {x y : T} (p : x == y)
    (f : A x -> B x) (g : A y -> B y),
         (transport (fun x => A x -> B x) p f == g) ~=
         (forall a, transport B p (f a) == g (transport A p a)).
Proof. intros. myauto. apply funext. Qed.


Definition pi_transport_equiv :
  forall {T} {A : T -> Type} {B : forall x, A x -> Type} {x1 x2 : T} (p : x1 == x2)
    (f : forall a, B x1 a) (g : forall a, B x2 a),
         (transport (fun x => forall a, B x a) p f == g)
           ~= (forall a, transport (fun w => B w.1 w.2)
                              (sigma_path_lift p a)
                              (f a)
                              ==
                              g (transport A p a)).
Proof. intros. myauto. apply funext. Qed.

Definition id2eqv {A B} : (A == B) -> (A ~= B).
Proof.
  intro. induction X.
  apply type_equiv_refl.
Defined.

Lemma qinv_equiv_equiv :
  forall A B (f : A -> B), Eqv (@qinv_implies_isequiv A B f).
Proof.
  intros.
  exists (eqv_g := isequiv_implies_qinv f) (eqv_h := isequiv_implies_qinv f).
  - intro. destruct x.
    unfold isequiv_implies_qinv, qinv_implies_isequiv, compose.


(* univalence axiom *)
Axiom ua : forall {A B}, QInv (@id2eqv A B).
Coercion qinv_g : QInv >-> Funclass.

Definition transport_equiv {A B : Type} (p : A == B) : A ~= B := id2eqv p.

Lemma type_intro {A B} : A ~= B -> A == B.
Proof. apply ua. Defined.

Lemma type_elim {A B} : A == B -> A ~= B.
Proof. apply id2eqv. Defined.

Definition ua_map : forall {A B}, A ~= B -> A == B.
Proof. intros. apply ua. apply X. Defined.

Lemma type_prop_uniq :
  forall {A B} (p : A == B) (e := @ua A B), e (id2eqv p) == p.
Proof.
  intros.
  destruct e.
  pose proof qinv_gf0 p.
  unfold id, compose, homotopy, ua_map in *.
  simpl. apply X.
  clear qinv_fg0 qinv_gf0.


  induction X.
  unfold ua_map.


Lemma type_prop_uniq :
  forall {A B} (p : A == B)
         (e := @ua A B),
         p == e (id2eqv p).
Proof.
  intros.
  destruct e.
  simpl.
  apply paths_symm.
  pose proof eqv_fg0 (id2eqv p).
  unfold id, compose, homotopy in *.

  pose proof eqv_hf0 p.
  induction X0.
  induction x. induction X. simpl.

  eapply whisker_right.
  eapply concat.
  - apply whis

  induction p as [X].
  pose proof eqv_hf0 (idpath X).
  pose proof eqv_fg0 (type_equiv_refl X).
  unfold homotopy, compose, id in *.
  simpl in *.
  apply paths_symm.
  induction X0.
  induction X1.



  pose proof isequiv_implies_qinv id2eqv e.
  destruct X.
  induction p. simpl.
  unfold homotopy, compose, id in eqv_hf0, eqv_fg0.
  pose proof eqv_hf0 (idpath x).
  apply paths_symm.




  (* apply ua_map. *)
  (*
     Unable to unify
     "@paths Type ?A ?B"
     with
     "@paths (@paths Type A B) p (eqv_to_fn (Equivalence A B) (@paths Type A B) (@ua A B) (@id2eqv A B p))".
   *)

Admitted.

Lemma type_prop_comp :forall {A B} (f : A ~= B) (x : A), id2eqv (ua f) x == f x.
Proof. Admitted.

Lemma ua_refl : forall A, (ua (type_equiv_refl A)) == idpath A.
Proof. Admitted.

Lemma ua_concat : forall A B C (f : A ~= B) (g : B ~= C),
         (ua f) @ (ua g) == ua (type_equiv_comp f g).
Proof.
  intros.
  destruct f as [f []], g as [g []].


Lemma transport_eq_transport_ap :
  forall A (B : A -> Type) (x y : A) (p : x == y) (u: B x),
         transport B p u == id2eqv (ap B p) u.
Proof. myauto. Defined.

Definition ua_refl : forall x, idpath x == ua (type_type_refl x).
Proof.
  intros.
