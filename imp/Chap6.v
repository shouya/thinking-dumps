
(* CHAPTER VI: SIMILARITY OF RELATIONS *)

Require Export Chap5.


Definition heterogeneous_relation {X} {Y} := X -> Y -> Prop.

(* The relation in stdlib is what we called 'homogeneous relation',
   because the domain and the converse domain has the same logic type. *)
Definition homogenenous_relation {X} := X -> X -> Prop.
Definition homogenenous_relation' := relation.

Definition field {X} (R : relation X) (x : X) := domain R x \/ converse_domain R x.


(* We may define two relations P and Q as “similar,” or as having
“likeness,” when
there is a (1)one-one relation S
(2)whose domain is the field of P and
(3)whose converse domain is the field of Q
, and which is such that,
(4)if one term(a) has the relation P to another(b), the correlate of
the one(S a) has the relation Q to the correlate of the other(S b), and
  (* forall a b, P a b -> Q (S a) (S b) *)
(5)vice versa.
  (* forall a b, Q (S a) (S b) -> P a b *)
*)

Inductive similar {X} (P : relation X) (Q : relation X) : Prop :=
| similar_intro : forall (S : relation X),
                    one_one S ->
                    (forall x, field P x -> domain S x) ->
                    (forall x y z w, P x y -> S x z -> S y w -> Q z w) ->
                    (forall x y z w, Q z w -> S x z -> S y w -> P x y) ->
                    similar P Q.

(* This theorem is not mentioned on the book but I want to prove it *)
Theorem one_one_converse_one_one :
  forall {X} (P : relation X), one_one P ->
                               one_one (converse P).
Proof.
  intros.
  inversion H. unfold many_one in H0. unfold one_many in H1.
  unfold one_one. unfold many_one. unfold one_many.
  split; intros; inversion H2; inversion H3; subst.
  apply H1 with y x y' in H4; assumption.
  apply H0 with y x x' in H7; assumption.
Qed.

(*
A relation S is said to be a “correlator” or an “ordinal correlator”
of two relations P and Q if S is one-one, has the field of Q for its
converse domain, and is such that P is the relative product of S and Q
and the converse of S.
*)

Inductive correlator {X} (P Q : relation X) : relation X -> Prop :=
  | correlator_intro :
      forall (S : relation X),
        one_one S ->
        (forall x, field P x -> domain S x) ->
        (forall x y, relative_product (relative_product S Q) (converse S) x y -> P x y) ->
        correlator P Q S.

(* Two relations P and Q are said to be “similar,” or to have
“likeness,” when there is at least one correlator of P and Q.
*)
Inductive similar' {X} (P Q : relation X) : Prop :=
  | similar'_intro : forall S, correlator P Q S -> similar' P Q.

(* NOTE: this defintion is taken from Russel's book
   Principles of Mathematics rather than Introduction to Mathematical Philosophy
 ===============================================================================
 Two relations P, Q are like when there is a one-one relation S such
 that the domain of S is the field of P, and Q = S̆PS.
   ** I don't know about this notation 'S̆PS', but I guess
      it's the relative product of the converse of S, P, and S.
*)

(* Proving these two definition are equivalent *)
Theorem similar_eqv1 :
  forall {X} (P Q : relation X), similar P Q -> similar' P Q.
Proof.
  intros.
  inversion H. apply similar'_intro with S.
  constructor; try assumption; intros.

  inversion H4; clear H4.
  inversion H5; clear H5.
  inversion H6; clear H6.
  subst.

  rename y1 into z.
  rename y0 into w.
  specialize H2 with x y z w.
  specialize H3 with x y z w.

  apply H3; assumption.
Qed.

Theorem similar_eqv2 :
  forall {X} (P Q : relation X), similar' P Q -> similar P Q.
Proof.
  intros.
  inversion H. inversion H0. subst.
  apply similar_intro with S; try assumption; intros.
  specialize H3 with x y.
  (* Stuck... *)
  (* apply rp0 with (relative_product S Q) (converse S) x y w in H4. *)