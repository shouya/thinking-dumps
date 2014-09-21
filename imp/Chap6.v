
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
| similar_intro : (exists S : relation X,
                    one_one S /\
                    (forall x, field P x <-> domain S x) /\
                    (forall x, field Q x <-> converse_domain S x) /\
                    (forall x y z w, P x y -> S x z -> S y w -> Q z w) /\
                    (forall x y z w, Q z w -> S x z -> S y w -> P x y)) ->
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
        (forall x, field P x <-> domain S x) ->
        (forall x, field Q x <-> converse_domain S x) ->
        (forall x y, relative_product (relative_product S Q) (converse S) x y -> P x y) ->
        correlator P Q S.

(* Two relations P and Q are said to be “similar,” or to have
“likeness,” when there is at least one correlator of P and Q.
*)
Inductive similar' {X} (P Q : relation X) : Prop :=
  | similar'_intro : (exists S, correlator P Q S) -> similar' P Q.

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
  inversion H as [HS].
  inversion HS as [S SProps].
  inversion SProps as [HS11 SProps'].
  inversion SProps' as [HSdomain SProps''].
  inversion SProps'' as [HScdomain SProps'''].
  inversion SProps''' as [HSPQ HSQP].

  clear SProps SProps' SProps'' SProps''' HS.

  constructor. exists S.
  constructor; try assumption.

  (*
Inductive relative_product
          {X} (R: relation X) (S: relation X) : relation X :=
  | rp0 : forall x y, forall z, R x y -> S y z -> relative_product R S x z.
*)
  intros x y Himp.

  inversion Himp.
  inversion H0.
  inversion H1.
  subst.

  rename y1 into z.
  rename y0 into w.
  clear H0 H1.

  specialize HSPQ with x y z w.
  specialize HSQP with x y z w.

  apply HSQP; assumption.
Qed.

Theorem similar_eqv2 :
  forall {X} (P Q : relation X), similar' P Q -> similar P Q.
Proof.
  intros.
  inversion H as [HExCorrelator].
  inversion HExCorrelator as [S Hcorrelator]. clear HExCorrelator.
  inversion Hcorrelator as [S' HS11 HSdomain HScodomain HSrp]. subst. clear Hcorrelator.

  constructor. exists S.

  repeat (split; try assumption; try intros; try specialize HSrp with x y);
    try (apply HSrp; apply rp0 with w; [ apply rp0 with z; assumption |
                                         apply cv0; assumption ]).

  rename H0 into HP.
  rename H1 into HSx.
  rename H2 into HSy.

  pose proof HScodomain as HScodomain'.
  specialize HScodomain with z.
  specialize HScodomain' with w.

  inversion HScodomain.
  inversion HScodomain'.
  clear H0 H2.

  assert (Qz : converse_domain S z).
  apply converse_domain_intro with x. assumption.

  assert (Qw : converse_domain S w).
  apply converse_domain_intro with y. assumption.

  apply H1 in Qz.
  apply H3 in Qw.

  (*
  assert (relative_product (relative_product S Q) (converse S) x y).
  apply rp0 with w; try apply cv0; try assumption.
  apply rp0 with z; try assumption.
  *)

  admit.
Qed.
