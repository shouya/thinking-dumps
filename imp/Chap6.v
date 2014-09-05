
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
there is a (1) one-one relation S
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
| similar_intro : (exists (S : relation X),
                     one_one S ->
                     (forall x, domain S x <-> field P x) ->
                     (forall x, converse_domain S x <-> field Q x) ->
                     (forall x y x' y', S x x' -> S y y' -> (P x y <-> Q x' y'))) ->
                      similar P Q.

(* This theorem is not mentioned on the book but I want to prove it *)
Theorem one_one_has_inverse :
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
