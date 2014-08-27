
Require Export A009prop.


Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.


Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros.
  inversion H as [m].
  exists (2 + m).
  apply H0.
Qed.

Lemma exists_example_3 :
  exists (n:nat), even n /\ beautiful n.
Proof.
  exists 8. split. constructor. apply b_sum with (n:=3)(m:=5); constructor.
Qed.


(* ex nat (fun n => beautiful (S n)). *)
(* Means that exists a n:nat, beautiful S n.
*)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros. intro.
  inversion H0. apply H1. apply H.
Qed.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle.
  intros.
  assert (P x \/ ~P x). apply H.
  inversion H1. assumption.
  elimtype False. (* Ex falso quodlibet *)

  apply H0.
  exists (x). assumption.
Qed.



Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros.
  split; intro.
  inversion H. inversion H0.
    left. exists witness. assumption.
    right. exists witness. assumption.

  inversion H; inversion H0.
    exists witness. left. assumption.
    exists witness. right. assumption.
Qed.

Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B
 | right : B -> sumbool A B.

Notation "{ A } + { B }" := (sumbool A B) : type_scope.

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  induction n.
  destruct m. left. reflexivity.
              right. intro. inversion H.
  destruct m. right. intro. inversion H.
              destruct IHn with m.
                left. apply f_equal. assumption.
                right. intro. inversion H. intuition.
Qed.

Definition override' {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same' : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 ->
  (override' f k1 x1) k2 = f k2.
Proof.
  unfold override'. intros.
  destruct (eq_nat_dec k1 k2).
    rewrite <- H. apply f_equal. assumption.
    reflexivity.
Qed.

Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  unfold override'. intros.
  destruct (eq_nat_dec k1 k2).
    reflexivity.
    reflexivity.
Qed.

Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
  | all0 : all P []
  | allI : forall x xs, P x -> all P xs -> all P (x :: xs).

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

Theorem forallb_true_imp_all :
  forall {X} (p : X -> bool) l, forallb p l = true ->
                                all (fun x => p x = true) l.
Proof.
  intros.
  induction l.
    apply all0.
    simpl in H.
      destruct (p x) eqn:px.
      assert (forallb p l = true).
      destruct (forallb p l). reflexivity. inversion H.
      apply IHl in H0. apply allI. assumption. assumption.

      inversion H.
Qed.

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X),
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros.
  induction xs. simpl in H. right. assumption.
  inversion H. left. constructor.
  apply IHxs in H1. inversion H1. subst.
    left. constructor. assumption.
    right. assumption.
Qed.


Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X),
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros.
  inversion H.
  induction H0.
  apply ai_here.
  simpl. apply ai_later.
  apply IHappears_in. left. assumption.

  induction xs. simpl. assumption.
  simpl. apply ai_later. apply IHxs. right. assumption.
Qed.

Definition disjoint {X} (xs ys : list X) : Prop :=
  forall a, appears_in a xs -> ~appears_in a ys.

Inductive no_repeats {X} : list X -> Prop :=
  | nr_null : no_repeats []
  | nr_cons : forall x xs, no_repeats xs -> ~(appears_in x xs) -> no_repeats (x::xs).

Goal forall {X} (xs ys : list X),
       no_repeats xs ->
       no_repeats ys ->
       disjoint xs ys ->
       no_repeats (xs ++ ys).
Proof.
  intros X xs ys Hxs Hys Hdisj.
  generalize dependent ys.
  induction Hxs.

  Case "nr_null []". intros.
  assumption.

  Case "nr_cons, xs = x::xs".
  intros ys Hys Hdisj.
  unfold disjoint in Hdisj.
  simpl.
  apply nr_cons.
  apply IHHxs. assumption.
  unfold disjoint. intros. apply Hdisj. apply ai_later. assumption.

  intro. apply appears_in_app in H0. inversion H0.

  apply H in H1. inversion H1. inversion H1. subst.
  unfold not in Hdisj. apply Hdisj with x. apply ai_here.
  assumption.

  subst.
  unfold not in Hdisj. apply Hdisj with x. apply ai_here. assumption.
Qed.

Inductive nostutter: list nat -> Prop :=
  | ns0 : nostutter []
  | ns1 : forall x, nostutter [x]
  | nsc : forall x x' xs, nostutter (x'::xs) -> x' <> x -> nostutter (x::x'::xs).

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. repeat constructor; apply beq_nat_false; auto. Qed.

Example test_nostutter_2: nostutter [].
Proof. repeat constructor; apply beq_nat_false; auto. Qed.

Example test_nostutter_3: nostutter [5].
Proof. repeat constructor; apply beq_nat_false; auto. Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction H5; auto.
Qed.
