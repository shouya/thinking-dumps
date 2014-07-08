

Require Export A007logic.

Definition relation (X: Type) := X->X->Prop.


Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold partial_function.
  intro.
  assert (0 = 1) as nonsense.
  apply H with (x:=0).
  reflexivity.
  apply le_S. reflexivity.
  inversion nonsense.
Qed.


Inductive total_relation : nat -> nat -> Prop :=
  tot : forall n m : nat, total_relation n m.


Theorem total_relation_not_a_partial_function :
  ~ (partial_function total_relation).
Proof.
  unfold partial_function.
  intro.
  assert (0 = 1).
  apply H with (x := 0).
  apply tot.
  apply tot.
  inversion H0.
Qed.


Inductive empty_relation : nat -> nat -> Prop :=.

Theorem empty_relation_is_a_partial_function :
  partial_function empty_relation.
Proof.
  unfold partial_function.
  intros.
  inversion H.
Qed.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive.
  intro.
  apply le_n.
Qed.


Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).







Theorem le_trans :
  transitive le.
Proof.
  unfold transitive.
  intros.
  (*
   H: a <= b
   H0: b <= c
   -----------
   a <= c
   *)
  induction H0.
  (* Goal 1:
     H: a <= b
     -----------
     a <= b

     Goal 2:
     H: a <= b
     m: nat
     H0: b <= m
     IHle: a <= m
     ------------
     a <= S m
   *)

  assumption.
  apply le_S. assumption.
Qed.

(* NOTE: i have once confused on how induction works here.
   then i posed the question on irc #coq, soonly i got a clear explanation.

   IRC log (abridged):

(01:42:22 AM) shouya: first of all, the type of le is nat -> nat -> Prop, right?
(01:42:36 AM) Cypi: Yes
(01:42:42 AM) shouya: so 'le a b' should have type of Prop isn't it?
(01:42:44 AM) ianjneu: le is an inductive definition that carries more information about the ordering relationship of two natural numbers.
(01:42:56 AM) Cypi: Yes it does
(01:42:59 AM) shouya: that's why it's valid to be put as a hypo.
(01:43:01 AM) shouya: and...
(01:43:02 AM) ianjneu: You can eliminate Prop into Prop.
(01:43:20 AM) shouya: why can i perform an induction on a Prop.
(01:43:32 AM) ianjneu: relation's return type is Prop.
(01:43:34 AM) shouya: Prop isn't any inductive type basically.
(01:43:41 AM) Cypi: Because in this case, [le] is an inductive definition
(01:44:02 AM) shouya: Cypi: okay, that's how i interpret it. fine.
(01:44:15 AM) shouya: and second, i don't know if i'm understanding correctly.
(01:44:50 AM) shouya: induction basically means to seperate an inductive definition into each cases, just like what 'destruct' does.
01:45
(01:45:18 AM) shouya: so as the definition of le, showing here: http://lpaste.net/107061
(01:45:42 AM) Ptival: shouya: yes, but on top of what destruct does, it also gives you a proof for the recursive occurences of the same type
(01:45:57 AM) shouya: Ptival: yup that's no problem.
(01:46:19 AM) shouya: but i found no where the cases goes in splited subgoals after induction.
(01:47:32 AM) Ptival: shouya: what is your misunderstanding
(01:47:45 AM) Ptival: so after induction you now have two subgoals, one for each of the constructors of `le`
(01:48:36 AM) shouya: Ptival: yup i think in this way.
(01:48:47 AM) Ptival: in the first case, `b` and `c` have been unified (because le_n is indexed at the same value as its parameter)
(01:49:31 AM) shouya: okay. good so far :)
01:50
(01:50:10 AM) shouya: so it should yield a hypo: b = c right?
(01:50:25 AM) shouya: okay... i get it.
(01:50:31 AM) shouya: how about the second case?
(01:50:39 AM) Ptival: well, it does, but then it just substs it, so you never see that hypothesis
(01:50:52 AM) Ptival: I mean, it doesn't, but morally you could think it does
(01:51:13 AM) shouya: Ptival: i see it :)
(01:51:46 AM) shouya: btw, updated paste: the goals before and after the induction are shown. http://lpaste.net/107061
(01:51:52 AM) Ptival: in fact, if you do 'remember c.' before the induction, you will see it
(01:52:18 AM) shouya: Ptival: i think i can comprehend this case, no problem :)
(01:52:35 AM) Ptival: not the second one?
(01:53:27 AM) Ptival: so in the second one, we consider the case where the original `b <= c` we did induction has been built using the constructor `le_S`
(01:54:08 AM) Ptival: so it must be the case that `b <= c` unifies with `n <= S m`, therefore `b` unifies with `n` and `c` unifies with `S m`
(01:54:22 AM) shouya: hmm...
(01:54:48 AM) shouya: gotcha!
01:55
(01:55:09 AM) Ptival: so you get in your context the parameters given to le_S: m, `n <= m` (which after unification becomes `b <= m`)
(01:55:22 AM) shouya: Ptival: thank you i think i got the idea of how it works :P
(01:55:40 AM) Ptival: and your goal is still `a <= c`, but `c` has been unified with `S m`, so the goal is `a <= S m`
(01:55:47 AM) shouya: yes, yes..
(01:56:07 AM) shouya: it just a little bit convoluted :)

*)


(*
  annotation by ianjneu: http://lpaste.net/107061,
  elaborating the detailed works
*)
Theorem le_trans' :
  transitive le.
Proof.
  unfold transitive.
  intros; generalize dependent c.
  induction H.  (* why? *)
  intros; assumption.
  intros; inversion H0; subst; apply le_S.
  assumption.
  apply IHle.
  assert (R : forall m n, S m <= n -> m <= n).
  induction n; [intro bad; inversion bad
               |intros K; inversion K; subst; constructor;
                  [constructor|apply IHn; assumption]].
  apply R; assumption.
Qed.



Theorem lt_le :
  forall a b : nat, a < b -> a < S b.
Proof.
  unfold lt. intros.
  induction H.
  constructor; constructor.
  constructor; apply IHle.
Qed.


Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt.
  unfold transitive.
  intros.
  apply le_S in H.
  apply le_trans with (a := (S a)) (b := (S b)) (c := c).
  assumption.
  assumption.
Qed.


Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that m is less than o. *)
  unfold lt. unfold transitive.
  intros.
  induction H0.
  constructor; assumption.
  constructor; assumption.
Qed.

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  inversion Hmo.
  induction Hmo; constructor; assumption.
Qed.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros.
  induction H.
  constructor; constructor.
  constructor; assumption.
Qed.

(* One star ??! *)
Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros.
  generalize dependent n.
  induction m.

  intros.
  induction n.
  constructor.

  inversion H.
  inversion H1.

  intros.
  induction n.
  assert (forall a, 0 <= a).
  induction a. constructor. constructor; assumption.
  apply H0.

  inversion H. constructor.

  apply le_trans with (S (S n)).
  constructor. constructor.

  assumption.
Qed.


Theorem le_Sn_n : forall n, ~(S n <= n).
Proof.
  intros. intro.
  induction n.
  inversion H.
  apply le_S_n in H. apply IHn in H. inversion H.
Qed.


Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).


(* prove by contradiction *)

Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  unfold symmetric. intro.
  assert (1 <= 0).
  apply H. constructor. constructor.
  inversion H0.
Qed.


Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.


Lemma Sn_neq_n : forall n, ~(S n = n).
Proof.
  induction n.
  intro. inversion H.
  intro.
  inversion H. apply IHn in H1.
  assumption.
Qed.

Lemma Sn_nle_n : forall n, ~(S n <= n).
Proof.
  intros. intro.
  induction n.
  inversion H.
  apply le_S_n in H. apply IHn in H. inversion H.
Qed.

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  intros.
  induction H0.
  reflexivity.

  assert (S m <= m).
  apply le_trans with (b := b); assumption.
  apply le_Sn_n in H1. inversion H1.
Qed.

Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  intros.
  unfold lt in H.
  assert (S n <= S p). apply le_trans with (b := m); assumption.
  apply le_S_n. assumption.
Qed.



Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).


Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).


Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order.
  split. apply le_reflexive.
  split. apply le_antisymmetric. apply le_trans.
Qed.

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step : forall x y, R x y -> clos_refl_trans R x y
    | rt_refl : forall x, clos_refl_trans R x x
    | rt_trans : forall x y z,
          clos_refl_trans R x y ->
          clos_refl_trans R y z ->
          clos_refl_trans R x z.


Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros. split.
  Case "->".
    intro.
    induction H.
    apply rt_refl.
    apply rt_trans with m. assumption.
    apply rt_step. apply nn.

  Case "<-".
    intro. induction H.
    induction H. apply le_S. apply le_n.
    apply le_n.
    apply le_trans with y. assumption. assumption.
Qed.

Inductive refl_step_closure {X:Type} (R: relation X) : relation X :=
  | rsc_refl : forall (x : X), refl_step_closure R x x
  | rsc_step : forall (x y z : X),
                    R x y ->
                    refl_step_closure R y z ->
                    refl_step_closure R x z.

Tactic Notation "rt_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rt_step" | Case_aux c "rt_refl"
  | Case_aux c "rt_trans" ].

Tactic Notation "rsc_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rsc_refl" | Case_aux c "rsc_step" ].



Theorem rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> refl_step_closure R x y.
Proof.
  intros.
  apply rsc_step with y. assumption.
  apply rsc_refl.
Qed.

Theorem rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      refl_step_closure R x y ->
      refl_step_closure R y z ->
      refl_step_closure R x z.
Proof.
  intros.
  induction H. assumption.
  apply rsc_step with y. assumption.
  apply IHrefl_step_closure. assumption.
Qed.
