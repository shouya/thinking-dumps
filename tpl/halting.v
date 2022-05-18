(* untyped lambda calculus *)

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Open Scope string_scope.


Inductive term :=
| TVar (var: string) : term
| TLam (var: string) (body: term) : term
| TApp (rator: term) (rand: term) : term
.

Declare Custom Entry term.

Notation "{{ x }}" := x (x custom term).
Notation "( x )" := x (in custom term, x custom term).

Notation "'λ' a , body" :=
  (TLam a body) (in custom term at level 98
                      , a constr at level 0  (* avoid ":" being interpreted as type *)
                      , body custom term at level 99
                      , right associativity).

Notation "t1 t2" :=
  (TApp t1 t2) (in custom term at level 97
                   , t1 custom term
                   , t2 custom term
                   , left associativity).

Coercion TVar : string >-> term.

Inductive value : term -> Prop :=
| VLam : forall x t, value (TLam x t)
.
Hint Constructors value.

Fixpoint sub (t: term) (x: string) (v: term) :=
  match t with
  | TLam x' t' => if String.eqb x x'
                 then TLam x' t'
                 else TLam x' (sub t' x v)
  | TVar x' => if  String.eqb x x'
              then v
              else x'
  | TApp t1 t2 => TApp (sub t1 x v) (sub t2 x v)
  end.

Notation "[ x '|->' v ] t" :=
  (sub t x v) ( in custom term at level 96
                   , t custom term
                   , v custom term
                   , x constr at level 0
                   , right associativity
              ).

(* the ~value terms are not necessary, but I don't want to bother
proving progress again so I included them in the rules *)
Inductive step : term -> term -> Prop :=
| EApp1 : forall t1 t1' t2, ~(value t1) ->
                       step t1 t1' -> step (TApp t1 t2) (TApp t1' t2)
| EApp2 : forall v1 t2 t2', value v1 ->
                       ~(value t2) ->
                       step t2 t2' -> step (TApp v1 t2) (TApp v1 t2')
| EAppAbs : forall x t1 v2, value v2 ->
                       step (TApp (TLam x t1) v2) (sub t1 x v2)
.
Hint Constructors step.

Inductive multi_step : term -> term -> Prop :=
| MS0 : forall t, multi_step t t
| MSs : forall t t' t'', step t t' -> multi_step t' t'' -> multi_step t t''.

Inductive evals_to : term -> term -> Prop :=
| EtVal : forall t, value t -> evals_to t t
| EtStep : forall t t' t'', step t t' -> evals_to t' t'' -> evals_to t t''.
Hint Constructors evals_to.

Lemma evals_to_trans : forall a b c, evals_to a b -> evals_to b c -> evals_to a c.
Proof.
  intros a b c H.
  generalize dependent c.
  induction H; intros.
  - auto.
  - apply IHevals_to in H1. eauto.
Qed.
Hint Resolve evals_to_trans.

Lemma evals_to_app : forall a b a' b',
    evals_to a a' -> evals_to b b' -> evals_to (TApp a b) (TApp a' b').
Proof.
  intros.
  induction H.
  - induction H0.
    + auto.
    + apply evals_to_trans.


Definition halting (t: term) : Prop := exists v, evals_to t v.
Hint Unfold halting.

Definition x := "x".
Example omega_ := TApp (TLam x (TApp x x)) (TLam x (TApp x x)).

Example omega_non_halting : ~(halting omega_).
Proof.
  unfold omega_.
  unfold halting.
  intro.
  remember (TApp (TLam x (TApp x x)) (TLam x (TApp x x))) as omega_.
  destruct H as [v].
  induction H; intros; subst.
  - inversion H.
  - inversion H.
    + subst. apply H3. easy.
    + subst. apply H4. easy.
    + subst. apply IHevals_to. easy.
Qed.

(* church encoding for true and false *)
Definition tru_ := TLam "a" (TLam "b" "a").
Definition fls_ := TLam "a" (TLam "b" "b").
Definition if_ := TLam "p" (TLam "a" (TLam "b" (TApp (TApp "p" "a") "b"))).

Lemma if_tru_fls : forall cond t f,
    (evals_to cond tru_ -> evals_to (TApp (TApp (TApp if_ cond) t) f) t) /\
    (evals_to cond fls_ -> evals_to (TApp (TApp (TApp if_ cond) t) f) f).
Proof.
  intros.
  unfold if_, tru_, fls_.
  split.
  - (* case: cond evals_to true *)
    intro.
    apply evals_to_trans with (b := (TApp (TApp tru_ t) f)).
    eapply evals_to_trans.

    (* apply evals_to_trans with (b := (TApp (TApp tru_ t) f)). *)


    eapply EtStep.
    eapply EApp1; auto.
    eapply EApp1; auto.
  - (* case: cond evals_to false *)


Definition oracle (o: term) :=
  forall t input, (evals_to (TApp (TApp o t) input) tru_ \/
              evals_to (TApp (TApp o t) input) fls_)
             /\ (evals_to (TApp (TApp o t) input) tru_ <->
                halting (TApp t input))
             /\ (evals_to (TApp (TApp o t) input) fls_ <->
                ~(halting (TApp t input))).

Definition problematic (oracle: term) :=
  TLam "i" (TApp (TApp (TApp if_ (TApp oracle "i")) omega_) tru_).

Lemma problematic_property :
  forall m, halting (problematic m) -> evals_to (problematic m) tru_.
Proof.
  intros.
  unfold problematic in *.
  destruct H.
  eapply EtStep.



(* halting problem *)
Theorem halting_problem : ~exists o, oracle o.
Proof.
  unfold oracle.
  intro.
  destruct H as [oracle].
  remember (
      (* λi.if_ (halts i) then omega_ else tru *)
      TLam "i" (TApp (TApp (TApp if_ (TApp oracle "i")) omega_) tru_)
    )
    as problematic.
  pose proof (H problematic problematic).
  clear H.
  destruct H0 as [[Hch | Hcnh] [Hh Hnh]].
  - (* Case 1: problematic halts on problematic *)
    apply Hh in Hch.
    unfold halting in Hch.
    destruct Hch.
    inversion H
