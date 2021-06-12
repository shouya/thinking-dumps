Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From PLF Require Import Maps.
From PLF Require Smallstep.
From Coq Require Import Lists.List.

Inductive ty : Type :=
  | Ty_Nat   : ty
  | Ty_Unit  : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Ref   : ty -> ty.

Inductive tm  : Type :=
  (* STLC with numbers: *)
  | tm_var    : string -> tm
  | tm_app    : tm -> tm -> tm
  | tm_abs    : string -> ty -> tm -> tm
  | tm_const  : nat -> tm
  | tm_succ    : tm -> tm
  | tm_pred    : tm -> tm
  | tm_mult    : tm -> tm -> tm
  | tm_if0  : tm -> tm -> tm -> tm
  (* Ref new terms: *)
  | tm_unit   : tm
  | tm_ref    : tm -> tm
  | tm_deref  : tm -> tm
  | tm_assign : tm -> tm -> tm
  | tm_loc    : nat -> tm
  (* GC new term: *)
  | tm_free   : tm -> tm
.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "{ x }" := x (in custom stlc at level 0, x constr).

Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).

Notation "'Natural'" := Ty_Nat (in custom stlc at level 0).
Notation "'succ' x" := (tm_succ x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "'pred' x" := (tm_pred x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "x * y" := (tm_mult x y) (in custom stlc at level 1,
                                      left associativity).
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Coercion tm_const : nat >-> tm.

Notation "'Ref' t" :=
  (Ty_Ref t) (in custom stlc at level 4).
Notation "'loc' x" := (tm_loc x) (in custom stlc at level 2).
Notation "'ref' x" := (tm_ref x) (in custom stlc at level 2).
Notation "'!' x " := (tm_deref x) (in custom stlc at level 2).
Notation " e1 ':=' e2 " := (tm_assign e1 e2) (in custom stlc at level 21).
Notation "'free' x" := (tm_free x) (in custom stlc at level 2).

Print Scopes.

Definition store := list (option tm).

Inductive store_lookup : nat -> store -> tm -> Prop :=
  | SL_found : forall r t, store_lookup 0 ((Some t) :: r) t
  | SL_next n r t (H: store_lookup n r t) : forall x, store_lookup (S n) (x :: r) t.

Inductive store_assign : store -> nat -> tm -> store -> Prop :=
  | SA_here : forall x r t, store_assign ((Some x) :: r) 0 t ((Some t)::r)
  | SA_next s n t s' x (H : store_assign s n t s') :
      store_assign (x::s) (S n) t (x::s')
.

Inductive store_assign_new : store -> nat -> tm -> store -> Prop :=
  | SAN_here : forall r t, store_assign_new (None :: r) 0 t ((Some t)::r)
  | SAN_next s n t s' x (H : store_assign_new s n t s') :
      store_assign_new (x::s) (S n) t (x::s')
.

Inductive store_free : store -> nat -> store -> Prop :=
  | SF_here : forall x r, store_free (Some x :: r) 0 (None::r)
  | SF_next s n s' x (H : store_free s n s') :
      store_free (x::s) (S n) (x::s')
.

Inductive first_empty_cell : store -> nat -> Prop :=
  | FEC_found : forall r, first_empty_cell (None :: r) 0
  | FEC_next s n (H: first_empty_cell s n) :
      forall x, first_empty_cell ((Some x) :: s) (S n)
.

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_nat : forall n : nat ,
      value <{ n }>
  | v_unit :
      value <{ unit }>
  | v_loc : forall l,
         value <{ loc l }>.

Hint Constructors value : core.

(** Extending substitution to handle the new syntax of terms is
    straightforward.  *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* pure STLC *)
  | tm_var y =>
      if eqb_string x y then s else t
  | <{\y:T, t1}> =>
      if eqb_string x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  (* numbers *)
  | tm_const _ =>
      t
  | <{succ t1}> =>
      <{succ [x := s] t1}>
  | <{pred t1}> =>
      <{pred [x := s] t1}>
  | <{t1 * t2}> =>
      <{ ([x := s] t1) * ([x := s] t2)}>
  | <{if0 t1 then t2 else t3}> =>
      <{if0 [x := s] t1 then [x := s] t2 else [x := s] t3}>
  (* unit *)
  | <{ unit }> =>
    <{ unit }>
  (* references *)
  | <{ ref t1 }> =>
      <{ ref ([x:=s] t1) }>
  | <{ !t1 }> =>
      <{ !([x:=s] t1) }>
  | <{ t1 := t2 }> =>
    <{ ([x:=s] t1) := ([x:=s] t2) }>
  | <{ loc _ }> =>
      t
  | <{ free t }> =>
    <{ free [x:=s]t }>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Reserved Notation "t / st --> t' / st'"
  (at level 40, st at level 39, t' at level 39).

Inductive step : tm * store -> tm * store -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2 st,
         value v2 ->
         <{ (\x : T2, t1) v2 }> / st --> <{ [x := v2] t1 }> / st
  | ST_App1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         <{ t1 t2 }> / st --> <{ t1' t2 }> / st'
  | ST_App2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 t2 }> / st --> <{ v1 t2' }> / st'
  (* numbers *)
  | ST_SuccNatural : forall (n : nat) st,
         <{ succ n }> / st --> tm_const (S n) / st
  | ST_Succ : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ succ t1 }> / st --> <{ succ t1' }> / st'
  | ST_PredNatural : forall (n : nat) st,
         <{ pred n }> / st --> tm_const (n - 1) / st
  | ST_Pred : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ pred t1 }> / st --> <{ pred t1' }> / st'
  | ST_MultNaturals : forall (n1 n2 : nat) st,
      <{ n1 * n2 }> / st -->  tm_const (n1 * n2) / st
  | ST_Mult1 : forall t1 t2 t1' st st',
         t1 / st --> t1' / st' ->
         <{ t1 * t2 }> / st --> <{ t1' * t2 }> / st'
  | ST_Mult2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 * t2 }> / st --> <{ v1 * t2' }> / st'
  | ST_If0 : forall t1 t1' t2 t3 st st',
         t1 / st --> t1' / st' ->
         <{ if0 t1 then t2 else t3 }> / st --> <{ if0 t1' then t2 else t3 }> / st'
  | ST_If0_Zero : forall t2 t3 st,
         <{ if0 0 then t2 else t3 }> / st --> t2 / st
  | ST_If0_Nonzero : forall n t2 t3 st,
         <{ if0 {S n} then t2 else t3 }> / st --> t3 / st
  (* references *)
  | ST_RefValue : forall v st st' n,
         value v ->
         first_empty_cell st n ->
         store_assign_new st n v st' ->
         <{ ref v }> / st --> <{ loc n }> / st'
  | ST_Ref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ ref t1 }> /  st --> <{ ref t1' }> /  st'
  | ST_DerefLoc : forall st n t,
         store_lookup n st t ->
         <{ !(loc n) }> / st --> <{ t }> / st
  | ST_Deref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ ! t1 }> / st --> <{ ! t1' }> / st'
  | ST_Assign : forall v l st st',
         value v ->
         store_assign st l v st' ->
         <{ (loc l) := v }> / st --> <{ unit }> / st'
  | ST_Assign1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         <{ t1 := t2 }> / st --> <{ t1' := t2 }> / st'
  | ST_Assign2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 := t2 }> / st --> <{ v1 := t2' }> / st'
  | ST_Free : forall st st' n,
      store_free st n st' ->
      <{free (loc n)}> / st --> <{unit}> / st'
  | ST_Free1 : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ free t1 }> / st --> <{ free t1' }> / st'
where "t / st --> t' / st'" := (step (t,st) (t',st')).

Definition multi_step := Smallstep.multi step.

Notation "t / st -->* t' / st'" :=
  (multi_step (t, st) (t', st'))
       (at level 40, st at level 39, t' at level 39).


Lemma can_assign_empty_cell : forall st n t,
       first_empty_cell st n ->
       exists st', store_assign_new st n t st'.
Proof.
  intros.
  generalize dependent st.
  induction n.
  - intros.
    inversion H; subst; clear H.
    eexists. constructor.

  - intros.
    inversion H; subst; clear H.
    apply IHn in H2. destruct H2.
    eexists. constructor. eauto.
Qed.

Lemma assign_new_free_inv : forall st n t st',
       store_assign_new st n t st' ->
       store_free st' n st.
Proof.
  intros.
  generalize dependent st.
  generalize dependent st'.
  induction n.
  - intros. inversion H; subst. constructor.

  - intros. inversion H; subst; clear H.
    apply IHn in H2. constructor. auto.
Qed.


Lemma free_ref_noop : forall st t n,
       (* I could have proved it for arbitrary t, but
          it would require proving progress first. Therefore I will be assuming
          t is a value.
        *)
       value t ->
       (* ensure that st has an empty space *)
       first_empty_cell st n ->
       <{free (ref t)}> / st -->* <{unit}> / st.
Proof.
  intros.
  assert (first_empty_cell st n) by auto.
  apply can_assign_empty_cell with (t:=t) in H1. destruct H1.
  rename x into st'.
  assert (store_free st' n st) by eauto using assign_new_free_inv.

  eapply Smallstep.multi_step.
  eapply ST_Free1.
  apply ST_RefValue; eauto.

  eapply Smallstep.multi_step.
  eapply ST_Free; eauto.

  eapply Smallstep.multi_refl.
Qed.
