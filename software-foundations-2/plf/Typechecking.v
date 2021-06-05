(** * Typechecking: A Typechecker for STLC *)

(** The [has_type] relation of the STLC defines what it means for a
    term to belong to a type (in some context).  But it doesn't, by
    itself, give us an algorithm for _checking_ whether or not a term
    is well typed.

    Fortunately, the rules defining [has_type] are _syntax directed_
    -- that is, for every syntactic form of the language, there is
    just one rule that can be used to give a type to terms of that
    form.  This makes it straightforward to translate the typing rules
    into clauses of a typechecking _function_ that takes a term and a
    context and either returns the term's type or else signals that
    the term is not typable.  *)

(** This short chapter constructs such a function and proves it
    correct. *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.
From PLF Require MoreStlc.

Module STLCTypes.
Export STLC.

(* ################################################################# *)
(** * Comparing Types *)

(** First, we need a function to compare two types for equality... *)

Locate "Bool".

Fixpoint eqb_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | <{ Bool }> , <{ Bool }> =>
      true
  | <{ T11->T12 }>, <{ T21->T22 }> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | _,_ =>
      false
  end.

(** ... and we need to establish the usual two-way connection between
    the boolean result returned by [eqb_ty] and the logical
    proposition that its inputs are equal. *)

Lemma eqb_ty_refl : forall T,
  eqb_ty T T = true.
Proof.
  intros T. induction T; simpl.
    reflexivity.
    rewrite IHT1. rewrite IHT2. reflexivity.  Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof with auto.
  intros T1. induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq.
  - (* T1=Bool *)
    reflexivity.
  - (* T1 = T1_1->T1_2 *)
    rewrite andb_true_iff in H0. inversion H0 as [Hbeq1 Hbeq2].
    apply IHT1_1 in Hbeq1. apply IHT1_2 in Hbeq2. subst...  Qed.
End STLCTypes.

(* ################################################################# *)
(** * The Typechecker *)

(** The typechecker works by walking over the structure of the given
    term, returning either [Some T] or [None].  Each time we make a
    recursive call to find out the types of the subterms, we need to
    pattern-match on the results to make sure that they are not
    [None].  Also, in the [app] case, we use pattern matching to
    extract the left- and right-hand sides of the function's arrow
    type (and fail if the type of the function is not [T11->T12]
    for some [T11] and [T12]). *)

Module FirstTry.
Import STLCTypes.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      Gamma x
  | <{\x:T2, t1}> =>
      match type_check (x |-> T2 ; Gamma) t1 with
      | Some T1 => Some <{T2->T1}>
      | _ => None
      end
  | <{t1 t2}> =>
      match type_check Gamma t1, type_check Gamma t2 with
      | Some <{T11->T12}>, Some T2 =>
          if eqb_ty T11 T2 then Some T12 else None
      | _,_ => None
      end
  | <{true}> =>
      Some <{Bool}>
  | <{false}> =>
      Some <{Bool}>
  | <{if guard then t else f}> =>
      match type_check Gamma guard with
      | Some <{Bool}> =>
          match type_check Gamma t, type_check Gamma f with
          | Some T1, Some T2 =>
              if eqb_ty T1 T2 then Some T1 else None
          | _,_ => None
          end
      | _ => None
      end
  end.

End FirstTry.

(* ################################################################# *)
(** * Digression: Improving the Notation *)

(** Before we consider the properties of this algorithm, let's write
    it out again in a cleaner way, using "monadic" notations in the
    style of Haskell to streamline the plumbing of options.  First, we
    define a notation for composing two potentially failing (i.e.,
    option-returning) computations: *)

Notation " x <- e1 ;; e2" := (match e1 with
                              | Some x => e2
                              | None => None
                              end)
         (right associativity, at level 60).

(** Second, we define [return] and [fail] as synonyms for [Some] and
    [None]: *)

Notation " 'return' e "
  := (Some e) (at level 60).

Notation " 'fail' "
  := None.

Module STLCChecker.
Import STLCTypes.

(** Now we can write the same type-checking function in a more
    imperative-looking style using these notations. *)

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
    T <- Gamma x ;; return T
  | <{\x:T2, t1}> =>
      T1 <- type_check (x |-> T2 ; Gamma) t1 ;;
      return <{T2->T1}>
  | <{t1 t2}> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{T11->T12}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | <{true}> =>
      return <{ Bool }>
  | <{false}> =>
      return <{ Bool }>
  | <{if guard then t1 else t2}> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match Tguard with
      | <{ Bool }> =>
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  end.

(* ################################################################# *)
(** * Properties *)

(** To verify that the typechecking algorithm is correct, we show that
    it is _sound_ and _complete_ for the original [has_type]
    relation -- that is, [type_check] and [has_type] define the same
    partial function. *)

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H.
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    remember (type_check Gamma t1) as TO1.
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct T1 as [|T11 T12]; try solve_by_invert;
    remember (type_check Gamma t2) as TO2;
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (eqb_ty T11 T2) eqn: Heqb.
    apply eqb_ty__eq in Heqb.
    inversion H0; subst...
    inversion H0.
  - (* abs *)
    rename s into x, t into T1.
    remember (x |-> T1 ; Gamma) as G'.
    remember (type_check G' t0) as TO2.
    destruct TO2; try solve_by_invert.
    inversion H0; subst...
  - (* tru *) eauto.
  - (* fls *) eauto.
  - (* test *)
    remember (type_check Gamma t1) as TOc.
    remember (type_check Gamma t2) as TO1.
    remember (type_check Gamma t3) as TO2.
    destruct TOc as [Tc|]; try solve_by_invert.
    destruct Tc; try solve_by_invert;
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (eqb_ty T1 T2) eqn:Heqb;
    try solve_by_invert.
    apply eqb_ty__eq in Heqb.
    inversion H0. subst. subst...
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
Proof with auto.
  intros Gamma t T Hty.
  induction Hty; simpl.
  - (* T_Var *) destruct (Gamma x0) eqn:H0; assumption.
  - (* T_Abs *) rewrite IHHty...
  - (* T_App *)
    rewrite IHHty1. rewrite IHHty2.
    rewrite (eqb_ty_refl T2)...
  - (* T_True *) eauto.
  - (* T_False *) eauto.
  - (* T_If *) rewrite IHHty1. rewrite IHHty2.
    rewrite IHHty3. rewrite (eqb_ty_refl T1)...
Qed.

End STLCChecker.

(* ################################################################# *)
(** * Exercises *)

(** **** Exercise: 5 stars, standard (typechecker_extensions)

    In this exercise we'll extend the typechecker to deal with the
    extended features discussed in chapter [MoreStlc].  Your job
    is to fill in the omitted cases in the following. *)

Module TypecheckerExtensions.
(* Do not modify the following line: *)
Definition manual_grade_for_type_checking_sound : option (nat*string) := None.
(* Do not modify the following line: *)
Definition manual_grade_for_type_checking_complete : option (nat*string) := None.
Import MoreStlc.
Import STLCExtended.

Fixpoint eqb_ty (T1 T2 : ty) : bool :=
  match T1,T2 with
  | <{{Nat}}>, <{{Nat}}> =>
      true
  | <{{Unit}}>, <{{Unit}}> =>
      true
  | <{{T11 -> T12}}>, <{{T21 -> T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{T11 * T12}}>, <{{T21 * T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{T11 + T12}}>, <{{T21 + T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{List T11}}>, <{{List T21}}> =>
      eqb_ty T11 T21
  | _,_ =>
      false
  end.

Lemma eqb_ty_refl : forall T,
  eqb_ty T T = true.
Proof.
  intros T.
  induction T; simpl; auto;
    rewrite IHT1; rewrite IHT2; reflexivity.  Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof.
  intros T1.
  induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq;
    try reflexivity;
    try (rewrite andb_true_iff in H0; inversion H0 as [Hbeq1 Hbeq2];
         apply IHT1_1 in Hbeq1; apply IHT1_2 in Hbeq2; subst; auto);
    try (apply IHT1 in Hbeq; subst; auto).
 Qed.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | <{ \ x1 : T1, t2 }> =>
      T2 <- type_check (x1 |-> T1 ; Gamma) t2 ;;
      return <{{T1 -> T2}}>
  | <{ t1 t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{{T11 -> T12}}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | tm_const _ =>
      return <{{Nat}}>
  | <{ succ t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _ => fail
      end
  | <{ pred t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _ => fail
      end
  | <{ t1 * t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1, T2 with
      | <{{Nat}}>, <{{Nat}}> => return <{{Nat}}>
      | _,_        => fail
      end
  | <{ t.fst }> =>
    match type_check Gamma t with
    | Some <{{T1 * T2}}> => return T1
    | _ => fail
    end
  | <{ t.snd }> =>
    match type_check Gamma t with
    | Some <{{T1 * T2}}> => return T2
    | _ => fail
    end
  | <{ if0 guard then t else f }> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t ;;
      T2 <- type_check Gamma f ;;
      match Tguard with
      | <{{Nat}}> => if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end

  (* Complete the following cases. *)

  (* sums *)
  | <{ inl T2 t }> =>
    T1 <- type_check Gamma t ;;
    return <{{T1 + T2}}>
  | <{ inr T1 t }> =>
    T2 <- type_check Gamma t ;;
    return <{{T1 + T2}}>
  | <{ case t of | inl x1 => t1 | inr x2 => t2 }> =>
    match type_check Gamma t with
    | Some <{{T1 + T2}}> =>
      T3  <- type_check (x1 |-> T1; Gamma) t1 ;;
      T3' <- type_check (x2 |-> T2; Gamma) t2 ;;
      if eqb_ty T3 T3' then return T3 else fail
    | _ => fail
    end


  (* lists (the [tlcase] is given for free) *)
  | <{ nil T }> => return <{{List T}}>
  | <{ h :: t }> =>
    Th <- type_check Gamma h ;;
    match type_check Gamma t with
    | Some <{{List T}}> => if eqb_ty T Th then return <{{List T}}> else fail
    | _ => fail
    end
  | <{ case t0 of | nil => t1 | x21 :: x22 => t2 }> =>
      match type_check Gamma t0 with
      | Some <{{List T}}> =>
          match type_check Gamma t1,
                type_check (x21 |-> T ; x22 |-> <{{List T}}> ; Gamma) t2 with
          | Some T1', Some T2' =>
              if eqb_ty T1' T2' then Some T1' else None
          | _,_ => None
          end
      | _ => None
      end
  (* unit *)
  | <{ unit }> => return <{{Unit}}>
  (* pairs *)
  | <{(t1,t2)}> =>
    T1 <- type_check Gamma t1 ;;
    T2 <- type_check Gamma t2 ;;
    return <{{T1 * T2}}>
  (* let *)
  | <{let x=v in t}> =>
    Tv <- type_check Gamma v ;;
    type_check (x |-> Tv ; Gamma) t
  (* fix *)
  | <{ fix t }> =>
    match type_check Gamma t with
    | Some <{{T -> T'}}> => if eqb_ty T T' then return T else fail
    | _ => fail
    end
  end.

(** Just for fun, we'll do the soundness proof with just a bit more
    automation than above, using these "mega-tactics": *)

Ltac invert_typecheck Gamma t T :=
  remember (type_check Gamma t) as TO;
  destruct TO as [T|];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

Ltac analyze T T1 T2 :=
  destruct T as [T1 T2| |T1 T2|T1| |T1 T2]; try solve_by_invert.

Ltac fully_invert_typecheck Gamma t T T1 T2 :=
  let TX := fresh T in
  remember (type_check Gamma t) as TO;
  destruct TO as [TX|]; try solve_by_invert;
  destruct TX as [T1 T2| |T1 T2|T1| |T1 T2];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

Ltac case_equality S T :=
  destruct (eqb_ty S T) eqn: Heqb;
  inversion H0; apply eqb_ty__eq in Heqb; subst; subst; eauto.

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T ->
  has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H.
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12.
    case_equality T11 T2.
  - (* abs *)
    rename s into x, t into T1.
    remember (x |-> T1 ; Gamma) as Gamma'.
    invert_typecheck Gamma' t0 T0.
  - (* const *) eauto.
  - (* scc *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* prd *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* mlt *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12; analyze T2 T21 T22.
    inversion H0. subst. eauto.
  - (* test0 *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    invert_typecheck Gamma t3 T3.
    destruct T1; try solve_by_invert.
    case_equality T2 T3.
  - (* inl *)
    rename t into T2.
    invert_typecheck Gamma t0 T1.
  - (* inr *)
    rename t into T1.
    invert_typecheck Gamma t0 T2.
  - (* sum case *)
    invert_typecheck Gamma t1 T12.
    analyze T12 T1 T2.
    rename s into x1. rename s0 into x2.
    rename t1 into t0. rename t2 into t1. rename t3 into t2.
    invert_typecheck (x1 |-> T1; Gamma) t1 HT3.
    invert_typecheck (x2 |-> T2; Gamma) t2 HT3'.
    case_equality HT3 HT3'.
  - (* nil *)
    subst...
  - (* cons *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T2 T2' T2''.
    case_equality T2' T1.
  - (* tlcase *)
    rename s into x31, s0 into x32.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
    invert_typecheck Gamma t2 T2.
    remember (x31 |-> T11 ; x32 |-> <{{List T11}}> ; Gamma) as Gamma'2.
    invert_typecheck Gamma'2 t3 T3.
    case_equality T2 T3.
  - (* unit *)
    eauto.
  - (* pair *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
  - (* fst *)
    invert_typecheck Gamma t T'.
    analyze T' T'1 T'2.
    inversion H0. subst. eauto.
  - (* snd *)
    invert_typecheck Gamma t T'.
    analyze T' T'1 T'2.
    inversion H0. subst. eauto.
  - (* let *)
    invert_typecheck Gamma t1 T'.
  - (* fix *)
    invert_typecheck Gamma t T'.
    analyze T' T'1 T'2.
    case_equality T'1 T'2.
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T ->
  type_check Gamma t = Some T.
Proof.
  intros Gamma t T Hty.
  induction Hty; simpl;
    try (rewrite IHHty);
    try (rewrite IHHty1);
    try (rewrite IHHty2);
    try (rewrite IHHty3);
    try (rewrite (eqb_ty_refl T0));
    try (rewrite (eqb_ty_refl T1));
    try (rewrite (eqb_ty_refl T2));
    try (rewrite (eqb_ty_refl T3));
    eauto.
  - destruct (Gamma x0); [assumption| solve_by_invert].
  - rewrite eqb_ty_refl.  reflexivity.
Qed.

End TypecheckerExtensions.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (stlc_step_function)

    Above, we showed how to write a typechecking function and prove it
    sound and complete for the typing relation.  Do the same for the
    operational semantics -- i.e., write a _function_ [stepf] of type
    [tm -> option tm] and prove that it is sound and complete with
    respect to [step] from chapter [MoreStlc]. *)

Module StepFunction.
Import MoreStlc.
Import STLCExtended.

Fixpoint valueb (t : tm) : bool :=
  match t with
  | <{\x:T2, t1}> => true
  | tm_const _ => true
  | <{inl _ v}> => valueb v
  | <{inr _ v}> => valueb v
  | <{nil _}> => true
  | <{x :: xs}> => valueb x && valueb xs
  | <{unit}> => true
  | <{(a,b)}> => valueb a && valueb b
  | _ => false
  end.

(* Operational semantics as a Coq function. *)
Fixpoint stepf (t : tm) : option tm :=
  match t with
  | tm_var x => fail
  | <{ \ x1 : T1, t2 }> => fail
  | <{ t1 t2 }> =>
    match t1, valueb t2 with
    | <{\x1 : T1, t1'}>, true => Some <{ [x1:=t2]t1' }>
    | <{\x1 : T1, t1'}>, false =>
      t2' <- stepf t2 ;; Some <{ (\x1 : T1, t1') t2' }>
    | t1, _ =>
      t1' <- stepf t1 ;; Some <{ t1' t2 }>
    end
  | tm_const _ => fail
  | <{ succ t1 }> =>
    match t1 with
    | tm_const n => Some (tm_const (S n))
    | _ => t1' <- stepf t1 ;; Some <{ succ t1' }>
    end
  | <{ pred t1 }> =>
    match t1 with
    | tm_const n => Some (tm_const (n - 1))
    | _ => t1' <- stepf t1 ;; Some <{ pred t1' }>
    end
  | <{ t1 * t2 }> =>
    match t1, t2 with
    | tm_const n1, tm_const n2 => Some (tm_const (n1 * n2))
    | tm_const _, t2 => t2' <- stepf t2 ;; Some <{ t1 * t2' }>
    | t1, t2 => t1' <- stepf t1 ;; Some <{ t1' * t2 }>
    end
  | <{(t1,t2)}> =>
    match valueb t1, valueb t2 with
    | false, _ => t1' <- stepf t1 ;; Some <{(t1', t2)}>
    | true, false => t2' <- stepf t2 ;; Some <{(t1, t2')}>
    | _, _ => fail
    end
  | <{ t.fst }> =>
    match t with
    | <{(t1,t2)}> => Some t1
    | t' => t'' <- stepf t' ;; Some <{ t''.fst }>
    end
  | <{ t.snd }> =>
    match t with
    | <{(t1,t2)}> => Some t2
    | t' => t'' <- stepf t' ;; Some <{ t''.snd }>
    end
  | <{ if0 guard then t else f }> =>
    match guard with
    | tm_const 0 => Some t
    | tm_const _ => Some f
    | g => g' <- stepf g ;; Some <{ if0 g' then t else f }>
    end
  | <{ inl T2 t }> => t' <- stepf t ;; Some <{ inl T2 t' }>
  | <{ inr T1 t }> => t' <- stepf t ;; Some <{ inr T1 t' }>
  | <{ case t of | inl x1 => t1 | inr x2 => t2 }> =>
    match t with
    | <{ inl T2 t' }> => if valueb t' then Some <{[x1:=t']t1}> else fail
    | <{ inr T1 t' }> => if valueb t' then Some <{[x2:=t']t2}> else fail
    | _ => t' <- stepf t ;; Some <{ case t' of | inl x1 => t1 | inr x2 => t2  }>
    end
  | <{ nil T }> => fail
  | <{ h :: t }> =>
    match valueb h, valueb t with
    | false, _ => h' <- stepf h ;; Some <{ h' :: t }>
    | true, false => t' <- stepf t ;; Some <{ h :: t' }>
    | _, _ => fail
    end
  | <{ case t0 of | nil => t1 | x21 :: x22 => t2 }> =>
    match t0 with
    | <{ nil _ }> => Some t1
    | <{ h :: t }> => if valueb h then
                    if valueb t then
                    Some <{[x22 := t]([x21 := h]t2)}>
                    else fail
                    else fail
    | _ => t0' <- stepf t0 ;; Some <{ case t0' of | nil => t1 | x21 :: x22 => t2 }>
    end
  | <{ unit }> => fail
  | <{let x=v in t}> =>
    match valueb v with
    | true => Some <{[x:=v]t}>
    | false => v' <- stepf v ;; Some <{let x=v' in t}>
    end
  | <{ fix t }> =>
    match t with
    | <{\xf:T, t}> => Some <{ [xf:=fix (\xf:T, t)]t }>
    | _ => t' <- stepf t ;; Some <{ fix t' }>
    end
  end.

Hint Unfold stepf : core.

Theorem sound_valueb : forall t,
  valueb t = true -> value t.
Proof.
  intro. induction t; intro; eauto; try solve_by_invert.
  - (* cons *)
    inversion H. rewrite andb_true_iff in H1. destruct H1. eauto.
  - (* pair *)
    inversion H. rewrite andb_true_iff in H1. destruct H1. eauto.
Qed.

Theorem complete_valueb : forall t,
  value t -> valueb t = true.
Proof.
  intros. induction H; auto; simpl; rewrite IHvalue1; rewrite IHvalue2; easy.
Qed.

Hint Resolve complete_valueb : core.
Hint Resolve sound_valueb : core.

Theorem no_step_for_values : forall t,
  value t -> stepf t = None.
Proof.
  intros. induction H; auto; simpl;
          try (rewrite IHvalue; auto);
          try (rewrite IHvalue1; rewrite IHvalue2; auto);
          try (apply complete_valueb in H; apply complete_valueb in H0;
               rewrite H; rewrite H0;
               auto).
Qed.

From PLF Require Import MyTactics.

Ltac solve_stepf :=
  repeat (MyTactics.solve_stepf_step tm stepf valueb).

(* Soundness of [stepf]. *)
Theorem sound_stepf : forall t t',
    stepf t = Some t'  ->  t --> t'.
Proof.
  intro.
  induction t; intros t' H; inversion H; clear H; auto.
  - (* App *)
    solve_stepf.
  - (* Succ *)
    solve_stepf.
  - (* Pred *)
    solve_stepf.
  - (* Mult *)
    solve_stepf.
  - (* If0 *)
    solve_stepf.
  - (* Inl *)
    solve_stepf.
  - (* Inr *)
    solve_stepf.
  - (* Case Either *)
    solve_stepf.
  - (* Cons *)
    solve_stepf.
  - (* Case List *)
    solve_stepf.
  - (* Pair *)
    solve_stepf.
  - (* Fst *)
    solve_stepf.
  - (* Snd *)
    solve_stepf.
  - (* Let *)
    solve_stepf.
  - (* Fix *)
    solve_stepf.
Qed.

(* Completeness of [stepf]. *)
Theorem complete_stepf : forall t t',
    t --> t'  ->  stepf t = Some t'.
Proof. (* FILL IN HERE *) Admitted.

End StepFunction.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (stlc_impl)

    Using the Imp parser described in the [ImpParser] chapter
    of _Logical Foundations_ as a guide, build a parser for extended
    STLC programs.  Combine it with the typechecking and stepping
    functions from the above exercises to yield a complete typechecker
    and interpreter for this language. *)

Module StlcImpl.
Import StepFunction.

(* FILL IN HERE *)
End StlcImpl.
(** [] *)

(* 2020-09-09 21:08 *)
