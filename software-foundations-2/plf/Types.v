(** * Types: Type Systems *)

(** Our next major topic is _type systems_ -- static program
    analyses that classify expressions according to the "shapes" of
    their results.  We'll begin with a typed version of the simplest
    imaginable language, to introduce the basic ideas of types and
    typing rules and the fundamental theorems about type systems:
    _type preservation_ and _progress_.  In chapter [Stlc] we'll move
    on to the _simply typed lambda-calculus_, which lives at the core
    of every modern functional programming language (including
    Coq!). *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From PLF Require Import Maps.
From PLF Require Import Imp.
From PLF Require Import Smallstep.

Hint Constructors multi : core.

(* ################################################################# *)
(** * Typed Arithmetic Expressions *)

(** To motivate the discussion of type systems, let's begin as
    usual with a tiny toy language.  We want it to have the potential
    for programs to go wrong because of runtime type errors, so we
    need something a tiny bit more complex than the language of
    constants and addition that we used in chapter [Smallstep]: a
    single kind of data (e.g., numbers) is too simple, but just two
    kinds (numbers and booleans) gives us enough material to tell an
    interesting story.

    The language definition is completely routine. *)

(* ================================================================= *)
(** ** Syntax *)

(** Here is the syntax, informally:

    t ::= tru
        | fls
        | test t then t else t
        | zro
        | scc t
        | prd t
        | iszro t

    And here it is formally: *)

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

(** _Values_ are [tru], [fls], and numeric values... *)

Inductive bvalue : tm -> Prop :=
  | bv_tru : bvalue tru
  | bv_fls : bvalue fls.

Inductive nvalue : tm -> Prop :=
  | nv_zro : nvalue zro
  | nv_scc : forall t, nvalue t -> nvalue (scc t).

Definition value (t : tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue : core.
Hint Unfold value : core.

(* ================================================================= *)
(** ** Operational Semantics *)

(** Here is the single-step relation, first informally...

                   -------------------------------                  (ST_TestTru)
                   test tru then t1 else t2 --> t1

                   -------------------------------                  (ST_TestFls)
                   test fls then t1 else t2 --> t2

                               t1 --> t1'
            ----------------------------------------------------       (ST_Test)
            test t1 then t2 else t3 --> test t1' then t2 else t3

                             t1 --> t1'
                         ------------------                             (ST_Scc)
                         scc t1 --> scc t1'

                           ---------------                           (ST_PrdZro)
                           prd zro --> zro

                         numeric value v
                        -------------------                          (ST_PrdScc)
                        prd (scc v) --> v

                              t1 --> t1'
                         ------------------                             (ST_Prd)
                         prd t1 --> prd t1'

                          -----------------                        (ST_IszroZro)
                          iszro zro --> tru

                         numeric value v
                      ---------------------                       (ST_IszroScc)
                      iszro (scc v) --> fls

                            t1 --> t1'
                       ----------------------                         (ST_Iszro)
                       iszro t1 --> iszro t1'
*)

(** ... and then formally: *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_TestTru : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFls : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)
  | ST_Scc : forall t1 t1',
      t1 --> t1' ->
      (scc t1) --> (scc t1')
  | ST_PrdZro :
      (prd zro) --> zro
  | ST_PrdScc : forall v,
      nvalue v ->
      (prd (scc v)) --> v
  | ST_Prd : forall t1 t1',
      t1 --> t1' ->
      (prd t1) --> (prd t1')
  | ST_IszroZro :
      (iszro zro) --> tru
  | ST_IszroScc : forall v,
       nvalue v ->
      (iszro (scc v)) --> fls
  | ST_Iszro : forall t1 t1',
      t1 --> t1' ->
      (iszro t1) --> (iszro t1')

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

(** Notice that the [step] relation doesn't care about whether the
    expression being stepped makes global sense -- it just checks that
    the operation in the _next_ reduction step is being applied to the
    right kinds of operands.  For example, the term [scc tru] cannot
    take a step, but the almost as obviously nonsensical term

       scc (test tru then tru else tru)

    can take a step (once, before becoming stuck). *)

(* ================================================================= *)
(** ** Normal Forms and Values *)

(** The first interesting thing to notice about this [step] relation
    is that the strong progress theorem from the [Smallstep] chapter
    fails here.  That is, there are terms that are normal forms (they
    can't take a step) but not values (because we have not included
    them in our definition of possible "results of reduction").  Such
    terms are _stuck_. *)

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck : core.

(** **** Exercise: 2 stars, standard (some_term_is_stuck)  *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (test zro zro zro). split.
  - (* normal form *)
    intro. inversion H. inversion H0. inversion H5.
  - (* not value *)
    intro. inversion H. inversion H0. inversion H0.
Qed.

(** [] *)

(** However, although values and normal forms are _not_ the same in
    this language, the set of values is a subset of the set of normal
    forms.  This is important because it shows we did not accidentally
    define things so that some value could still take a step. *)

(** **** Exercise: 3 stars, standard (value_is_nf)  *)
Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  unfold value, step_normal_form.
  intros. intro.
  destruct H0.
  destruct H.
  - inversion H; subst; inversion H0.
  - generalize dependent x. induction H; subst.
    + intros. inversion H0.
    + intros. inversion H0; subst.
      apply IHnvalue in H2. inversion H2.
Qed.

(** (Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways.)

    [] *)
Lemma value_is_nf' : forall t,
  value t -> step_normal_form t.
Proof.
  unfold value, step_normal_form.
  intros.
  intros. intro.
  destruct H0.
  destruct H.
  - inversion H; subst; inversion H0.
  - induction H0; subst; inversion H; subst.
    apply IHstep; apply H2.
Qed.

(** **** Exercise: 3 stars, standard, optional (step_deterministic)

    Use [value_is_nf] to show that the [step] relation is also
    deterministic. *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros; inversion Hy2; clear Hy2; subst;
         try reflexivity;
         try (inversion H3; fail);
         try (inversion H0; fail);
         try (inversion Hy1; fail);
         try (f_equal; eauto; fail).
  - assert (Hv: value (scc v)) by auto; apply value_is_nf in Hv.
    unfold step_normal_form in Hv. exfalso. apply Hv. eexists. apply H1.
  - assert (Hv: value (scc y2)) by auto; apply value_is_nf in Hv.
    unfold step_normal_form in Hv. exfalso. apply Hv. eexists. apply Hy1.
  - assert (Hv: value (scc v)) by auto; apply value_is_nf in Hv.
    unfold step_normal_form in Hv. exfalso. apply Hv. eexists. apply H1.
  - assert (Hv: value (scc v)) by auto; apply value_is_nf in Hv.
    unfold step_normal_form in Hv. exfalso. apply Hv. eexists. apply Hy1.
Qed.

(** [] *)

(* ================================================================= *)
(** ** Typing *)

(** The next critical observation is that, although this
    language has stuck terms, they are always nonsensical, mixing
    booleans and numbers in a way that we don't even _want_ to have a
    meaning.  We can easily exclude such ill-typed terms by defining a
    _typing relation_ that relates terms to the types (either numeric
    or boolean) of their final results.  *)

Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.

(** In informal notation, the typing relation is often written
    [|- t \in T] and pronounced "[t] has type [T]."  The [|-] symbol
    is called a "turnstile."  Below, we're going to see richer typing
    relations where one or more additional "context" arguments are
    written to the left of the turnstile.  For the moment, the context
    is always empty.


                           ---------------                     (T_Tru)
                           |- tru \in Bool

                          ---------------                      (T_Fls)
                          |- fls \in Bool

             |- t1 \in Bool    |- t2 \in T    |- t3 \in T
             --------------------------------------------     (T_Test)
                    |- test t1 then t2 else t3 \in T

                             --------------                    (T_Zro)
                             |- zro \in Nat

                            |- t1 \in Nat
                          -----------------                    (T_Scc)
                          |- scc t1 \in Nat

                            |- t1 \in Nat
                          -----------------                    (T_Prd)
                          |- prd t1 \in Nat

                            |- t1 \in Nat
                        --------------------                 (T_IsZro)
                        |- iszro t1 \in Bool
*)

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_Tru :
       |- tru \in Bool
  | T_Fls :
       |- fls \in Bool
  | T_Test : forall t1 t2 t3 T,
       |- t1 \in Bool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- test t1 t2 t3 \in T
  | T_Zro :
       |- zro \in Nat
  | T_Scc : forall t1,
       |- t1 \in Nat ->
       |- scc t1 \in Nat
  | T_Prd : forall t1,
       |- t1 \in Nat ->
       |- prd t1 \in Nat
  | T_Iszro : forall t1,
       |- t1 \in Nat ->
       |- iszro t1 \in Bool

where "'|-' t '\in' T" := (has_type t T).

Hint Constructors has_type : core.

Example has_type_1 :
  |- test fls zro (scc zro) \in Nat.
Proof.
  apply T_Test.
  - apply T_Fls.
  - apply T_Zro.
  - apply T_Scc. apply T_Zro.
Qed.

(** (Since we've included all the constructors of the typing relation
    in the hint database, the [auto] tactic can actually find this
    proof automatically.) *)

(** It's important to realize that the typing relation is a
    _conservative_ (or _static_) approximation: it does not consider
    what happens when the term is reduced -- in particular, it does
    not calculate the type of its normal form. *)

Example has_type_not :
  ~ ( |- test fls zro tru \in Bool ).
Proof.
  intros Contra. solve_by_inverts 2.  Qed.

(** **** Exercise: 1 star, standard, optional (scc_hastype_nat__hastype_nat)  *)
Example scc_hastype_nat__hastype_nat : forall t,
  |- scc t \in Nat ->
  |- t \in Nat.
Proof. intros. inversion H. auto. Qed.

(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Canonical forms *)

(** The following two lemmas capture the fundamental property that the
    definitions of boolean and numeric values agree with the typing
    relation. *)

Lemma bool_canonical : forall t,
  |- t \in Bool -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn].
  - assumption.
  - destruct Hn as [ | Hs].
    + inversion HT.
    + inversion HT.
Qed.

Lemma nat_canonical : forall t,
  |- t \in Nat -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn].
  - inversion Hb; subst; inversion HT.
  - assumption.
Qed.

(* ================================================================= *)
(** ** Progress *)

(** The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are not stuck -- or conversely, if a
    term is well typed, then either it is a value or it can take at
    least one step.  We call this _progress_. *)

(** **** Exercise: 3 stars, standard (finish_progress)  *)
Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t --> t'.

(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the parts we've given of the informal proof in the
    following exercise before starting -- this will save you a lot of
    time.) *)
Proof.
  intros t T HT.
  induction HT; auto.
  (* The cases that were obviously values, like T_Tru and
     T_Fls, were eliminated immediately by auto *)
  - (* T_Test *)
    right. destruct IHHT1.
    + (* t1 is a value *)
    apply (bool_canonical t1 HT1) in H.
    destruct H.
      * exists t2. auto.
      * exists t3. auto.
    + (* t1 can take a step *)
      destruct H as [t1' H1].
      exists (test t1' t2 t3). auto.
  - (* |- t1 in Nat -> suc *)
    destruct IHHT.
    + left. right.
      apply (nat_canonical t1 HT) in H.
      constructor. apply H.
    + right. inversion H as [t'].
      eexists. constructor. apply H0.
  - (* |- t1 in Nat -> prd *)
    destruct IHHT.
    + apply (nat_canonical t1 HT) in H.
      inversion H; subst; clear H.
      * right. eexists. constructor.
      * right. eexists. constructor. apply H0.
    + right. inversion H as [t'].
      eexists. constructor. apply H0.
  - (* |- t in Nat -> iszro *)
    destruct IHHT.
    + apply (nat_canonical t1 HT) in H.
      right. inversion H; subst; clear H.
      * eexists. constructor.
      * eexists. constructor. apply H0.
    + destruct H. right. eexists. constructor.  apply H.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (finish_progress_informal)

    Complete the corresponding informal proof: *)

(** _Theorem_: If [|- t \in T], then either [t] is a value or else
    [t --> t'] for some [t']. *)

(** _Proof_: By induction on a derivation of [|- t \in T].

    - If the last rule in the derivation is [T_Test], then [t = test t1
      then t2 else t3], with [|- t1 \in Bool], [|- t2 \in T] and [|- t3
      \in T].  By the IH, either [t1] is a value or else [t1] can step
      to some [t1'].

      - If [t1] is a value, then by the canonical forms lemmas
        and the fact that [|- t1 \in Bool] we have that [t1]
        is a [bvalue] -- i.e., it is either [tru] or [fls].
        If [t1 = tru], then [t] steps to [t2] by [ST_TestTru],
        while if [t1 = fls], then [t] steps to [t3] by
        [ST_TestFls].  Either way, [t] can step, which is what
        we wanted to show.

      - If [t1] itself can take a step, then, by [ST_Test], so can
        [t].

    - If the last rule in the derivation is [T_Scc], then [t = scc t1],
      with [|- t1 \in Nat]. By the IH, either [t1] is a value or else [t1] can
      step to some [t1'].

      - If [t1] is a value, then by the canonical forms lemmas and the fact
        that [|- t1 \in Nat] we have that t1 is a nvalue.
        Therefore [scc t1] is also an nvalue by nv_scc.
        Therefore [scc t1] is a value.
      - If [t1 --> t1'], then by ST_Scc we can conclude
        that [scc t1 --> scc t1] based on [t1 --> t']

    - If the last rule is [T_Prd], then [t = prd t1], with [|- t1 \in Nat].
      By IH, either [t1] is a value or [t1] can step to some [t1'].

      - If [t1] is a value, then by the canonical forms lemmas and the fact
        that [|- t1 \in Nat] we have that [t1] is a nvalue. Therefore,
        either [t1 = zro] or [t1 = scc x].
        - if [t1 = zro], we can show that [prd zro] steps to [zro] by ST_PrdZro.
        - if [t1 = scc x], we can show that [prd (scc x)]
          steps to [x] by ST_PrdScc.

      - If [t1] can step to [t1']. We can show that [prd t1] steps to [prd t1']
        by ST_Prd.

    - If the last rule is [T_IsZro], then [t = iszro t1], with [|- t1 \in Nat].
      By IH, either [t1] is a value or [t1] can step to some [t1'].

      - If [t1] is a value, it must be either [zro] or [scc x].
        * If [t1 = zro], we can show [iszro zro] can step to [tru] by ST_IszroZro.
        * If [t1 = scc x], we can show [iszro (scc x)] steps to [fls] by
          ST_IszroScc.

      - If [t1] can step into [t1']. We can use ST_Iszro to claim that
        [iszro t1] can step to [iszro t1'].
Qed.
 *)
(* Do not modify the following line: *)
Definition manual_grade_for_finish_progress_informal : option (nat*string) := None.
(** [] *)

(** This theorem is more interesting than the strong progress theorem
    that we saw in the [Smallstep] chapter, where _all_ normal forms
    were values.  Here a term can be stuck, but only if it is ill
    typed. *)

(* ================================================================= *)
(** ** Type Preservation *)

(** The second critical property of typing is that, when a well-typed
    term takes a step, the result is also a well-typed term. *)

(** **** Exercise: 2 stars, standard (finish_preservation)  *)
Theorem preservation : forall t t' T,
  |- t \in T ->
  t --> t' ->
  |- t' \in T.

(** Complete the formal proof of the [preservation] property.  (Again,
    make sure you understand the informal proof fragment in the
    following exercise first.) *)

Proof.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
         (* every case needs to introduce a couple of things *)
         intros t' HE;
         (* and we can deal with several impossible
            cases all at once *)
         try solve_by_invert.
    - (* T_Test *) inversion HE; subst; clear HE.
      + (* ST_TESTTru *) assumption.
      + (* ST_TestFls *) assumption.
      + (* ST_Test *) apply T_Test; try assumption.
        apply IHHT1; assumption.
    - inversion HE; subst. constructor. apply IHHT. apply H0.
    - inversion HE; subst.
      + apply HT.
      + inversion HT. apply H1.
      + constructor. apply IHHT in H0. apply H0.
    - inversion HE; subst; clear HE.
      + constructor.
      + constructor.
      + constructor. apply IHHT. apply H0.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (finish_preservation_informal)

    Complete the following informal proof: *)

(** _Theorem_: If [|- t \in T] and [t --> t'], then [|- t' \in T]. *)

(** _Proof_: By induction on a derivation of [|- t \in T].

    - If the last rule in the derivation is [T_Test], then [t = test t1
      then t2 else t3], with [|- t1 \in Bool], [|- t2 \in T] and [|- t3
      \in T].

      Inspecting the rules for the small-step reduction relation and
      remembering that [t] has the form [test ...], we see that the
      only ones that could have been used to prove [t --> t'] are
      [ST_TestTru], [ST_TestFls], or [ST_Test].

      - If the last rule was [ST_TestTru], then [t' = t2].  But we
        know that [|- t2 \in T], so we are done.

      - If the last rule was [ST_TestFls], then [t' = t3].  But we
        know that [|- t3 \in T], so we are done.

      - If the last rule was [ST_Test], then [t' = test t1' then t2
        else t3], where [t1 --> t1'].  We know [|- t1 \in Bool] so,
        by the IH, [|- t1' \in Bool].  The [T_Test] rule then gives us
        [|- test t1' then t2 else t3 \in T], as required.

    - If the last rule in the derivation is [T_Scc], then [t = scc t1].
      with [|- t1 \in Nat] and [scc t1 --> t']. By ST_Scc on [scc t1 --> t'],
      [t' = scc x] for some x such that [t1 --> x]. By IH this implies
      [x \in Nat], which in turn implies [t' = scc x \in Nat] by T_Scc.

    - If the last rule in the derivation is [T_Prd], then [t = prd t1].
      with [|- t1 \in Nat] and [prd t1 --> t']. There are three cases where
      [prd t1 --> t'] can hold, we will do a case analysis.

      - [t1 = zro], thus [prd zro --> zro = t']. And we have [|- zro \in Nat]
        by T_Zro.
      - [t1 = scc t1'] for some t1', thus [prd (scc t1') --> t1' = t'].
        And we have [|- zro \in Nat] by T_Zro.
        Because [|- suc t' \in Nat] we have [|- t' \in Nat] by T_Scc.
      - [prd t1 --> prd t1'] and [t1 --> t1']. We need to prove [|- prd t1' \in Nat].
        Apply the IH to [t1 --> t1'], we get [t' \in Nat]. Then by T_Prd,
        we can show that [prd t1' \in Nat].
    - If the last rule is [T_IsZro],  Then [t = iszro t1], with
      [|- t1 \in Nat] and [iszro t1 --> t']. There are three ways for
      [iszro t1 --> t'] to hold, we will do a case analysis.

      - [t1 = zro] and [t' = tru]. It's trivial to prove [|- tru \in Bool] by
        T_Tru.
      - [t1 = scc x] for some x and [t' = fls]. It's trivial to prove
        [|- fls \in Bool] by T_Fls.
      - [t1 --> t1'] for some [t1']. We need to prove [|- iszro t1' \in Bool].
        apply IH, we get [|- t1' \in Nat]. Then by T_IsZro we can show
        [|- iszro t1' \in Bool]

Qed.

*)
(* Do not modify the following line: *)
Definition manual_grade_for_finish_preservation_informal : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard (preservation_alternate_proof)

    Now prove the same property again by induction on the
    _evaluation_ derivation instead of on the typing derivation.
    Begin by carefully reading and thinking about the first few
    lines of the above proofs to make sure you understand what
    each one is doing.  The set-up for this proof is similar, but
    not exactly the same. *)

Theorem preservation' : forall t t' T,
  |- t \in T ->
  t --> t' ->
  |- t' \in T.
Proof with eauto.
  intros.
  generalize dependent t'.
  induction H; intros t' Ht;
         try (inversion Ht; fail);
         try (inversion Ht; subst; auto; fail).
  inversion Ht; subst; auto.
  inversion H. auto.
Qed.

(** [] *)

(** The preservation theorem is often called _subject reduction_,
    because it tells us what happens when the "subject" of the typing
    relation is reduced.  This terminology comes from thinking of
    typing statements as sentences, where the term is the subject and
    the type is the predicate. *)

(* ================================================================= *)
(** ** Type Soundness *)

(** Putting progress and preservation together, we see that a
    well-typed term can never reach a stuck state.  *)

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |- t \in T ->
  t -->* t' ->
  ~(stuck t').
Print stuck. (* stuck = fun t : tm => step_normal_form t /\ ~ value t : tm -> Prop *)
Proof.
  intros t t' T HT P. induction P; intros [R S].
  - apply progress in HT. destruct HT; auto.
  - apply IHP.
    + apply preservation with (t := x); auto.
    + unfold stuck. split; auto.
Qed.

(* ================================================================= *)
(** ** Additional Exercises *)

(** **** Exercise: 2 stars, standard, especially useful (subject_expansion)

    Having seen the subject reduction property, one might
    wonder whether the opposity property -- subject _expansion_ --
    also holds.  That is, is it always the case that, if [t --> t']
    and [|- t' \in T], then [|- t \in T]?  If so, prove it.  If
    not, give a counter-example.  (You do not need to prove your
    counter-example in Coq, but feel free to do so.)

My original answer: yes of course why not, lemme prove that.

(I changed my answer after failed attempt - see below)

 *)

Definition subject_expansion := forall t t' T,
  t --> t' ->
  |- t' \in T ->
  |- t \in T.

Theorem subject_expansion_attempt : subject_expansion.
Proof.
  unfold subject_expansion.
  intros.
  generalize dependent t.
  induction H0; intros; try auto;
         try (inversion H; auto; fail).
  - inversion H; subst; eauto.
    + constructor. auto. auto. auto.

      (*
  So I was supposed to prove this but I can't! t2 doesn't have to be Bool at all.

  H : test tru tru t2 --> tru
  ============================
  |- t2 \in Bool

 So this is a counterexample, I'll now turn to prove the opposite.
 *)
Abort.

Theorem subject_expansion_does_not_hold : ~subject_expansion.
Proof.
  unfold subject_expansion.
  intro.
  specialize H with
      (t := test tru tru zro)
      (t' := tru)
      (T := Bool).
  assert (test tru tru zro --> tru) by auto.
  apply H in H0; clear H.
  (* prove for contradiction in: |- test tru tru zro \in Bool *)
  inversion H0; subst. inversion H6.
  (* prove for |- tru \in Bool *)
  auto.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_subject_expansion : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (variation1)

    Suppose that we add this new rule to the typing relation:

      | T_SccBool : forall t,
           |- t \in Bool ->
           |- scc t \in Bool

   Which of the following properties remain true in the presence of
   this rule?  For each one, write either "remains true" or
   else "becomes false." If a property becomes false, give a
   counterexample.
      - Determinism of [step]
        remains true, because we are not changing the stepping rule.

      - Progress
        becomes false.
        counterexample: (scc fls)
        justification:

        - |- scc fls \in Bool by T_SccBool
        - scc fls is not a value
        - scc fls cannot be stepped further

      - Preservation
        remains true.
        justification:

        This rule adds a new type of well-typed expression that's irreducible
        (not step further). But all reducible expression and well-typed
        expression remains the same. The condition of preservation only applies
        to those that are both well-typed (|- t \in T) and reducible (t --> t').
        Therefore this new rule doesn't affect preservation rule.
 *)

(* Do not modify the following line: *)
Definition manual_grade_for_variation1 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (variation2)

    Suppose, instead, that we add this new rule to the [step] relation:

      | ST_Funny1 : forall t2 t3,
           (test tru t2 t3) --> t3

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

      - Determinism of [step]
        becomes false. counterexample: [test tru tru fls]

        It can step into [tru] by ST_TestTru, or
        step into [fls] by ST_Funny1.

      - Progress
        remains true.
        justification:

        This rule is an addition to reduce some expression further.
        Thus it's only making the progress property weaker.
        Therefore progress property should remain true.

      - Preservation
        remains true.
        justification:

        A  [|- test tru t2 t3 \in T] expression requires both [|- t2 \in T]
        and [|- t3 \in T]. Therefore, the two derivation of
        [test tru t2 t3], which are [t2] (ST_TestTru) and [t3] (ST_Funny1)
        will still both [\in T].

*)
(* Do not modify the following line: *)
Definition manual_grade_for_variation2 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (variation3)

    Suppose instead that we add this rule:

      | ST_Funny2 : forall t1 t2 t2' t3,
           t2 --> t2' ->
           (test t1 t2 t3) --> (test t1 t2' t3)

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

      - Determinism of [step]
        becomes false.

        test fls (iszro zro) fls can be reduced in two ways:
        - fls (by ST_TestFls)
        - test fls tru fls (by ST_Funny2)

      - Progress
        remains true.
        justification:

        This rule is an addition to reduce some expression further.
        Thus it's only making the progress property weaker.
        Therefore progress property should remain true.

      - Preservation
        remains true.
        justification:

        [|- test t1 t2 t3 \in T] requires [|- t1 \in Bool] and
        [|- t2, t3 \in T]. Therefore, the new derivation (ST_Funny1) of
        [test t1 t2 t3], which is [test t2' t3], will still be
        of type [\in T].
*)
(** [] *)

(** **** Exercise: 2 stars, standard, optional (variation4)

    Suppose instead that we add this rule:

      | ST_Funny3 :
          (prd fls) --> (prd (prd fls))

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

      - Determinism of [step]
        remains true. Because ST_Funny3 doesn't introduce
        any new way to step an existing step-able expression.

      - Progress
        remains true.
        justification:

        [prd fls] is not well-typed based on existing
        typing rules. Therefore it doesn't satisfy the progress's typing
        condition.

      - Preservation
        remains true, because [prd fls] is not well-typed.
*)
(** [] *)

(** **** Exercise: 2 stars, standard, optional (variation5)

    Suppose instead that we add this rule:

      | T_Funny4 :
            |- zro \in Bool

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

      - Determinism of [step]
        remains true. Because adding a typing rule doesn't change
        anything about stepping.

      - Progress
        becomes false. [test zro tru fls] is well-typed but irreducible.

      - Preservation
        remains true. It looks like it's true because I can't seem to find
        a counterexample. but I also isn't very sure of this. So I'll
        try formally prove it.
 *)
Module variation5.

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_Tru :
       |- tru \in Bool
  | T_Fls :
       |- fls \in Bool
  | T_Test : forall t1 t2 t3 T,
       |- t1 \in Bool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- test t1 t2 t3 \in T
  | T_Zro :
       |- zro \in Nat
  | T_Scc : forall t1,
       |- t1 \in Nat ->
       |- scc t1 \in Nat
  | T_Prd : forall t1,
       |- t1 \in Nat ->
       |- prd t1 \in Nat
  | T_Iszro : forall t1,
       |- t1 \in Nat ->
       |- iszro t1 \in Bool
  | T_Funny4 : |- zro \in Bool

where "'|-' t '\in' T" := (has_type t T).

Theorem preservation' : forall t t' T,
  |- t \in T ->
  t --> t' ->
  |- t' \in T.
Proof with eauto.
  intros.
  generalize dependent t'.
  induction H; intros t' Ht;
         try (inversion Ht; fail);
         try (inversion Ht; subst; auto; fail).
  - inversion Ht; subst; auto. constructor; auto.
  - inversion Ht; subst; constructor; apply IHhas_type; apply H1; subst.
  - inversion Ht; subst; try constructor.
    + inversion H1. constructor. subst.
      inversion H; subst. apply H3.
    + apply IHhas_type. apply H1.
  - inversion Ht; subst; constructor.
    apply IHhas_type. apply H1.
Qed.

(* it seems that preservation indeed remains true. *)
End variation5.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (variation6)

    Suppose instead that we add this rule:

      | T_Funny5 :
            |- prd zro \in Bool

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

      - Determinism of [step]
        remains true. Because adding a typing rule doesn't change
        anything about stepping.

      - Progress
        remains true. Because even though [prd zro]
        can now be of both \Nat and \Bool type, it can always step to
        zro.

      - Preservation
        becomes false. [|- test (prd zro) zro zro \in Nat] is well typed,
        but it's derivation [test zro zro zro] is not well typed.

*)
(** [] *)

(** **** Exercise: 3 stars, standard, optional (more_variations)

    Make up some exercises of your own along the same lines as
    the ones above.  Try to find ways of selectively breaking
    properties -- i.e., ways of changing the definitions that
    break just one of the properties and leave the others alone.

    Break determinism only:

    | ST_Funny : test tru tru tru --> fls.

    Break progress only:

    | T_Funny : forall t1 t2, |- test zro t1 t2 \in Nat

    Break preservation only:

    | T_Funny : |- scc (prd zro) \in Bool

*)

(** **** Exercise: 1 star, standard (remove_prdzro)

    The reduction rule [ST_PrdZro] is a bit counter-intuitive: we
    might feel that it makes more sense for the predecessor of [zro] to
    be undefined, rather than being defined to be [zro].  Can we
    achieve this simply by removing the rule from the definition of
    [step]?  Would doing so create any problems elsewhere?

- determinism: remains true.
- progress: becomes false. now (prd zro) is neither a value nor steppable.
- preservation: remains true.

 *)

(* Do not modify the following line: *)
Definition manual_grade_for_remove_predzro : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (prog_pres_bigstep)

    Suppose our evaluation relation is defined in the big-step style.
    State appropriate analogs of the progress and preservation
    properties. (You do not need to prove them.)

    Can you see any limitations of either of your properties?  Do they
    allow for nonterminating commands?  Why might we prefer the
    small-step semantics for stating preservation and progress?

 *)

Module bigstep.


Inductive big_step : tm -> tm -> Prop :=
  | BST_Id : forall t,
    value t -> t ==> t
  | BST_TestTru : forall t1 t2 t3 t2',
    t1 ==> tru ->
    t2 ==> t2' ->
    (test t1 t2 t3) ==> t2'
  | BST_TestFls : forall t1 t2 t3 t3',
    t1 ==> fls ->
    t3 ==> t3' ->
    (test t1 t2 t3) ==> t3'
  | BST_Scc : forall t1 t1',
      t1 ==> t1' ->
      (* this condition is necessary, or else we would allow non-nat expression
         to reduce *)
      nvalue t1' ->
      scc t1 ==> scc t1'
  | BST_PrdZro :
      (prd zro) ==> zro
  | BST_PrdScc : forall t t',
      t ==> t' ->
      (prd (scc t)) ==> t'
  | BST_IszroZro : forall t,
      t ==> zro ->
      (iszro t) ==> tru
  | BST_IszroScc : forall t n,
      t ==> scc n ->
      (iszro (scc n)) ==> fls
where "t '==>' t'" := (big_step t t').

Hint Constructors big_step : core.

Definition bigstep_always_value: forall t t',
  t ==> t' -> value t'.
Proof.
  intros.
  induction H; auto.
Qed.

Definition bigstep_progress: forall t T,
  |- t \in T -> value t \/ (exists t', t ==> t').
Proof.
  intros.
  induction H; subst; auto.

  - right. destruct IHhas_type1.
    + apply (bool_canonical t1 H) in H2. inversion H2; subst; clear H2.
      * inversion IHhas_type2; subst.
        -- exists t2. auto.
        -- inversion H2. exists x. auto.
      * inversion IHhas_type3; subst.
        -- exists t3. auto.
        -- inversion H2. exists x. auto.
    + inversion H2. assert (t1 ==> x) by auto.
      apply (bigstep_always_value t1 x) in H3.


      (*

Here I'm stuck:


  t1, t2, t3 : tm
  T : ty
  H : |- t1 \in Bool
  H0 : |- t2 \in T
  H1 : |- t3 \in T
  H2 : exists t' : tm, t1 ==> t'
  IHhas_type2 : value t2 \/ (exists t' : tm, t2 ==> t')
  IHhas_type3 : value t3 \/ (exists t' : tm, t3 ==> t')
  x : tm
  H3 : value x
  H4 : t1 ==> x
  ============================
  exists t' : tm, test t1 t2 t3 ==> t'


I need a rule to state that [|- x \in Bool] (so I can use canonical form of bool
to assert it as bvalue). From the context I only have two related hypothesis:

-   H : |- t1 \in Bool
-   H4 : t1 ==> x

So this means it ends up requiring the preservation property to prove the
progress property.

Of course, here I may not need a full version of preservation property to
continue the progress proof, only proving preservation property
for some specific terms may already work.

I haven't tried proving the preservation properties first, but I guess
it may end up having circular dependency to progress as well.


As of the concern to "nonterminating" command in the problem, I think it is
easy to tackle and have tackled it in my definition for bigstep. The key is to
only allow values to step into themselves, ie. [value t ==> t]. Then we can
assert bigstep always terminates at a value.

 *)
Abort.
End bigstep.

(* Do not modify the following line: *)
Definition manual_grade_for_prog_pres_bigstep : option (nat*string) := None.
(** [] *)

(* 2020-09-09 21:08 *)
