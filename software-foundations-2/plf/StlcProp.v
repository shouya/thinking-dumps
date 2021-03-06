(** * StlcProp: Properties of STLC *)

Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Stlc.
From PLF Require Import Smallstep.
Module STLCProp.
Import STLC.

(** In this chapter, we develop the fundamental theory of the Simply
    Typed Lambda Calculus -- in particular, the type safety
    theorem. *)

(* ################################################################# *)
(** * Canonical Forms *)

(** As we saw for the very simple language in the [Types]
    chapter, the first step in establishing basic properties of
    reduction and types is to identify the possible _canonical
    forms_ (i.e., well-typed closed values) belonging to each type.
    For [Bool], these are again the boolean values [true] and [false];
    for arrow types, they are lambda-abstractions.  *)

Lemma canonical_forms_bool : forall t,
  empty |- t \in Bool ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
Proof.
  intros t HT HVal.
  destruct HVal; auto.
  inversion HT.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (T1 -> T2) ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal; inversion HT; subst.
  exists x0, t1. reflexivity.
Qed.

(* ################################################################# *)
(** * Progress *)

(** The _progress_ theorem tells us that closed, well-typed
    terms are not stuck: either a well-typed term is a value, or it
    can take a reduction step.  The proof is a relatively
    straightforward extension of the progress proof we saw in the
    [Types] chapter.  We give the proof in English first, then
    the formal version. *)

Theorem progress : forall t T,
  empty |- t \in T ->
  value t \/ exists t', t --> t'.

(** _Proof_: By induction on the derivation of [|- t \in T].

    - The last rule of the derivation cannot be [T_Var], since a
      variable is never well typed in an empty context.

    - The [T_True], [T_False], and [T_Abs] cases are trivial, since in
      each of these cases we can see by inspecting the rule that [t]
      is a value.

    - If the last rule of the derivation is [T_App], then [t] has the
      form [t1 t2] for some [t1] and [t2], where [|- t1 \in T2 -> T]
      and [|- t2 \in T2] for some type [T2].  The induction hypothesis
      for the first subderivation says that either [t1] is a value or
      else it can take a reduction step.

        - If [t1] is a value, then consider [t2], which by the
          induction hypothesis for the second subderivation must also
          either be a value or take a step.

            - Suppose [t2] is a value.  Since [t1] is a value with an
              arrow type, it must be a lambda abstraction; hence [t1
              t2] can take a step by [ST_AppAbs].

            - Otherwise, [t2] can take a step, and hence so can [t1
              t2] by [ST_App2].

        - If [t1] can take a step, then so can [t1 t2] by [ST_App1].

    - If the last rule of the derivation is [T_If], then [t = if
      t1 then t2 else t3], where [t1] has type [Bool].  The first IH
      says that [t1] either is a value or takes a step.

        - If [t1] is a value, then since it has type [Bool] it must be
          either [true] or [false].  If it is [true], then [t] steps to
          [t2]; otherwise it steps to [t3].

        - Otherwise, [t1] takes a step, and therefore so does [t] (by
          [ST_If]). *)
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma; auto.
  (* auto solves all three cases in which t is a value *)
  - (* T_Var *)
    (* contradictory: variables cannot be typed in an
       empty context *)
    discriminate H.

  - (* T_App *)
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a
       value or steps... *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t2 is also a value *)
        eapply canonical_forms_fun in Ht1; [|assumption].
        destruct Ht1 as [x [t0 H1]]. subst.
        exists (<{ [x:=t2]t0 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists (<{t1 t2'}>)...

    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists (<{t1' t2}>)...

  - (* T_If *)
    right. destruct IHHt1...

    + (* t1 is a value *)
      destruct (canonical_forms_bool t1); subst; eauto.

    + (* t1 also steps *)
      destruct H as [t1' Hstp]. exists <{if t1' then t2 else t3}>...
Qed.

(** **** Exercise: 3 stars, advanced (progress_from_term_ind)

    Show that progress can also be proved by induction on terms
    instead of induction on typing derivations. *)

Theorem progress' : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t --> t'.
Proof.
  intros t.
  induction t; intros T Ht; auto.
  - (* variable *)
    inversion Ht; subst; clear Ht. inversion H1.
  - (* application *)
    right.
    inversion Ht; subst; clear Ht.
    assert (Ht1: value t1 \/ (exists t' : tm, t1 --> t')) by eauto.
    assert (Ht2: value t2 \/ (exists t' : tm, t2 --> t')) by eauto.
    clear IHt1 IHt2.
    destruct Ht2; destruct Ht1.
    (* case 1: t1 is value (lambda), t2 is value *)
    + apply (canonical_forms_fun _ _ _ H2) in H0.
      destruct H0 as [x [t1']]; subst.
      eauto.
    + (* case 2: t1 -> t', t2 is value *)
      destruct H0. eauto.
    + (* case 3: t1 is value, t2 -> t' *)
      destruct H. eauto.
    + (* case 3: t1 -> t', t2 -> t' *)
      destruct H0; destruct H; eauto.
  - (* if *)
    right.
    inversion Ht; subst; clear Ht.
    (* duplicate H3 *)
    assert (empty |- t1 \in Bool) by assumption.
    apply IHt1 in H3. destruct H3.
    + (* t1 is value *)
      apply (canonical_forms_bool _ H) in H0. destruct H0; subst; eauto.
    + (* t1 -> t' *)
      destruct H0. eauto.
Qed.

(** [] *)

(* ################################################################# *)
(** * Preservation *)

(** The other half of the type soundness property is the
    preservation of types during reduction.  For this part, we'll need
    to develop some technical machinery for reasoning about variables
    and substitution.  Working from top to bottom (from the high-level
    property we are actually interested in to the lowest-level
    technical lemmas that are needed by various cases of the more
    interesting proofs), the story goes like this:

      - The _preservation theorem_ is proved by induction on a typing
        derivation, pretty much as we did in the [Types] chapter.
        The one case that is significantly different is the one for
        the [ST_AppAbs] rule, whose definition uses the substitution
        operation.  To see that this step preserves typing, we need to
        know that the substitution itself does.  So we prove a...

      - _substitution lemma_, stating that substituting a (closed)
        term [s] for a variable [x] in a term [t] preserves the type
        of [t].  The proof goes by induction on the form of [t] and
        requires looking at all the different cases in the definition
        of substitition.  This time, for the variables case, we
        discover that we need to deduce from the fact that a term
        [s] has type S in the empty context the fact that [s] has
        type S in every context. For this we prove a...

      - _weakening_ lemma, showing that typing is preserved under
        "extensions" to the context [Gamma].

   To make Coq happy, of course, we need to formalize the story in the
   opposite order... *)

(* ================================================================= *)
(** ** The Weakening Lemma *)

(** Typing is preserved under "extensions" to the context [Gamma].
    (Recall the definition of "inclusion" from Maps.v.) *)

Print inclusion.
(*

inclusion =
fun (A : Type) (m m' : partial_map A) =>
forall (x : string) (v : A), m x = Some v -> m' x = Some v
     : forall A : Type, partial_map A -> partial_map A -> Prop

 *)
Lemma weakening : forall Gamma Gamma' t T,
     inclusion Gamma Gamma' ->
     Gamma  |- t \in T  ->
     Gamma' |- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using inclusion_update.
Qed.

(** The following simple corollary is useful below. *)

Lemma weakening_empty : forall Gamma t T,
     empty |- t \in T  ->
     Gamma |- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

(* ================================================================= *)
(** ** A Substitution Lemma *)

(** Now we come to the conceptual heart of the proof that reduction
    preserves types -- namely, the observation that _substitution_
    preserves types. *)

(** Formally, the so-called _substitution lemma_ says this:
    Suppose we have a term [t] with a free variable [x], and suppose
    we've assigned a type [T] to [t] under the assumption that [x] has
    some type [U].  Also, suppose that we have some other term [v] and
    that we've shown that [v] has type [U].  Then, since [v] satisfies
    the assumption we made about [x] when typing [t], we can
    substitute [v] for each of the occurrences of [x] in [t] and
    obtain a new term that still has type [T]. *)

(** _Lemma_: If [x|->U; Gamma |- t \in T] and [|- v \in U],
    then [Gamma |- [x:=v]t \in T]. *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  x |-> U ; Gamma |- t \in T ->
  empty |- v \in U   ->
  Gamma |- [x:=v]t \in T.

(** The substitution lemma can be viewed as a kind of "commutation
    property."  Intuitively, it says that substitution and typing can
    be done in either order: we can either assign types to the terms
    [t] and [v] separately (under suitable contexts) and then combine
    them using substitution, or we can substitute first and then
    assign a type to [ [x:=v] t ]; the result is the same either
    way.

    _Proof_: We show, by induction on [t], that for all [T] and
    [Gamma], if [x|->U; Gamma |- t \in T] and [|- v \in U], then
    [Gamma |- [x:=v]t \in T].

      - If [t] is a variable there are two cases to consider,
        depending on whether [t] is [x] or some other variable.

          - If [t = x], then from the fact that [x|->U; Gamma |- x \in
            T] we conclude that [U = T].  We must show that [[x:=v]x =
            v] has type [T] under [Gamma], given the assumption that
            [v] has type [U = T] under the empty context.  This
            follows from the weakening lemma.

          - If [t] is some variable [y] that is not equal to [x], then
            we need only note that [y] has the same type under [x|->U;
            Gamma] as under [Gamma].

      - If [t] is an abstraction [\y:S, t0], then [T = S->T1] and
        the IH tells us, for all [Gamma'] and [T0], that if [x|->U;
        Gamma' |- t0 \in T0], then [Gamma' |- [x:=v]t0 \in T0].
        Moreover, by inspecting the typing rules we see it must be
        the case that [y|->S; x|->U; Gamma |- t0 \in T1].

        The substitution in the conclusion behaves differently
        depending on whether [x] and [y] are the same variable.

        First, suppose [x = y].  Then, by the definition of
        substitution, [[x:=v]t = t], so we just need to show [Gamma |-
        t \in T].  Using [T_Abs], we need to show that [y|->S; Gamma
        |- t0 \in T1]. But we know [y|->S; x|->U; Gamma |- t0 \in T1],
        and the claim follows since [x = y].

        Second, suppose [x <> y]. Again, using [T_Abs],
        we need to show that [y|->S; Gamma |- [x:=v]t0 \in T1].
        Since [x <> y], we have
        [y|->S; x|->U; Gamma = x|->U; y|->S; Gamma]. So,
        we have [x|->U; y|->S; Gamma |- t0 \in T1]. Then, the
        the IH applies (taking [Gamma' = y|->S; Gamma]), giving us
        [y|->S; Gamma |- [x:=v]t0 \in T1], as required.

      - If [t] is an application [t1 t2], the result follows
        straightforwardly from the definition of substitution and the
        induction hypotheses.

      - The remaining cases are similar to the application case. *)

Proof.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into S.
    destruct (eqb_stringP x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
Qed.

(** One technical subtlety in the statement of the above lemma is that
    we assume [v] has type [U] in the _empty_ context -- in other
    words, we assume [v] is closed.  (Since we are using a simple
    definition of substition that is not capture-avoiding, it doesn't
    make sense to substitute non-closed terms into other terms.
    Fortunately, closed terms are all we need!)
 *)

(** **** Exercise: 3 stars, advanced (substitution_preserves_typing_from_typing_ind)

    Show that substitution_preserves_typing can also be
    proved by induction on typing derivations instead
    of induction on terms. *)
Lemma substitution_preserves_typing_from_typing_ind : forall Gamma x U t v T,
  x |-> U ; Gamma |- t \in T ->
  empty |- v \in U   ->
  Gamma |- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto;
  unfold update in *.


  - destruct (eqb_stringP x x0); subst.
    + rewrite t_update_eq in H. inversion H; subst.
      apply weakening_empty. apply Hv.
    + rewrite t_update_neq in H by auto.
      apply T_Var. apply H.

  - destruct (eqb_stringP x x0); subst.
    + rewrite t_update_shadow in *.
      constructor. apply Ht.
    + constructor. apply IHHt. unfold update in *.
      rewrite t_update_permute by auto.
      reflexivity.
Qed.

(** [] *)

(* ================================================================= *)
(** ** Main Theorem *)

(** We now have the ingredients we need to prove preservation: if a
    closed term [t] has type [T] and takes a step to [t'], then [t']
    is also a closed term with type [T].  In other words, the
    small-step reduction relation preserves types. *)

Theorem preservation : forall t t' T,
  empty |- t \in T  ->
  t --> t'  ->
  empty |- t' \in T.

(** _Proof_: By induction on the derivation of [|- t \in T].

    - We can immediately rule out [T_Var], [T_Abs], [T_True], and
      [T_False] as final rules in the derivation, since in each of these
      cases [t] cannot take a step.

    - If the last rule in the derivation is [T_App], then [t = t1 t2],
      and there are subderivations showing that [|- t1 \in T2->T] and
      [|- t2 \in T2] plus two induction hypotheses: (1) [t1 --> t1']
      implies [|- t1' \in T2->T] and (2) [t2 --> t2'] implies [|- t2'
      \in T2].  There are now three subcases to consider, one for
      each rule that could be used to show that [t1 t2] takes a step
      to [t'].

        - If [t1 t2] takes a step by [ST_App1], with [t1] stepping to
          [t1'], then, by the first IH, [t1'] has the same type as
          [t1] ([|- t1' \in T2->T]), and hence by [T_App] [t1' t2] has
          type [T].

        - The [ST_App2] case is similar, using the second IH.

        - If [t1 t2] takes a step by [ST_AppAbs], then [t1 =
          \x:T0,t0] and [t1 t2] steps to [[x0:=t2]t0]; the desired
          result now follows from the substitution lemma.

    - If the last rule in the derivation is [T_If], then [t = if
      t1 then t2 else t3], with [|- t1 \in Bool], [|- t2 \in T1], and
      [|- t3 \in T1], and with three induction hypotheses: (1) [t1 -->
      t1'] implies [|- t1' \in Bool], (2) [t2 --> t2'] implies [|- t2'
      \in T1], and (3) [t3 --> t3'] implies [|- t3' \in T1].

      There are again three subcases to consider, depending on how [t]
      steps.

        - If [t] steps to [t2] or [t3] by [ST_IfTrue] or
          [ST_IfFalse], the result is immediate, since [t2] and [t3]
          have the same type as [t].

        - Otherwise, [t] steps by [ST_If], and the desired
          conclusion follows directly from the first induction
          hypothesis. *)

Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2...
      inversion HT1...
Qed.

(** **** Exercise: 2 stars, standard, especially useful (subject_expansion_stlc)

    An exercise in the [Types] chapter asked about the _subject
    expansion_ property for the simple language of arithmetic and
    boolean expressions.  This property did not hold for that language,
    and it also fails for STLC.  That is, it is not always the case that,
    if [t --> t'] and [has_type t' T], then [empty |- t \in T].
    Show this by giving a counter-example that does _not involve
    conditionals_.

    You can state your counterexample informally in words, with a brief
    explanation. *)

(* Here's a counter example:

[if true then true else (\x : Bool, x)].


Let me prove it. *)

Lemma subject_expansion_stlc_does_not_hold :
  ~(forall t t' T, t --> t' -> empty |- t' \in T -> empty |- t \in T).
Proof.
  intro.
  specialize H with
      (t  := <{ if true then true else (\x : Bool, x) }>)
      (t' := <{ true }>)
      (T  := <{ Bool }>).
  assert (<{ if true then true else \ x : Bool, x }> --> <{ true }>) by auto.
  assert (empty |- true \in Bool) by auto.
  apply (H H0) in H1; clear H; clear H0; rename H1 into H.
  inversion H; subst.
  inversion H7.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_subject_expansion_stlc : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Type Soundness *)

(** **** Exercise: 2 stars, standard, optional (type_soundness)

    Put progress and preservation together and show that a well-typed
    term can _never_ reach a stuck state.  *)

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  empty |- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  - (* multi_refl *)
    apply progress in Hhas_type. destruct Hhas_type; congruence.
  - (* multi_step *)
    apply IHHmulti; auto.
    eapply preservation. apply Hhas_type. apply H.
Qed.
(** [] *)

(* ################################################################# *)
(** * Uniqueness of Types *)

(** **** Exercise: 3 stars, standard (unique_types)

    Another nice property of the STLC is that types are unique: a
    given term (in a given context) has at most one type. *)

Theorem unique_types : forall Gamma e T T',
  Gamma |- e \in T ->
  Gamma |- e \in T' ->
  T = T'.
Proof.
  intros Gamma e T T' HT HT'.
  generalize dependent T'.
  induction HT; intros T HT'; inversion HT'; subst; clear HT'; auto.
  - rewrite H in H2. inversion H2. reflexivity.
  - specialize IHHT with (T' := T0).
    apply IHHT in H4. subst. auto.
  - specialize IHHT2 with (T' := T3).
    apply IHHT2 in H4. subst. clear IHHT2.
    specialize IHHT1 with (T' := <{T3 -> T}>).
    apply IHHT1 in H2. inversion H2; subst; clear H2; clear IHHT1.
    reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Context Invariance *)

(** A standard technical lemma of a type system is
  _context invariance_. It states that typing is preserved
under "inessential changes" to the context [Gamma] -- in
particular, changes that do not affect any of the free
variables of the term. Next, we establish this property
for our system.  *)

(** First, we need to define the _free variables_ in a term --
i.e., variables that are used in the term in positions
that are _not_ in the scope of an enclosing function
abstraction binding a variable of the same name.

More technically, a variable [x] _appears free in_ a term _t_
if [t] contains some occurrence of [x] that is not under
an abstraction labeled [x]. For example:
  - [y] appears free, but [x] does not, in [\x:T->U, x y]
  - both [x] and [y] appear free in [(\x:T->U, x y) x]
  - no variables appear free in [\x:T->U, \y:T, x y]

  Formally: *)

Inductive appears_free_in (x : string) : tm -> Prop :=
  | afi_var : appears_free_in x <{x}>
  | afi_app1 : forall t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{t1 t2}>
  | afi_app2 : forall t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{t1 t2}>
  | afi_abs : forall y T1 t1,
      y <> x  ->
      appears_free_in x t1 ->
      appears_free_in x <{\y:T1, t1}>
  | afi_if1 : forall t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x <{if t1 then t2 else t3}>
  | afi_if2 : forall t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x <{if t1 then t2 else t3}>
  | afi_if3 : forall t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x <{if t1 then t2 else t3}>.

Hint Constructors appears_free_in : core.

(** The _free variables_ of a term are just the variables that appear
    free in it.  A term with no free variables is said to be
    _closed_. *)

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

(** An _open_ term is one that may contain free variables.  (I.e., every
    term is an open term; the closed terms are a subset of the open ones.
    "Open" precisely means "possibly containing free variables.") *)

(** **** Exercise: 1 star, standard (afi)

    In the space below, write out the rules of the [appears_free_in]
    relation in informal inference-rule notation.  (Use whatever
    notational conventions you like -- the point of the exercise is
    just for you to think a bit about the meaning of each rule.)
    Although this is a rather low-level, technical definition,
    understanding it is crucial to understanding substitution and its
    properties, which are really the crux of the lambda-calculus. *)

(*

Here it is:

|- free x x
free x t1 |- free x (t1 t2)
free x t2 |- free x (t1 t2)
free x t, x <> y |- free x (\y, t)
free x t1 |- free x (if t1 then t2 else t3)
free x t2 |- free x (if t1 then t2 else t3)
free x t3 |- free x (if t1 then t2 else t3)

 *)

(* Do not modify the following line: *)
Definition manual_grade_for_afi : option (nat*string) := None.
(** [] *)

(** Next, we show that if a variable [x] appears free in a term [t],
    and if we know [t] is well typed in context [Gamma], then it
    must be the case that [Gamma] assigns a type to [x]. *)

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.

(** _Proof_: We show, by induction on the proof that [x] appears free
    in [t], that, for all contexts [Gamma], if [t] is well typed under
    [Gamma], then [Gamma] assigns some type to [x].

    - If the last rule used is [afi_var], then [t = x], and from the
      assumption that [t] is well typed under [Gamma] we have
      immediately that [Gamma] assigns a type to [x].

    - If the last rule used is [afi_app1], then [t = t1 t2] and [x]
      appears free in [t1].  Since [t] is well typed under [Gamma], we
      can see from the typing rules that [t1] must also be, and the IH
      then tells us that [Gamma] assigns [x] a type.

    - Almost all the other cases are similar: [x] appears free in a
      subterm of [t], and since [t] is well typed under [Gamma], we
      know the subterm of [t] in which [x] appears is well typed under
      [Gamma] as well, and the IH gives us exactly the conclusion we
      want.

    - The only remaining case is [afi_abs].  In this case [t =
      \y:T1,t1] and [x] appears free in [t1], and we also know that
      [x] is different from [y].  The difference from the previous
      cases is that, whereas [t] is well typed under [Gamma], its body
      [t1] is well typed under [y|->T1; Gamma], so the IH allows us
      to conclude that [x] is assigned some type by the extended
      context [y|->T1; Gamma].  To conclude that [Gamma] assigns a
      type to [x], we appeal to lemma [update_neq], noting that [x]
      and [y] are different variables. *)

(** **** Exercise: 2 stars, standard (free_in_context)

    Complete the following proof. *)

Proof.
  intros x t T Gamma H H0. generalize dependent Gamma.
  generalize dependent T.
  induction H; intros; try solve [inversion H0; eauto].

  inversion H1; subst; clear H1.
  apply IHappears_free_in in H7. destruct H7 as [T2]; subst.
  unfold update in H1. rewrite (t_update_neq _ _ _ _ _ H) in H1.
  eauto.
Qed.

(** [] *)

(** From the [free_in_context] lemma, it immediately follows that any
    term [t] that is well typed in the empty context is closed (it has
    no free variables). *)

(** **** Exercise: 2 stars, standard, optional (typable_empty__closed)  *)
Corollary typable_empty__closed : forall t T,
    empty |- t \in T  ->
    closed t.
Proof.
  intros. intro. intro. rename x0 into x.
  eapply (free_in_context x t T empty H0) in H.
  destruct H as [T']. inversion H.
Qed.
(** [] *)

(** Next, we establish _context_invariance_.
    It is useful in cases when we have a proof of some typing relation
    [Gamma |- t \in T], and we need to replace [Gamma] by a different
    context [Gamma'].  When is it safe to do this?  Intuitively, it
    must at least be the case that [Gamma'] assigns the same types as
    [Gamma] to all the variables that appear free in [t]. In fact,
    this is the only condition that is needed. *)

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.

(** _Proof_: By induction on the derivation of [Gamma |- t \in T].

    - If the last rule in the derivation was [T_Var], then [t = x] and
      [Gamma x = T].  By assumption, [Gamma' x = T] as well, and hence
      [Gamma' |- t \in T] by [T_Var].

    - If the last rule was [T_Abs], then [t = \y:T2, t1], with [T =
      T2 -> T1] and [y|->T2; Gamma |- t1 \in T1].  The induction
      hypothesis states that for any context [Gamma''], if [y|->T2;
      Gamma] and [Gamma''] assign the same types to all the free
      variables in [t1], then [t1] has type [T1] under [Gamma''].
      Let [Gamma'] be a context which agrees with [Gamma] on the free
      variables in [t]; we must show [Gamma' |- \y:T2, t1 \in T2 -> T1].

      By [T_Abs], it suffices to show that [y|->T2; Gamma' |- t1 \in
      T1].  By the IH (setting [Gamma'' = y|->T2;Gamma']), it
      suffices to show that [y|->T2;Gamma] and [y|->T2;Gamma'] agree
      on all the variables that appear free in [t1].

      Any variable occurring free in [t1] must be either [y] or some
      other variable.  [y|->T2; Gamma] and [y|->T2; Gamma'] clearly
      agree on [y].  Otherwise, note that any variable other than [y]
      that occurs free in [t1] also occurs free in [t = \y:T2, t1],
      and by assumption [Gamma] and [Gamma'] agree on all such
      variables; hence so do [y|->T2; Gamma] and [y|->T2; Gamma'].

    - If the last rule was [T_App], then [t = t1 t2], with [Gamma |-
      t1 \in T2 -> T] and [Gamma |- t2 \in T2].  One induction
      hypothesis states that for all contexts [Gamma'], if [Gamma']
      agrees with [Gamma] on the free variables in [t1], then [t1] has
      type [T2 -> T] under [Gamma']; there is a similar IH for [t2].
      We must show that [t1 t2] also has type [T] under [Gamma'],
      given the assumption that [Gamma'] agrees with [Gamma] on all
      the free variables in [t1 t2].  By [T_App], it suffices to show
      that [t1] and [t2] each have the same type under [Gamma'] as
      under [Gamma].  But all free variables in [t1] are also free in
      [t1 t2], and similarly for [t2]; hence the desired result
      follows from the induction hypotheses. *)

(** **** Exercise: 3 stars, standard, optional (context_invariance)

    Complete the following proof. *)
Proof.
  intros.
  generalize dependent Gamma'.
  induction H; intros; auto.

  - (* variable *)
    constructor; rewrite <- H; symmetry; apply H0; constructor.
  - (* abstraction *)
    constructor; apply IHhas_type; intros.
    destruct (eqb_stringP x0 x1).
    + (* x0 = x1 *)
      subst. unfold update. rewrite t_update_eq. rewrite t_update_eq.
      reflexivity.
    + (* x0 <> x1 *)
      unfold update.
      rewrite t_update_neq by auto. rewrite t_update_neq by auto.
      apply H0. constructor; auto.
  - (* application *)
    econstructor; auto.
Qed.
(** [] *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 1 star, standard (progress_preservation_statement)

    Without peeking at their statements above, write down the progress
    and preservation theorems for the simply typed lambda-calculus (as
    Coq theorems).
    You can write [Admitted] for the proofs. *)

Lemma stlc_progress: forall t Gamma T,
  (Gamma |- t \in T) ->
  (value t \/ exists t', t --> t').
Admitted.

Lemma stlc_preservation: forall t t' Gamma T,
  (Gamma |- t \in T) ->
  t --> t' ->
  (Gamma |- t' \in T).
Admitted.


(* checking my answer against the statement above. There is one
mismatch.

I wrote here any Gamma can be the context whereas the actual lemma
uses empty.

For stlc_progress I am wrong. t needs to be closed to be steppable or
value.  Counter example: Gamma = (x |-> Bool), then Gamma |- x \in
Bool. But x being a variable has no way to step further, it is not a
value either.

For stlc_preservation, I am not sure. I cannot find any counterexample
intuitively, but let me try proving it.

 *)

Lemma substitution_preserves_typing_for_any_context : forall Gamma x U t v T,
  x |-> U ; Gamma |- t \in T ->
  Gamma |- v \in U   ->
  Gamma |- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  generalize dependent v.
  generalize dependent x.
  induction Ht; intros x1 v Gamma' Gt Gv; try (simpl; eauto; fail);
  unfold update in *.

  - simpl. destruct (eqb_stringP x1 x0); subst.
    + rewrite t_update_eq in H. inversion H. subst. auto.
    + rewrite t_update_neq in H by auto. constructor. assumption.

  - simpl. destruct (eqb_stringP x1 x0); subst.
    + constructor. rewrite t_update_shadow in *. assumption.
    + constructor. unfold update in *.
      apply IHHt. rewrite t_update_permute by auto. reflexivity.
      (* Here I'm stuck. There is no way to prove this theorem.
         But I am lucky to find the way to construct a counterexample to
         disprove it - check it out below. *)
Abort.


Lemma substitution_does_not_preserves_typing_when_not_closed :
~forall Gamma x U t v T,
  x |-> U ; Gamma |- t \in T ->
  Gamma |- v \in U   ->
  Gamma |- [x:=v]t \in T.
Proof.
  intro.
  specialize H with
      (Gamma := y |-> <{Bool -> Bool}>)
      (x := x)
      (U := <{Bool -> Bool}>)
      (t := <{\y: Bool, x}>)
      (v := <{y}>)
      (T := <{Bool -> Bool -> Bool}>)
  .

  (* Asserting Gamma |- [x:=v]t \in T. *)
  assert (y |-> <{ Bool -> Bool }> |- [x := y] (\ y : Bool, x) \in (Bool -> Bool -> Bool)).
  apply H; auto; fail. clear H.
  inversion H0; subst; clear H0.
  inversion H2; subst; clear H2.
  inversion H1; subst; clear H1.
Qed.

Lemma stlc_preservation': forall t t' Gamma T,
  (Gamma |- t \in T) ->
  t --> t' ->
  (Gamma |- t' \in T).
Proof with eauto.
  intros t t' Gamma T HT. generalize dependent t'.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2...
      inversion HT1...
      inversion H2; subst; clear H2;
      inversion HT2; subst; clear HT2;
      auto. constructor. unfold update.
      (* By above reasoning, this theorem is not true.
         Let me give a counterexample. *)
Abort.

Lemma stlc_preservation_does_not_hold_with_context : ~forall t t' Gamma T,
  (Gamma |- t \in T) ->
  t --> t' ->
  (Gamma |- t' \in T).
Proof.
  intro.
  specialize H with
      (t  := <{(\x:Bool->Bool, \y:Bool, x) (\x: Bool, y true)}>)
      (t' := <{\y:Bool, \x: Bool, y true}>)
      (Gamma := y |-> <{Bool -> Bool}>)
      (T := <{Bool -> (Bool -> Bool)}>).
  assert (y |-> <{ Bool -> Bool }>
       |- (\ x : Bool -> Bool, \ y : Bool, x) (\ x : Bool, y true) \in
             (Bool -> Bool -> Bool)).
  { eapply T_App; auto. eapply T_Abs. eapply T_App; auto.
    unfold update. rewrite t_update_permute. auto. easy.
  }
  assert (<{ (\ x : Bool -> Bool, \ y : Bool, x) (\ x : Bool, y true) }> -->
          <{ \ y : Bool, \x: Bool, y true }>).
  { apply ST_AppAbs. auto.
  }
  apply (H H0) in H1; clear H H0.
  inversion H1; subst; clear H1.
  inversion H2; subst; clear H2.
  inversion H1; subst; clear H1.
  inversion H3; subst; clear H3.
  unfold update in *.
  rewrite t_update_permute in H1 by easy.
  rewrite t_update_eq in H1. inversion H1.
Qed.


(* Do not modify the following line: *)
Definition manual_grade_for_progress_preservation_statement : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (stlc_variation1)

    Suppose we add a new term [zap] with the following reduction rule

                         ---------                  (ST_Zap)
                         t --> zap

and the following typing rule:

                      ------------------            (T_Zap)
                      Gamma |- zap \in T

    Which of the following properties of the STLC remain truee in
    the presence of these rules?  For each property, write either
    "remains true" or "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
      becomes false. any reducible term can reduce normally or reduce to zap.

      - Progress
      remains true. now every term can reduce to zap.

      - Preservation
      remains true.
      any typed expression can reduce to zap, which can have any type.
*)

(* Do not modify the following line: *)
Definition manual_grade_for_stlc_variation1 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (stlc_variation2)

    Suppose instead that we add a new term [foo] with the following
    reduction rules:

                       -----------------                (ST_Foo1)
                       (\x:A, x) --> foo

                         ------------                   (ST_Foo2)
                         foo --> true

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
        remains true. we didn't add any other way to reduce already reducible
        expression. (\x:A, x) is a value, thus not reducible.

      - Progress
        remains true. (\x:A, x) is a typed expression which both can reduce
        further and is a value.

      - Preservation
        becomes false. (\x:A, x) is well typed, but it's reduced form [foo]
        is not well typed.
*)

(* Do not modify the following line: *)
Definition manual_grade_for_stlc_variation2 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (stlc_variation3)

    Suppose instead that we remove the rule [ST_App1] from the [step]
    relation. Which of the following properties of the STLC remain
    true in the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
        remains true. we didn't add any other way to reduce already reducible
        expression.

      - Progress
        becomes false. now some expression is irreducible. counter example:
        ((if true then (\x:Bool, x) (\x:Bool, x)) true) is well typed
        (T = Bool), but is not reducible nor is a value.

      - Preservation
        remains true. we didn't introduce extra non-typable or ill-typed terms.

*)

(* Do not modify the following line: *)
Definition manual_grade_for_stlc_variation3 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (stlc_variation4)

    Suppose instead that we add the following new rule to the
    reduction relation:

            ----------------------------------        (ST_FunnyIfTrue)
            (if true then t1 else t2) --> true

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
        becomes false. (if true then false else true) now can reduce to
        both true and false.

      - Progress
        remains true. it's only making some expression more reducible.

      - Preservation
        becomes false. couterexample:
        (if true then (\x:Bool, x) (\x: Bool, x))  has type (Bool -> Bool)
        but it's reduction (true) has type Bool instead.

*)
(** [] *)

(** **** Exercise: 2 stars, standard, optional (stlc_variation5)

    Suppose instead that we add the following new rule to the typing
    relation:

                 Gamma |- t1 \in Bool->Bool->Bool
                     Gamma |- t2 \in Bool
                 ------------------------------          (T_FunnyApp)
                    Gamma |- t1 t2 \in Bool

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
        remains true. adding a typing rule doesn't affect step.

      - Progress
        becomes false. if ((\x, \y, x) true) then true else true is
        well typed but cannot reduce further nor is a value.

      - Preservation
        becomes false. ((\x, \y, x) true) has type Bool, but it's reduction
        (\y, true) has type (Bool->Bool)

*)
(** [] *)

(** **** Exercise: 2 stars, standard, optional (stlc_variation6)

    Suppose instead that we add the following new rule to the typing
    relation:

                     Gamma |- t1 \in Bool
                     Gamma |- t2 \in Bool
                    ---------------------               (T_FunnyApp')
                    Gamma |- t1 t2 \in Bool

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
        remains true. Adding typing rule doesn't affect reducibility.

      - Progress
        becomes false. counterexample: true true.

      - Preservation
        remains true. unlike variant 5, it doesn't introduce any
        ill-typed extra reducible terms. true X and false Y are not reducible.
 *)

(** [] *)

(** **** Exercise: 2 stars, standard, optional (stlc_variation7)

    Suppose we add the following new rule to the typing relation
    of the STLC:

                         ------------------- (T_FunnyAbs)
                         |- \x:Bool,t \in Bool

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
        remains true. Adding typing rule doesn't affect reducibility.

      - Progress
        becomes false. counterexample: [if (\x:Bool, true) then true else true]
        is neither a value nor reducible.

      - Preservation
        remains true. I'm not sure about this one but I can't find a
        counterexample either. (I may as well just prove it.)

        Proved that preservation indeed remains true. That's funny -
        both expected and unexpected :)
 *)

Module variant7.

Reserved Notation "Gamma '|-' t '\in' T" (at level 101,
                                          t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      x |-> T2 ; Gamma |- t1 \in T1 ->
      Gamma |- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (T2 -> T1) ->
      Gamma |- t2 \in T2 ->
      Gamma |- t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma |- true \in Bool
  | T_False : forall Gamma,
       Gamma |- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma |- t1 \in Bool ->
       Gamma |- t2 \in T1 ->
       Gamma |- t3 \in T1 ->
       Gamma |- if t1 then t2 else t3 \in T1
  | T_FunnyAbs : forall x t Gamma,
    Gamma |- \x:Bool, t \in Bool (* <-- NEW *)

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Lemma weakening : forall Gamma Gamma' t T,
     inclusion Gamma Gamma' ->
     Gamma  |- t \in T  ->
     Gamma' |- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using inclusion_update.
Qed.

Lemma weakening_empty : forall Gamma t T,
     empty |- t \in T  ->
     Gamma |- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.


Lemma substitution_preserves_typing : forall Gamma x U t v T,
  x |-> U ; Gamma |- t \in T ->
  empty |- v \in U   ->
  Gamma |- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into S.
    destruct (eqb_stringP x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
  - rename s into y, t0 into t.
    destruct (eqb_stringP x y); subst.
    + apply T_FunnyAbs.
    + apply T_FunnyAbs.
Qed.

Theorem preservation : forall t t' T,
  empty |- t \in T  ->
  t --> t'  ->
  empty |- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2...
      inversion HT1...
Qed.

End variant7.

(** [] *)

End STLCProp.

(* ================================================================= *)
(** ** Exercise: STLC with Arithmetic *)

(** To see how the STLC might function as the core of a real
    programming language, let's extend it with a concrete base
    type of numbers and some constants and primitive
    operators. *)

Module STLCArith.
Import STLC.

(** To types, we add a base type of natural numbers (and remove
    booleans, for brevity). *)

Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Nat  : ty.

(** To terms, we add natural number constants, along with
    successor, predecessor, multiplication, and zero-testing. *)

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_const  : nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0 : tm -> tm -> tm -> tm.



Notation "{ x }" := x (in custom stlc at level 1, x constr).

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

Notation "'Nat'" := Ty_Nat (in custom stlc at level 0).
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

(** **** Exercise: 5 stars, standard (stlc_arith)

    Finish formalizing the definition and properties of the STLC
    extended with arithmetic. This is a longer exercise. Specifically:

    1. Copy the core definitions for STLC that we went through,
        as well as the key lemmas and theorems, and paste them
        into the file at this point. Do not copy examples, exercises,
        etc. (In particular, make sure you don't copy any of the []
        comments at the end of exercises, to avoid confusing the
        autograder.)

        You should copy over five definitions:
          - Fixpoint susbt
          - Inductive value
          - Inductive step
          - Inductive has_type
          - Inductive appears_free_in

        And five theorems, with their proofs:
          - Lemma weakening
          - Lemma weakening_empty
          - Lemma substitution_preserves_typing
          - Theorem preservation
          - Theorem progress

        It will be helpful to also copy over "Reserved Notation",
        "Notation", and "Hint Constructors" for these things.

    2. Edit and extend the four definitions (subst, value, step,
        and has_type) so they are appropriate for the new STLC
        extended with arithmetic.

    3. Extend the proofs of all the five properties of the original
        STLC to deal with the new syntactic forms. Make sure Coq
        accepts the whole file. *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if eqb_string x y then s else t
  | <{\y:T, t1}> =>
      if eqb_string x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | tm_const n => tm_const n
  | <{ succ t }> => <{succ [x:=s]t}>
  | <{ pred t }> => <{pred [x:=s]t}>
  | <{ t1*t2 }> => <{([x:=s]t1) * ([x:=s]t2)}>
  | <{if0 t1 then t2 else t3}> =>
      <{if0 ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_const : forall n:nat,
      value <{ n }>.

Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_SuccConst : forall (n : nat),
    <{succ n}> --> tm_const (S n)
  | ST_Succ : forall t t',
    t --> t' ->
    <{succ t}> --> <{succ t'}>
  | ST_PredConst : forall (n : nat),
    <{pred n}> --> tm_const (PeanoNat.Nat.pred n)
  | ST_Pred : forall t t',
    t --> t' ->
    <{pred t}> --> <{pred t'}>
  | ST_MultConst : forall (a b : nat),
    <{a * b}> --> tm_const (a * b)
  | ST_Mult1 : forall t2 t1 t1',
    t1 --> t1' ->
    <{t1 * t2}> --> <{t1' * t2}>
  | ST_Mult2 : forall (a : nat) t t',
    t --> t' ->
    <{a * t}> --> <{a * t'}>
  | ST_If0 : forall t1 t2,
      <{if0 0 then t1 else t2}> --> t1
  | ST_IfNon0 : forall (n : nat) t1 t2,
      n <> 0 ->
      <{if0 n then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if0 t1 then t2 else t3}> --> <{if0 t1' then t2 else t3}>
where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Definition context := partial_map ty.
Reserved Notation "Gamma '|-' t '\in' T"
         (at level 101, t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      x |-> T2 ; Gamma |- t1 \in T1 ->
      Gamma |- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (T2 -> T1) ->
      Gamma |- t2 \in T2 ->
      Gamma |- t1 t2 \in T1
  | T_Const : forall Gamma (n : nat),
    Gamma |- n \in Nat
  | T_Succ : forall Gamma t,
    (Gamma |- t \in Nat) ->
    (Gamma |- succ t \in Nat)
  | T_Pred : forall Gamma t,
    (Gamma |- t \in Nat) ->
    (Gamma |- pred t \in Nat)
  | T_Mult : forall Gamma t t',
    (Gamma |- t \in Nat) ->
    (Gamma |- t' \in Nat) ->
    (Gamma |- t * t' \in Nat)
  | T_If0 : forall t1 t2 t3 T1 Gamma,
       Gamma |- t1 \in Nat ->
       Gamma |- t2 \in T1 ->
       Gamma |- t3 \in T1 ->
       Gamma |- if0 t1 then t2 else t3 \in T1

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Inductive appears_free_in (x : string) : tm -> Prop :=
  | afi_var : appears_free_in x <{x}>
  | afi_app1 : forall t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{t1 t2}>
  | afi_app2 : forall t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{t1 t2}>
  | afi_abs : forall y T1 t1,
      y <> x  ->
      appears_free_in x t1 ->
      appears_free_in x <{\y:T1, t1}>
  | afi_if1 : forall t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x <{if0 t1 then t2 else t3}>
  | afi_if2 : forall t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x <{if0 t1 then t2 else t3}>
  | afi_if3 : forall t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x <{if0 t1 then t2 else t3}>
  | afi_succ : forall t,
    appears_free_in x t ->
    appears_free_in x <{succ t}>
  | afi_pred : forall t,
    appears_free_in x t ->
    appears_free_in x <{pred t}>
  | afi_mult1 : forall t t',
    appears_free_in x t ->
    appears_free_in x <{t * t'}>
  | afi_mult2 : forall t t',
    appears_free_in x t' ->
    appears_free_in x <{t * t'}>
  .

Hint Constructors appears_free_in : core.


Lemma weakening : forall Gamma Gamma' t T,
     inclusion Gamma Gamma' ->
     Gamma  |- t \in T  ->
     Gamma' |- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using inclusion_update.
Qed.

Lemma weakening_empty : forall Gamma t T,
     empty |- t \in T  ->
     Gamma |- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  x |-> U ; Gamma |- t \in T ->
  empty |- v \in U   ->
  Gamma |- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into S.
    destruct (eqb_stringP x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
Qed.

Theorem preservation : forall t t' T,
  empty |- t \in T  ->
  t --> t'  ->
  empty |- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t'' HE; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2...
      inversion HT1...
Qed.

Lemma canonical_forms_nat : forall t,
  empty |- t \in Nat ->
  value t ->
  exists n, t = tm_const n.
Proof.
  intros t HT HVal.
  destruct HVal; eauto.
  inversion HT.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (T1 -> T2) ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal; inversion HT; subst.
  exists x0, t1. reflexivity.
Qed.

Theorem progress : forall t T,
  empty |- t \in T ->
  value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma; auto.
  (* auto solves all three cases in which t is a value *)
  - (* T_Var *)
    (* contradictory: variables cannot be typed in an
       empty context *)
    discriminate H.

  - (* T_App *)
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a
       value or steps... *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t2 is also a value *)
        eapply canonical_forms_fun in Ht1; [|assumption].
        destruct Ht1 as [x [t0 H1]]. subst.
        exists (<{ [x:=t2]t0 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists (<{t1 t2'}>)...

    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists (<{t1' t2}>)...

  - (* T_Succ *)
    destruct IHHt; auto.
    + apply canonical_forms_nat in Ht; auto. inversion Ht; subst; clear Ht.
      eauto.
    + right. destruct H. eauto.

  - (* T_Pred *)
    destruct IHHt; auto.
    + apply canonical_forms_nat in Ht; auto. inversion Ht; subst; clear Ht.
      eauto.
    + right. destruct H. eauto.

  - (* T_Mult *)
    destruct IHHt1; destruct IHHt2; auto.
    + apply canonical_forms_nat in H; auto;
      apply canonical_forms_nat in H0; auto.
      destruct H; destruct H0; subst.
      eauto.
    + apply canonical_forms_nat in H; auto.
      destruct H; destruct H0; subst.
      eauto.
    + destruct H. eauto.
    + destruct H. destruct H0. eauto.

  - (* T_If *)
    right. destruct IHHt1...

    + (* t1 is a value *)
      destruct (canonical_forms_nat t1 Ht1); auto; subst.
      destruct x0; eauto.
    + (* t1 also steps *)
      destruct H as [t1' Hstp]. exists <{if0 t1' then t2 else t3}>...
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_stlc_arith : option (nat*string) := None.
(** [] *)

End STLCArith.

(* 2020-09-09 21:08 *)
