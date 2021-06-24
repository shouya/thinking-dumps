
Definition relation T := T -> T -> Prop.

Definition reflexive {T} (R: relation T) := forall t: T, R t t.
Definition transitive {T} (R: relation T) := forall s t u: T, R s t -> R t u -> R s u.

(* R1 is subset of R2 *)
Definition rel_subset {T} (R1 R2: relation T) :=
  forall a b, R1 a b -> R2 a b.

Definition closure {T} (R Rc: relation T) (P: relation T -> Prop) : Prop :=
  rel_subset R Rc ->
  (forall Rc', (rel_subset R Rc') -> P Rc' -> (rel_subset Rc Rc')).

Definition rel_union {T} (R1 R2: relation T) : relation T :=
  fun a b => R1 a b \/ R2 a b.

Definition eq_rel {T} : relation T := (fun a b => a = b).

Definition reflexive_closure {T} (R: relation T) : relation T :=
  rel_union eq_rel R.

(* ex 2.2.6 *)
Lemma reflexive_closure_proof :
  forall T R, @closure T R (@reflexive_closure T R) reflexive.
Proof.
  intros.
  unfold closure, reflexive_closure, reflexive, rel_subset, rel_union, eq_rel, relation in *.
  intros.
  destruct H2.
  - subst. auto.
  - auto.
Qed.

Fixpoint transitive_closure' {T} (R: relation T) (n : nat) : relation T :=
  match n with
  | 0 => R
  | S n => let Rn := transitive_closure' R n
          in rel_union Rn (fun a b => exists c, Rn a c /\ Rn c b)
  end.

Definition transitive_closure {T} (R: relation T) : relation T :=
  fun a b => exists n, transitive_closure' R n a b.

(* ex 2.2.7 *)
Lemma transitive_closure_proof :
  forall T R, @closure T R (@transitive_closure T R) transitive.
Proof.
  intros.
  unfold closure, transitive_closure, transitive, rel_subset, rel_union, eq_rel, relation in *.
  intros.
  destruct H2 as [n ?].
  generalize dependent a.
  generalize dependent b.
  induction n; intros.
  - auto.
  - simpl in H2.
    unfold closure, transitive_closure, transitive, rel_subset, rel_union, eq_rel, relation in *.
    destruct H2.
    + auto.
    + destruct H2. destruct H2.
      eauto.
Qed.

Definition preserves {T} (R: relation T) (P: T -> Prop) :=
  forall t t', P t -> R t t' -> P t'.

(* ex 2.2.8 *)
Lemma preserves_reflexive_closure :
  forall {T} (R : relation T) (P: T -> Prop),
    preserves R P -> preserves (reflexive_closure R) P.
Proof.
  intros.
  unfold preserves, reflexive_closure, rel_union, eq_rel in *.
  intros.
  destruct H1; subst; eauto.
Qed.
