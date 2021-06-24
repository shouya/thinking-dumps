Require Import List.
Import ListNotations.

Definition set X := X -> Prop.

Inductive term : Type :=
| T0 : term
| TTrue : term
| TFalse : term
| TSucc (t: term) : term
| TPred (t: term) : term
| TIszero (t: term) : term
| TIf (t1 t2 t3: term) : term
.

Definition emptyset {X} : set X := fun x => False.
Definition union {X} (a b: set X) : set X := fun x => a x \/ b x.
Definition union3 {X} (a b c: set X) : set X := fun x => a x \/ b x \/ c x.
Definition singletonset {X} (x: X) : set X := fun x' => x = x'.
Definition setfromlist {X} (xs : list X) : set X := fun x => In x xs.
Definition setfrommappedset {X} (xs : set X) (f : X -> set X) : set X :=
  fun x => exists y, xs y /\ f y x.

Definition subset {X} (a b : set X) :=
  forall x, a x -> b x.

(* concrete term from 3.2.3 *)
Fixpoint Sterm (n : nat) :=
  match n with
  | 0 => emptyset
  | S n => let stn := Sterm n
          in union3
               (setfromlist [T0; TTrue; TFalse])
               (setfrommappedset
                  stn (fun x => setfromlist [TSucc x; TPred x; TIszero x]))
               (setfrommappedset
                  stn (fun x => (setfrommappedset
                                stn (fun y => (setfrommappedset
                                              stn (fun z => singletonset (TIf x y z)))))))
  end.

(* exercise  *)
Lemma Sterm_cumulative :
  forall n, subset (Sterm n) (Sterm (S n)).
Proof.
  induction n.
  - simpl. repeat intro.
    inversion H.

  - repeat intro.
    simpl in H. unfold union3 in H.
    destruct H.

    + left. auto.
    + destruct H.
      * right. left.
        unfold setfrommappedset in *. destruct H. destruct H.
        apply IHn in H.
        exists x0. split; auto.
      * right. right. unfold setfrommappedset in *.
        destruct H. destruct H. destruct H0.
        destruct H0. destruct H1. destruct H1.
        apply IHn in H. apply IHn in H0. apply IHn in H1.
        exists x0. split; auto. exists x1. split; auto. exists x2. split; auto.
Qed.
