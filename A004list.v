Require Export A003induction.
Module NatList.

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.


Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.


Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.


Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.
Qed.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intro p.
  destruct p.
  reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intro.
  destruct p.
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intro.
  destruct p.
  reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | 0 => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => 0
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => match h with
                 | 0 => nonzeros t
                 | _ => h :: nonzeros t
               end
  end.


Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => match oddb h with
                 | false => oddmembers t
                 | true => h :: oddmembers t
               end
  end.


Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).


Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
    | [] => l2
    | h1 :: t1 => match l2 with
                    | [] => l1
                    | h2 :: t2 => h1 :: h2 :: alternate t1 t2
                  end
  end.


Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4: alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.


Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
    | [] => 0
    | h :: t => match (beq_nat h v) with
                  | true => S (count v t)
                  | false => count v t
                end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.


Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition bge_nat (n m:nat) : bool :=
  negb (blt_nat n m).

Definition member (v:nat) (s:bag) : bool :=
  (bge_nat (count v s) 1).


Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.


Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
    | [] => []
    | h :: t => match (beq_nat v h) with
                  | true => t
                  | false => h :: remove_one v t
                end
  end.



Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
    | [] => []
    | h :: t => match (beq_nat v h) with
                  | true => remove_all v t
                  | false => h :: remove_all v t
                end
  end.



Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s__1:bag) (s__2:bag) : bool :=
  match s__1 with
    | [] => true
    | h :: t => match count h s__2 with
                 | 0 => false
                 | _ => subset t (remove_one h s__2)
               end
  end.


Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.


Theorem bag_add_count: forall (b : bag) (i : nat),
  count i (add i b) = S (count i b).
Proof.
  intros.
  destruct b.
  Case "b = []".
    replace (add i []) with [i].
    replace (count i []) with 0.
    simpl.
    replace (beq_nat i i) with true.
    reflexivity.
    SCase "beq_nat i i = true".
      rewrite <- beq_nat_refl.
      reflexivity.
    SCase "0 = count i []".
      reflexivity.
    SCase "[i] = add i []".
      reflexivity.

  Case "b = add i b".
    replace (add i (n :: b)) with (i :: n :: b).
    replace (count i (i :: n :: b)) with
      (S (count i (n :: b))).
    reflexivity.
    SCase "S (count i (n :: b)) = count i (i :: n :: b)".
      simpl.
      rewrite <- beq_nat_refl.
      reflexivity.
    SCase "i :: n :: b = add i (n :: b)".
      reflexivity.
Qed.

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intro.
  destruct l.
  reflexivity.
  simpl. reflexivity.
Qed.
