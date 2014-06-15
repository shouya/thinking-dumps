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

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'. reflexivity. Qed.


Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2.
  induction l1 as [| n l1'].
  reflexivity.
  simpl. rewrite -> IHl1'. reflexivity.
Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist :=
  match l with
    | [] => [v]
    | h :: t => h :: snoc t v
  end.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => snoc (rev t) h
  end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.


Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving snoc, but we don't have any equations
       in either the immediate context or the global
       environment that have anything to do with snoc!

       We can make a little progress by using the IH to
       rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.


Theorem length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).
Proof.
  intros n l.
  induction l.
  reflexivity.
  simpl. rewrite <- IHl. reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intro l.
  induction l.
  reflexivity.
  simpl. rewrite length_snoc. rewrite IHl. reflexivity.
Qed.

Theorem app_nil_end : forall l : natlist,
  l ++ [] = l.
Proof.
  intro l.
  induction l.
  reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Lemma rev_snoc_rev : forall t : natlist, forall h : nat,
                       rev (snoc (rev t) h) = h :: rev (rev t).
Proof.
  intros.
  induction t.
  reflexivity.
  simpl.

  replace (rev (snoc (rev t) n)) with (n :: (rev (rev t))).
Abort.

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  intros.
  induction l.
  reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Lemma cons_rev : forall n : nat, forall l : natlist,
                   n :: rev l = rev (l ++ [n]).
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  rewrite <- IHl.
  simpl.
  reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intro l.
  induction l as [| h t].
  Case "l = []".
    reflexivity.
  Case "l = h :: t".
    simpl.
    replace (rev (snoc (rev t) h)) with (h :: rev (rev t)).
    rewrite IHt.
    reflexivity.
    SCase "h :: rev (rev t) = rev (snoc (rev t) h)".
      rewrite IHt.
      rewrite snoc_append.
      rewrite <- cons_rev.
      rewrite IHt.
      reflexivity.
Qed.


Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma app_nil_r : forall l : natlist,
                    l ++ [] = l.
Proof.
  induction l. reflexivity. simpl. rewrite IHl. reflexivity.
Qed.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros.
  induction l1 as [| h1 t1].
  Case "l1 = []".
    simpl.
    rewrite app_nil_r.
    reflexivity.
  Case "l1 = h1 :: t1".
    simpl.
    rewrite snoc_append.
    rewrite IHt1.
    rewrite app_assoc.
    rewrite snoc_append.
    reflexivity.
Qed.


Lemma cons_app_assoc : forall h : nat, forall l1 l2 : natlist,
                         (h :: l1) ++ l2 = h :: l1 ++ l2.
Proof. intros. reflexivity. Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [| h1 t1].
  Case "l1 = []".
    reflexivity.
  Case "l1 = h1 :: t1".
    rewrite cons_app_assoc.
    induction h1 as [| h1'].
    SCase "h1 = 0".
      simpl.
      rewrite IHt1.
      reflexivity.
    SCase "h1 = S h1'".
      simpl.
      rewrite IHt1.
      reflexivity.
Qed.


Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1, l2 with
    | [], [] => true
    | h1 :: t1, [] => false
    | [], h2 :: t2 => false
    | h1 :: t1, h2 :: t2 =>
      (andb (beq_nat h1 h2) (beq_natlist t1 t2))
  end.


Example test_beq_natlist1 : (beq_natlist nil nil = true).
Proof. reflexivity. Qed.
Example test_beq_natlist2 : beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_beq_natlist3 : beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.


Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intro.
  induction l.
  reflexivity.
  simpl.
  rewrite <- beq_nat_refl.
  rewrite <- IHl.
  reflexivity.
Qed.


Theorem count_member_nonzero : forall (s : bag),
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  reflexivity.
Qed.  (* WHAT THE ****!! YOU'RE SO AMAZING COQ!! *)

Theorem ble_n_Sn : forall n,
  ble_nat n (S n) = true.
Proof.
  intros n. induction n as [| n'].
  Case "0".
    simpl. reflexivity.
  Case "S n'".
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_decreases_count: forall (s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intro.
  induction s.
  Case "s = []". reflexivity.
  Case "s = n :: s".
    induction n.
    SCase "n = 0".
      simpl.
      rewrite ble_n_Sn.
      reflexivity.
    SCase "n = S n".
      simpl.
      rewrite IHs.
      reflexivity.
Qed.


Theorem bag_count_sum: forall s1 s2 : bag,
  count 0 (sum s1 s2) = count 0 s1 + count 0 s2.
Proof.
  intros.
  induction s1, s2.
  Case "s1 = [], s2 = []". reflexivity.
  Case "s1 = [], s2 = n :: s2". reflexivity.
  Case "s1 = n :: s1, s2 = []".
    induction n.
    SCase "n = 0".
      rewrite plus_0_r.
      rewrite app_nil_r.
      reflexivity.
    SCase "n = S n".
      rewrite plus_0_r.
      rewrite app_nil_r.
      reflexivity.
  Case "s1 = n0 :: s1, s2 = n :: s2".
    induction n0, n; (simpl; rewrite IHs1; reflexivity).
(*
    induction n0, n.
    SCase "n0 = n = 0".
      simpl. rewrite IHs1.
      reflexivity.
    SCase "n0 = 0, n = S n".
      simpl. rewrite IHs1.
      reflexivity.
    SCase "n0 = S n0, n = 0".
      simpl. rewrite IHs1.
      reflexivity.
    SCase "n0 = S n0, n = S n".
      simpl. rewrite IHs1.
      reflexivity.
*)
Qed.

(* this question is a four-star exercise.

  my idea is to apply induction on l1 and l2, then deny all false assumptions:
   - l1 = [], l2 <> []
   - l1 <> [], l1 = []
  and prove the true assumptions:
   - l1 = l2 = []
   - l1 = l2 <> []

  currently i have no idea about how to cope with such false hypotheses.
 *)
Theorem rev_injective: forall (l1 l2 : natlist),
                         rev l1 = rev l2 -> l1 = l2.
Proof.
Abort.  (* TODO *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Fixpoint index (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n 0 with
               | true => Some a
               | false => index (pred n) l'
               end
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Example test_index1 : index 0 [4;5;6;7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 3 [4;5;6;7] = Some 7.
Proof. reflexivity. Qed.
Example test_index3 : index 10 [4;5;6;7] = None.
Proof. reflexivity. Qed.

Fixpoint index' (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n 0 then Some a else index' (pred n) l'
  end.

Definition hd_opt (l : natlist) : natoption :=
  match l with
    | nil => None
    | a :: _ => Some a
  end.


Example test_hd_opt1 : hd_opt [] = None.
Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt3 : hd_opt [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_opt l).
Proof.
  intros.
  induction l.
  reflexivity.
  reflexivity.
Qed.

Module Dictionary.

Inductive dictionary : Type :=
  | empty : dictionary
  | record : nat -> nat -> dictionary -> dictionary.

Definition insert (key value : nat) (d : dictionary) : dictionary :=
  (record key value d).

Fixpoint find (key : nat) (d : dictionary) : natoption :=
  match d with
  | empty => None
  | record k v d' => if (beq_nat key k)
                       then (Some v)
                       else (find key d')
  end.


Theorem dictionary_invariant1' : forall (d : dictionary) (k v: nat),
  (find k (insert k v d)) = Some v.
Proof.
  intros.
  induction d.
  Case "d = {}".
    simpl.
    rewrite <- beq_nat_refl.
    reflexivity.
  Case "d = (k:v)::d".
    simpl.
    rewrite <- beq_nat_refl.
    reflexivity.
Qed.

Theorem dictionary_invariant2' : forall (d : dictionary) (m n o: nat),
  beq_nat m n = false -> find m d = find m (insert n o d).
Proof.
  intros.
  simpl.
  rewrite H.
  reflexivity.
Qed.

End Dictionary.

End NatList.
