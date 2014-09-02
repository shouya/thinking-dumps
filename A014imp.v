
Require Export A013sflib.

Module AExp.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (e : aexp) : nat :=
  match e with
    | ANum n => n
    | APlus a b => (aeval a) + (aeval b)
    | AMinus a b => (aeval a) - (aeval b)
    | AMult a b => (aeval a) * (aeval b)
  end.

SearchAbout (bool).

Fixpoint beval (e : bexp) : bool :=
  match e with
    | BTrue => true
    | BFalse => false
    | BEq a b => beq_nat (aeval a) (aeval b)
    | BLe a b => ble_nat (aeval a) (aeval b)
    | BNot a => negb (beval a)
    | BAnd a b => andb (beval a) (beval b)
  end.


Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed. (* 2 + (0 + (0 + 1)) *)


Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros.
  induction a.

  Case "ANum". reflexivity.
  Case "APlus".
    destruct a1.
    SCase "ANum".
      destruct n.
      SSCase "n == 0". assumption.
      SSCase "n <> 0". simpl. rewrite IHa2. reflexivity.
    SCase "APlus".
      simpl in IHa1. simpl. rewrite IHa1. rewrite IHa2. reflexivity.
    SCase "AMinus".
      simpl in IHa1. simpl. rewrite IHa1. rewrite IHa2. reflexivity.
    SCase "AMult".
      simpl in IHa1. simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  Case "AMinus".
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  Case "AMult".
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

(*
Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros.
  induction a; try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  reflexivity.
  destruct a1; try (simpl in IHa1; simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  destruct n; [assumption | simpl; rewrite IHa2; reflexivity].
Qed.

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros.
  induction a; try (simpl; rewrite IHa1; rewrite IHa2; reflexivity); try reflexivity.
  destruct a1; try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
  destruct n; simpl; rewrite IHa2; reflexivity.
Qed.
*)

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq a b => BEq (optimize_0plus a) (optimize_0plus b)
    | BLe a b => BLe (optimize_0plus a) (optimize_0plus b)
    | BNot BTrue => BFalse
    | BNot BFalse => BTrue
    | BNot a => BNot (optimize_0plus_b a)
    | BAnd BTrue BFalse => BFalse
    | BAnd BFalse _ => BFalse
    | BAnd BTrue b => (optimize_0plus_b b)
    | BAnd a b => BAnd (optimize_0plus_b a) (optimize_0plus_b b)
  end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intro.
  induction b;
    try reflexivity;
    try (simpl; repeat rewrite optimize_0plus_sound; reflexivity);
    try (destruct b;
         try reflexivity;
         try (simpl; repeat rewrite optimize_0plus_sound; reflexivity);
         try (simpl; simpl in IHb; rewrite IHb; reflexivity)).
  Case "BAnd b1 b2".
  destruct b1; destruct b2;
      try reflexivity;
      try (simpl; repeat rewrite optimize_0plus_sound; reflexivity);
      try (simpl; simpl in IHb2; rewrite IHb2;
           try repeat rewrite optimize_0plus_sound;
           reflexivity);
      try (simpl; simpl in IHb1; rewrite IHb1; try repeat rewrite optimize_0plus_sound;
           reflexivity);
      try (simpl; simpl in IHb1; rewrite IHb1; simpl in IHb2; rewrite IHb2; reflexivity).
Qed.



Fixpoint optimize_0plus' (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus' e2
  | APlus e1 (ANum 0) => optimize_0plus' e1
  | APlus e1 e2 => APlus (optimize_0plus' e1) (optimize_0plus' e2)
  | AMinus e1 (ANum 0) => optimize_0plus' e1
  | AMinus e1 e2 => AMinus (optimize_0plus' e1) (optimize_0plus' e2)
  | AMult (ANum 0) e2 => ANum 0
  | AMult e1 (ANum 0) => ANum 0
  | AMult (ANum 1) e2 => optimize_0plus' e2
  | AMult e1 (ANum 1) => optimize_0plus' e1
  | AMult e1 e2 => AMult (optimize_0plus' e1) (optimize_0plus' e2)
  end.


Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus' a) = aeval a.
Proof.
  intros.
  induction a; try reflexivity.
  Case "APlus".
    destruct a1;
      try destruct n; [simpl; assumption
                       | destruct a2; try (destruct n0;
                                         try (simpl; rewrite plus_0_r; reflexivity);
                                         try (simpl; reflexivity))
                       | .. ].
admit. (* 懶得寫完 *)
Admitted.


Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros.
  omega.
Qed.


Module aevalR_first_try.

Reserved Notation "e '||' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n: nat), (ANum n) || n
  | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
      e1 || n1 -> e2 || n2 -> (APlus e1 e2) || (n1 + n2)
  | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
      e1 || n1 -> e2 || n2 -> (AMinus e1 e2) || (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2: nat),
      e1 || n1 -> e2 || n2 -> (AMult e1 e2) || (n1 * n2)
  where "e '||' n" := (aevalR e n) : type_scope.

Tactic Notation "aevalR_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_ANum" | Case_aux c "E_APlus"
  | Case_aux c "E_AMinus" | Case_aux c "E_AMult" ].

Theorem aeval_iff_aevalR : forall a n,
  (a || n) <-> aeval a = n.
Proof.
  intros. split.

  Case "->". intros H; induction H; subst; reflexivity.
  Case "<-".
  generalize dependent n.
  aevalR_cases (induction a) SCase;
    intros; subst; simpl; constructor;
    try apply IHa1; try apply IHa2; try reflexivity.
Qed.

(*
Fixpoint beval (e : bexp) : bool :=
  match e with
    | BTrue => true
    | BFalse => false
    | BEq a b => beq_nat (aeval a) (aeval b)
    | BLe a b => ble_nat (aeval a) (aeval b)
    | BNot a => negb (beval a)
    | BAnd a b => andb (beval a) (beval b)
  end.
*)

Reserved Notation "e '//' b" (at level 50, left associativity).

Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue : BTrue // true
  | E_BFalse : BFalse // false
  | E_BEq : forall (a b : aexp) (a' b' : nat),
              a || a' -> b || b' -> BEq a b // beq_nat a' b'
  | E_BLe : forall a b a' b',
              a || a' -> b || b' -> BLe a b // ble_nat a' b'
  | E_BNot : forall a a', a // a' -> BNot a // negb a'
  | E_BAnd : forall a b a' b',
               a // a' -> b // b' -> BAnd a b // andb a' b'
  where "e '//' b" := (bevalR e b) : type_scope.



Theorem beval_iff_bevalR : forall a b,
  (a // b) <-> beval a = b.
Proof.
  intros. split; intros.

  Case "->".
    induction H;
    try (apply aeval_iff_aevalR in H; apply aeval_iff_aevalR in H0);
    subst; reflexivity.

  Case "<-".
    generalize dependent b.
    induction a;
    intros; subst; constructor; try (apply aeval_iff_aevalR; reflexivity);
    try (apply IHa; reflexivity);
    try (apply IHa1; reflexivity);
    try (apply IHa2; reflexivity).
Qed.


(* To show how relational definitions are preferrable to computational definitions
   in the condition of non-deterministic cases.
*)
Module aevalR_division.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ADiv : aexp -> aexp -> aexp. (* <--- new *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) || n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (APlus a1 a2) || (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMinus a1 a2) || (n1 - n2)
  | E_AMult : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMult a1 a2) || (n1 * n2)
  | E_ADiv : forall (a1 a2: aexp) (n1 n2 n3: nat),
      (a1 || n1) -> (a2 || n2) -> (mult n2 n3 = n1) -> (ADiv a1 a2) || n3

where "a '||' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.
Inductive aexp : Type :=
  | AAny : aexp (* <--- NEW *)
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.


Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any : forall (n:nat),
      AAny || n (* <--- new *)
  | E_ANum : forall (n:nat),
      (ANum n) || n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (APlus a1 a2) || (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMinus a1 a2) || (n1 - n2)
  | E_AMult : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMult a1 a2) || (n1 * n2)

where "a '||' n" := (aevalR a n) : type_scope.

End aevalR_extended.

Module Id.

Inductive id : Type :=
  Id : nat -> id.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
  intros.
  destruct id1, id2.
  destruct (eq_nat_dec n n0).
  subst. left. reflexivity.
  right. intro. inversion H.  apply n1 in H1. contradiction.
Qed.

Lemma eq_id : forall (T:Type) x (p q:T),
              (if eq_id_dec x x then p else q) = p.
Proof.
  intros.
  destruct (eq_id_dec x x).
  reflexivity.
  apply ex_falso_quodlibet. apply n. reflexivity.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y ->
               (if eq_id_dec x y then p else q) = q.
Proof.
  intros.
  destruct (eq_id_dec x y).
  apply H in e. inversion e.
  reflexivity.
Qed.

End Id.
