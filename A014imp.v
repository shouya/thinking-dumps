
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
    destruct a1


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
