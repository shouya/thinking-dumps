Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Open Scope string_scope.

Inductive typ : Type :=
| TyBase : string -> typ
| TyFun : typ -> typ -> typ
| TyBool : typ
.

Inductive term : Type :=
| TVar (var: string) : term
| TLam (var: string) (typ: typ) (body: term) : term
| TApp (operator: term) (operand: term) : term
| TIf (cond: term) (then_: term) (else_: term) : term
| TTru : term
| TFls : term
.

Declare Custom Entry term.
Declare Custom Entry typ.

Notation "{{ x }}" := x (x custom term).
Notation "{: x :}" := x (x custom typ).
Notation "( x )" := x (in custom term, x custom term).

Notation "'λ' a : T , body" :=
  (TLam a T body) (in custom term at level 98
                      , a constr at level 0  (* avoid ":" being interpreted as type *)
                      , T custom typ at level 0
                      , body custom term at level 99
                      , right associativity).

Notation "t1 t2" :=
  (TApp t1 t2) (in custom term at level 97
                   , t1 custom term
                   , t2 custom term
                   , left associativity).

Notation "'if' a 'then' b 'else' c" :=
  (TIf a b c) (in custom term at level 99
                  , a custom term
                  , b custom term
                  , c custom term
                  , left associativity).

Notation "'tru'" := TTru (in custom term).
Notation "'fls'" := TTru (in custom term).


Coercion TVar : string >-> term.
Coercion TyBase : string >-> typ.

Notation "x" := x (in custom term at level 0, x constr at level 0).
Notation "x" := x (in custom typ at level 0, x constr at level 0).

Notation "x -> y" :=
  (TyFun x y) (in custom typ at level 80,
                  x custom typ,
                  y custom typ,
                  right associativity).
Notation "( x )" := x (in custom typ, x custom typ).

Print Custom Grammar term.

Definition a := "a".
Definition b := "b".
Definition c := "c".
Definition x := "x".
Definition y := "y".
Definition z := "z".
Definition T := "T".
Definition T1 := "T1".
Definition T2 := "T2".
Definition Bool := "Bool".

Unset Printing Notations.

Definition foo := {{ λ x : (T -> T) -> T -> T, (λ y : "S", (x x) (x x)) x }}.

Print foo.

Example expanded_foo :
  foo = TLam x (TyFun (TyFun (TyBase T) (TyBase T)) (TyFun (TyBase T) (TyBase T)))
             (TApp (TLam y (TyBase "S") (TApp (TApp (TVar x) (TVar x)) (TApp (TVar x) (TVar x)))) (TVar x)).
Proof. reflexivity. Qed.

Set Printing Notations.
Print foo.

(* prints:
{{λ x : (T -> T) -> T -> T, (λ y : S, x x (x x)) x}}
 *)

Definition ctx := string -> option typ.

Fixpoint eqb_typ (T S : typ) : bool :=
  match T, S with
  | TyBase a, TyBase b => String.eqb a b
  | TyBool, TyBool => true
  | TyFun t1 t2, TyFun s1 s2 => eqb_typ t1 s1 && eqb_typ t2 s2
  | _, _ => false
  end.

(*

Inductive term : Type :=
| TVar (var: string) : term
| TLam (var: string) (typ: typ) (body: term) : term
| TApp (operator: term) (operand: term) : term
| TIf (cond: term) (then_: term) (else_: term) : term

 *)

Notation "x <- a ;; b" :=
  match a with
  | Some(x) => b
  | _ => None
  end
    (at level 60, right associativity)
.

Definition add_ctx (Γ: ctx) (x: string) (t: typ) : ctx :=
  (fun x' => if String.eqb x x' then Some t else Γ x').

(* Notation "G , x : T" := (add_ctx G x T) *)
(*                           (at level 40, *)
(*                            G constr, *)
(*                            x constr at level 0, *)
(*                            T custom typ) *)


Fixpoint type_of (Γ: ctx) (t: term) : option typ :=
  match t with
  | TVar x => Γ x
  | TLam x A body =>
    S <- type_of (add_ctx Γ x A) body ;;
    Some {: A -> S :}
  | TApp t1 t2 =>
    T1 <- type_of Γ t1 ;;
    T2 <- type_of Γ t2 ;;
    match T1 with
    | {:A -> B:} => if eqb_typ A T2 then Some B else None
    | _ => None
    end
  | TIf cond then_ else_ =>
    Tcond <- type_of Γ cond ;;
    match Tcond with
    | TyBool =>
      Tthen <- type_of Γ then_ ;;
      Telse <- type_of Γ else_ ;;
      if eqb_typ Tthen Telse
      then Some Tthen
      else None
    | _ => None
    end
  | TTru => Some TyBool
  | TFls => Some TyBool
  end
  .

Definition empty_ctx: ctx := fun _ => None.

Compute type_of empty_ctx {{ λ x: T, x }}.
Compute type_of empty_ctx {{ λ x: T -> T, λ y: T, x y }}.
Compute type_of empty_ctx {{ λ x: T, if tru then x else x }}.

Definition typ_constraint := list (typ * typ).

Definition typ_id := nat.

Open Scope char_scope.

Definition natToDigit (n : nat) : ascii :=
  match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
  end.

Open Scope string_scope.

Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := String (natToDigit (Nat.modulo n 10)) acc in
  match time with
    | 0 => acc'
    | S time' =>
      match Nat.div n 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.


Definition writeNat (n : nat) : string :=
  writeNatAux n n "".

Definition gen_typ (id: typ_id) : typ * typ_id :=
  let prefix := "?X" in
  let id_str := writeNat id
  in (TyBase (append prefix id_str), S id).
