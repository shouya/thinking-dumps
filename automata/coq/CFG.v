Module CFG.

Require Import Utf8_core.


Definition inputunit := nat.
Definition input := list inputunit.

Definition natproc := input → Prop.


Definition terminal (c : inputunit) (i : input) : Prop :=
  match i with
    | [] => False
    | [x] => i = x
    | _ => False
  end.


Definition concat (a : natproc) (b : natproc) : natproc ≔
  fun