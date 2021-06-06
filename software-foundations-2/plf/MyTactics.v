Module MyTactics.

Ltac invert_return H := inversion H; subst; try rewrite H; auto.

Ltac solve_stepf_step tm stepf valueb :=
  auto; simpl in *; subst;
  match goal with
  | H : Some _ = Some _ |- _ =>
    invert_return H
  | H : None = Some _ |- _ =>
    invert_return H
  | H : Some _ = None |- _ =>
    invert_return H
  | H : (match (stepf ?t) with | Some _ => _ | None => _ end) |- _ =>
    destruct (stepf t)
  | H : (match (valueb ?t) with | _ => _ end) = _ |- _ =>
    destruct (valueb t) eqn:?
  | H : (match (?t:tm) with | _ => _ end) = _ |- _ =>
    destruct t
  end.

Ltac rewrite_stepf stepf :=
  match goal with
  | H: stepf _ = Some _ |- _ => rewrite H
  end.

Ltac auto_inversion step value stepf valueb :=
  try match goal with
  | H: step ?t ?t' |- _ => try solve [inversion H]
  end;
  try match goal with
  | H: value ?t |- _ => try solve [inversion H]
  end;
  try match goal with
  | H: stepf ?t = Some ?t' |- _ => try solve [inversion H]
  end;
  try match goal with
  | H: valueb ?t = _ |- _ => try solve [simpl in H; inversion H]
  end.


Ltac solve_stepf_converse_step
     tm
     step value
     stepf valueb
     complete_valueb sound_valueb no_step_for_values :=
  try easy; simpl in *; subst; repeat rewrite_stepf stepf;
  match goal with
  | |- ?x = ?x => reflexivity
  | H1: value ?v, H2: valueb ?v = false |- _ =>
    apply complete_valueb in H1; rewrite H1 in H2; inversion H2
  | H1: valueb ?t = true, H2: stepf ?t = Some ?t' |- _ =>
    apply sound_valueb in H1; apply no_step_for_values in H1;
    rewrite H1 in H2; inversion H2
  | H1: value ?t, H2: stepf ?t = Some ?t' |- _ =>
    apply no_step_for_values in H1;
    rewrite H1 in H2; inversion H2
  | |- (match (valueb ?v) with | _ => _ end) = _ =>
    destruct (valueb v) eqn:?
  | |- (match stepf ?t with | _ => _ end) = _ =>
    destruct (stepf t) eqn:?; try easy;
    auto_inversion step value stepf valueb
  | |- (match (match stepf ?t with | _ => _ end) with | _ => _ end) = _ =>
    destruct (stepf t) eqn:?; try easy;
    auto_inversion step value stepf valueb
  | |- (match (match stepf ?t with | _ => _ end) with | _ => _ end) = _ =>
    destruct (stepf t) eqn:?; try easy;
    auto_inversion step value stepf valueb
  | |- (match (match valueb ?v with | _ => _ end) with | _ => _ end) = _ =>
    destruct (valueb v) eqn:?; try easy;
    auto_inversion step value stepf valueb
  | |- (match (?t:tm) with | _ => _ end) = _ =>
    destruct t; try easy;
    auto_inversion step value stepf valueb
  end.

End MyTactics.
