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
    destruct (valueb t) eqn:Hvt
  | H : (match (?t:tm) with | _ => _ end) = _ |- _ =>
    destruct t
  end.

End MyTactics.
