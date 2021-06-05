Module MyTactics.

Ltac invert_return H := inversion H; subst; try rewrite H; auto.
Ltac auto_invert_return := match goal with
 | H : Some _ = Some _ |- _ => invert_return H
 | H : None = Some _ |- _ => invert_return H
 | H : Some _ = None |- _ => invert_return H
 | _ => idtac
  end.

End MyTactics.
