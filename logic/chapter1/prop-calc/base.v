Require Export List.
Set Implicit Arguments.

Module Type base_mod.

Delimit Scope My_scope with M.
Open Scope My_scope.

Parameter PropVars : Set.
Hypothesis Varseq_dec : forall x y : PropVars, {x = y} + {x <> y}.

Fixpoint map_fold_right (A B : Type) (f : B -> A) (g : A -> A -> A) a l :=
  match l with
  | nil => a
  | b :: l' => g (f b) (map_fold_right f g a l')
  end.

End base_mod.


