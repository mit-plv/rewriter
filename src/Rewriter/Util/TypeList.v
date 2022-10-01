Inductive t := nil | cons (T : Type) (vs : t).

Fixpoint nth (n : nat) (l : t) (default : Type) {struct l} :=
  match n, l with
  | O, cons x _ => x
  | S m, cons _ l => nth m l default
  | _, _ => default
  end.

Module Export Notations.
  Declare Scope type_list_scope.
  Delimit Scope type_list_scope with type_list.
  Bind Scope type_list_scope with t.
  Notation "[ ]" := nil (format "[ ]") : type_list_scope.
  Notation "[ x ]" := (cons x nil) : type_list_scope.
  Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : type_list_scope.
End Notations.
