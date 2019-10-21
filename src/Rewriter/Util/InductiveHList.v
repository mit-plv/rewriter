Inductive hlist := nil | cons {T : Type} (v : T) (vs : hlist).

Fixpoint nth_type (n : nat) (l : hlist) (default : Type) {struct l} :=
  match n, l with
  | O, @cons T _ _ => T
  | S m, @cons _ _ l => nth_type m l default
  | _, _ => default
  end.

Fixpoint nth (n : nat) (l : hlist) {T} (default : T) {struct l} : nth_type n l T :=
  match n, l return nth_type n l T with
  | O, @cons _ x _ => x
  | S m, @cons _ _ l => nth m l default
  | _, _ => default
  end.

Module Export Notations.
  Delimit Scope hlist_scope with hlist.
  Bind Scope hlist_scope with hlist.
  Notation "[ ]" := nil (format "[ ]") : hlist_scope.
  Notation "[ x ]" := (cons x nil) : hlist_scope.
  Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : hlist_scope.
End Notations.
