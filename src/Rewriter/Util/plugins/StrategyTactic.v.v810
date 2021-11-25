Declare ML Module "strategy_tactic_plugin".

(*
(* TEST: *)

Definition id0 {A} (x : A) := x.
Definition id1 {A} (x : A) := x.
Definition id2 {A} (x : A) := id1 x.
Definition id3 {A} (x : A) := id1 x.
Definition id4 := id1 O.

(* Works locally *)
Goal exists x : nat, id0 x = id4.
Proof.
  strategy 1000 [id0];
    eexists; lazymatch goal with |- ?x = ?y => unify x y; constr_eq x (id0 O) end.
  Undo.
  strategy -1000 [id0];
    eexists; lazymatch goal with |- ?x = ?y => unify x y; constr_eq x (id0 id4) end.
  reflexivity.
Abort.

(* works globally *)
Goal exists x : nat, id0 x = id4.
Proof.
  strategy -1000 [id0];
    eexists; lazymatch goal with |- ?x = ?y => unify x y; constr_eq x (id0 id4) end.
  reflexivity.
Defined.

Goal exists x : nat, id0 x = id4.
Proof.
  eexists; lazymatch goal with |- ?x = ?y => unify x y; constr_eq x (id0 id4) end.
Abort.
*)
