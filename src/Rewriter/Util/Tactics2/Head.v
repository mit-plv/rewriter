Require Import Ltac2.Ltac2.
Import Ltac2.Constr.Unsafe.
Require Export Rewriter.Util.FixCoqMistakes.

(** find the head of the given expression *)
Ltac2 rec head (expr : constr) : constr :=
  match kind expr with
  | App f _ => f
  | Cast c _ _ => head c
  | _ => expr
  end.

Ltac2 head_hnf expr := let expr' := eval hnf in $expr in head expr'.
