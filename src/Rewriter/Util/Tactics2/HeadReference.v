Require Import Ltac2.Ltac2.
Import Ltac2.Constr.Unsafe.
Require Import Rewriter.Util.Tactics2.Head.
Require Export Rewriter.Util.FixCoqMistakes.

(** find the head reference of the given expression_if it exists *)
Ltac2 rec head_reference_opt (expr : constr) : Std.reference option :=
  match kind expr with
  | App f _ => head_reference_opt f
  | Cast c _ _ => head_reference_opt c
  | Var v => Some (Std.VarRef v)
  | Constant c _ => Some (Std.ConstRef c)
  | Ind i _ => Some (Std.IndRef i)
  | Constructor c _ => Some (Std.ConstructRef c)
  | _ => None
  end.

Ltac2 head_reference_hnf_opt expr := let expr' := eval hnf in $expr in head_reference_opt expr'.

Ltac2 Type exn ::= [ Not_headed_by_a_reference ((* term *) constr, (* head kind *) kind) ].
Ltac2 Type exn ::= [ Not_headed_by_a_reference_in_hnf ((* term *) constr, (* hnf *) constr, (* head kind *) kind) ].

Ltac2 head_reference (expr : constr) : Std.reference :=
  match head_reference_opt expr with
  | Some r => r
  | None => Control.throw (Not_headed_by_a_reference expr (kind (head expr)))
  end.

Ltac2 head_reference_hnf (expr : constr) : Std.reference :=
  let expr' := eval hnf in $expr in
  match head_reference_opt expr' with
  | Some r => r
  | None => Control.throw (Not_headed_by_a_reference_in_hnf expr expr' (kind (head expr')))
  end.
