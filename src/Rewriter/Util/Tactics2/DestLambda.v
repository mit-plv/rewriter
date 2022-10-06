Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Import Ltac2.Constr.Unsafe.

Ltac2 Type exn ::= [ Not_a_lambda (kind) ].
Ltac2 destLambda (c : constr) :=
  let k := kind c in
  match k with
  | Lambda x f => (x, f)
  | _ => Control.throw (Not_a_lambda k)
  end.
