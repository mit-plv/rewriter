Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Import Ltac2.Constr.Unsafe.

Ltac2 Type exn ::= [ Not_a_sort (kind) ].
Ltac2 destSort (c : constr) :=
  let k := kind c in
  match k with
  | Sort s => s
  | _ => Control.throw (Not_a_sort k)
  end.
