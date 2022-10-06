Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Import Ltac2.Constr.Unsafe.

Ltac2 Type exn ::= [ Not_a_fix (kind) ].
Ltac2 destFix (c : constr) :=
  let k := kind c in
  match k with
  | Fix x y z w => (x, y, z, w)
  | _ => Control.throw (Not_a_fix k)
  end.
