Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Import Ltac2.Constr.Unsafe.

Ltac2 Type exn ::= [ Not_a_cofix (kind) ].
Ltac2 destCoFix (c : constr) :=
  let k := kind c in
  match k with
  | CoFix x y z => (x, y, z)
  | _ => Control.throw (Not_a_cofix k)
  end.
