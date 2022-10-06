Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Import Ltac2.Constr.Unsafe.

Ltac2 Type exn ::= [ Not_a_cast (kind) ].
Ltac2 destCast (c : constr) :=
  let k := kind c in
  match k with
  | Cast x y z => (x, y, z)
  | _ => Control.throw (Not_a_cast k)
  end.
